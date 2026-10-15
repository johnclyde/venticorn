use venticorn::environment::Environment;
use venticorn::expression::Expression;
use venticorn::project::Project;

const PAIR: &str = "structure Pair<T, U> {\n first: T\n second: U\n}\n";

#[test]
fn generic_family_aliases_keep_arity_and_specialization_identity() {
    let mut env = Environment::new_test();
    env.add(PAIR);
    env.add("type Family: Pair\ntype Other: Family\ntype Left: Pair<Bool, Bool -> Bool>\ntype Right: Pair<Bool -> Bool, Bool>");
    env.add("define identity(value: Bool) -> Bool { value }");
    env.add("let p: Family<Bool, Bool -> Bool> = Other.new(true, identity)");
    env.add("let q: Left = Other<Bool, Bool -> Bool>.new(true, identity)");
    for text in [
        "let bad: Family = axiom",
        "let bad: Family<Bool> = axiom",
        "let bad: Family<Bool, Bool, Bool> = axiom",
        "let bad: Right = p",
        "type Bad: Left<Bool>",
    ] {
        env.bad(text);
    }
    let project = Project::new_mock();
    for text in [
        "function(x: Left) { x }",
        "function(x: Right) { x }",
        "Family.new<Bool, Bool -> Bool>",
    ] {
        let value = env
            .bindings
            .evaluate_value(&project, &Expression::expect_value(text), None)
            .unwrap();
        let code = env.bindings.value_to_code(&value).unwrap();
        let replay = env
            .bindings
            .evaluate_value(&project, &Expression::expect_value(&code), None)
            .unwrap();
        assert_eq!(value, replay, "{text} rendered as {code}");
    }
}

#[test]
fn direct_generic_type_imports_keep_the_defining_module() {
    let mut project = Project::new_mock();
    project.mock("/mock/pair.ac", PAIR);
    project.mock("/mock/main.ac", "from pair import Pair\ntype Family: Pair\ndefine identity(value: Bool) -> Bool { value }\nlet p: Family<Bool, Bool -> Bool> = Family.new(true, identity)");
    let id = project.expect_ok("main");
    let env = project.get_env_by_id(id).unwrap();
    for text in [
        "forall(x0: Pair<Bool, Bool>) { true }",
        "Family<Bool, Bool -> Bool>.new(true, identity)",
        "Family.first(p)",
    ] {
        let value = env
            .bindings
            .evaluate_value(&project, &Expression::expect_value(text), None)
            .unwrap();
        let code = env.bindings.value_to_code(&value).unwrap();
        let replay = env
            .bindings
            .evaluate_value(&project, &Expression::expect_value(&code), None)
            .unwrap();
        assert_eq!(value, replay, "{text} rendered as {code}");
    }
}

#[test]
fn import_completion_lists_canonical_generic_families_and_excludes_aliases() {
    let mut env = Environment::new_test();
    env.add(PAIR);
    env.add("type Family: Pair\ntype Concrete: Pair<Bool, Bool>");
    let project = Project::new_mock();
    let labels = env
        .bindings
        .get_completions(&project, "", true)
        .unwrap()
        .into_iter()
        .map(|item| item.label)
        .collect::<Vec<_>>();
    assert!(labels.contains(&"Pair".to_string()));
    assert!(!labels.contains(&"Family".to_string()));
    assert!(!labels.contains(&"Concrete".to_string()));
}
