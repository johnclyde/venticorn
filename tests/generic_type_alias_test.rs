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
        if text.starts_with("forall") {
            assert_eq!(code, text);
        }
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

#[test]
fn qualified_nested_data_and_function_actuals_round_trip() {
    let mut project = Project::new_mock();
    project.mock("/mock/pair.ac", PAIR);
    project.mock("/mock/main.ac", "import pair");
    let id = project.expect_ok("main");
    let env = project.get_env_by_id(id).unwrap();
    for text in [
        "forall(x0: pair.Pair<Bool, Bool>) { true }",
        "function(x0: pair.Pair<pair.Pair<Bool, Bool>, (Bool -> Bool) -> Bool>) { x0 }",
        "function(x0: (pair.Pair<Bool, Bool>, Bool) -> pair.Pair<Bool, Bool -> Bool>) { x0 }",
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
fn generated_types_prefer_exact_then_family_aliases_without_losing_actuals() {
    let mut project = Project::new_mock();
    project.mock("/mock/pair.ac", PAIR);
    project.mock("/mock/main.ac", "import pair\ntype Family: pair.Pair\ntype Left: Family<Bool, Bool -> Bool>\ntype Right: Family<Bool -> Bool, Bool>");
    let id = project.expect_ok("main");
    let env = project.get_env_by_id(id).unwrap();
    for (input, expected) in [
        (
            "function(x0: pair.Pair<Bool, Bool>) { x0 }",
            "function(x0: Family<Bool, Bool>) { x0 }",
        ),
        (
            "function(x0: pair.Pair<Bool, Bool -> Bool>) { x0 }",
            "function(x0: Left) { x0 }",
        ),
        (
            "function(x0: pair.Pair<Bool -> Bool, Bool>) { x0 }",
            "function(x0: Right) { x0 }",
        ),
        (
            "function(x0: pair.Pair<pair.Pair<Bool, Bool>, Bool>) { x0 }",
            "function(x0: Family<Family<Bool, Bool>, Bool>) { x0 }",
        ),
    ] {
        let value = env
            .bindings
            .evaluate_value(&project, &Expression::expect_value(input), None)
            .unwrap();
        let code = env.bindings.value_to_code(&value).unwrap();
        assert_eq!(code, expected);
        let replay = env
            .bindings
            .evaluate_value(&project, &Expression::expect_value(&code), None)
            .unwrap();
        assert_eq!(value, replay);
    }
}

#[test]
fn family_aliases_with_equal_canonical_names_keep_distinct_modules() {
    let mut project = Project::new_mock();
    project.mock("/mock/left.ac", PAIR);
    project.mock("/mock/right.ac", PAIR);
    project.mock("/mock/main.ac", "import left\nimport right\ntype Left: left.Pair\ntype Right: right.Pair\ntype Pair: Left\nlet x0: Bool = true\nlet k0: Bool = true\nlet left_pair: Left<Bool, Bool> = Pair.new(true, false)\nlet right_pair: Right<Bool, Bool> = Right.new(true, false)");
    let id = project.expect_ok("main");
    let env = project.get_env_by_id(id).unwrap();
    let mut types = vec![];
    for text in [
        "Left<Bool, Bool>.new(true, false)",
        "Right<Bool, Bool>.new(true, false)",
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
        types.push(value.get_type());
    }
    assert_ne!(types[0], types[1]);
    for text in [
        "left_pair = right_pair",
        "Left.first(right_pair)",
        "Right.first(left_pair)",
    ] {
        assert!(
            env.bindings
                .evaluate_value(&project, &Expression::expect_value(text), None)
                .is_err(),
            "{text}"
        );
    }
    for text in [
        "function(value: Left<Bool, Bool>) { value }",
        "function(value: Right<Bool, Bool>) { value }",
    ] {
        let value = env
            .bindings
            .evaluate_value(&project, &Expression::expect_value(text), None)
            .unwrap();
        let code = env.bindings.value_to_code(&value).unwrap();
        assert!(
            code.contains("x1:"),
            "generated binder must avoid x0: {code}"
        );
        let replay = env
            .bindings
            .evaluate_value(&project, &Expression::expect_value(&code), None)
            .unwrap();
        assert_eq!(value, replay);
    }
}

fn imported_generic_project(imports: &str, body: &str) -> Project {
    let mut project = Project::new_mock();
    project.mock("/mock/marker.ac", "structure Marker<T> {\n value: Bool\n}\nclass Marker<T> {\n define chosen(self) -> Marker<T> { axiom }\n}");
    project.mock("/mock/main.ac", &format!("{imports}\n{body}"));
    project
}

fn verify_imported_generic(imports: &str, source: &str) -> venticorn::prover::Outcome {
    use venticorn::prover::{Outcome, Prover};
    let mut project = imported_generic_project(imports, source);
    let id = project.expect_ok("main");
    for node in project.get_env_by_id(id).unwrap().iter_goals() {
        let mut prover = Prover::new(&project, false);
        for fact in node.usable_facts(&project) {
            prover.add_fact(fact);
        }
        prover.set_goal(&node.goal_context().unwrap());
        let outcome = prover.quick_verification_search();
        assert!(
            !matches!(outcome, Outcome::Error(_)),
            "{:?}",
            prover.error()
        );
        if outcome != Outcome::Success {
            return outcome;
        }
    }
    Outcome::Success
}

#[test]
fn generated_imported_generic_witnesses_replay_through_family_aliases() {
    use venticorn::prover::{Outcome, Prover};
    for (imports, family) in [
        ("from marker import Marker", "Marker"),
        ("import marker\ntype Family: marker.Marker", "Family"),
    ] {
        for actual in ["Bool", "(Bool -> Bool) -> Bool"] {
            let source = format!(
                "let k0: Bool = true\n\
                 let seed: {family}<{actual}> = axiom\n\
                 let mul: ({family}<{actual}>, {family}<{actual}>) -> {family}<{actual}> = axiom\n\
                 define marked(n: {family}<{actual}>) -> Bool {{ exists(d: {family}<{actual}>) {{ mul(seed, d) = n }} }}\n\
                 axiom marker_right(a: {family}<{actual}>, b: {family}<{actual}>) {{ b = seed.chosen -> mul(a, b) = seed.chosen }}\n\
                 theorem goal {{ marked(seed.chosen) }}"
            );
            let mut project = imported_generic_project(imports, &source);
            let id = project.expect_ok("main");
            let env = project.get_env_by_id(id).unwrap();
            let node = env.get_node_by_name("goal");
            let mut prover = Prover::new(&project, false);
            for fact in node.usable_facts(&project) {
                prover.add_fact(fact);
            }
            prover.set_goal(&node.goal_context().unwrap());
            assert_eq!(prover.quick_search(), Outcome::Success);
            let code = prover
                .get_and_print_proof()
                .unwrap()
                .to_code(&env.bindings)
                .unwrap();
            assert!(!code.is_empty());
            let code = code.join("\n");
            assert!(code.contains("chosen"), "{code}");
            assert!(code.contains(family), "{code}");
            assert!(
                !code.contains("let k0:"),
                "witness name must avoid k0: {code}"
            );
            assert_eq!(
                verify_imported_generic(imports, &format!("{source} by {{\n{code}\n}}")),
                Outcome::Success
            );
            assert_eq!(
                verify_imported_generic(
                    imports,
                    &format!("{source} by {{ exists(p: {family}<{actual}>) {{ p != p }} }}")
                ),
                Outcome::Exhausted
            );
        }
    }
}
