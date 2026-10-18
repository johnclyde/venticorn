// Modified for Venticorn: preserve declaration order and source boundaries for generic arguments.
use venticorn::environment::Environment;
use venticorn::project::Project;
use venticorn::prover::{Outcome, Prover};
use venticorn::statement::Statement;

fn prove(source: &str) -> Outcome {
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", source);
    let id = project.expect_ok("main");
    let env = project.get_env_by_id(id).unwrap();
    let node = env.get_node_by_name("goal");
    let context = node.goal_context().unwrap();
    context.goal.value().validate().unwrap();
    let mut prover = Prover::new(&project, false);
    for fact in node.usable_facts(&project) {
        fact.value.validate().unwrap();
        prover.add_fact(fact);
    }
    prover.set_goal(&context);
    let outcome = prover.quick_verification_search();
    assert!(
        !matches!(outcome, Outcome::Error(_)),
        "{:?}\n{source}",
        prover.error()
    );
    outcome
}

#[test]
fn multiple_function_parameters_round_trip_and_keep_their_order() {
    let declaration = "define first<T, U>(left: T, right: U) -> T { left }";
    let parsed = Statement::parse_str(declaration).unwrap();
    let formatted = parsed.to_string();
    assert_eq!(
        Statement::parse_str(&formatted).unwrap().to_string(),
        formatted
    );
    let declarations = r#"
        inductive Item {
            one
            two
        }
        define first<T, U>(left: T, right: U) -> T { left }
        define swapped<T, U>(left: T, right: U) -> U { first(right, left) }
    "#;
    for goal in [
        "first(Item.one, true) = Item.one",
        "first(true, Item.one) = true",
        "swapped(true, Item.one) = Item.one",
        "first(Item.one, Item.two) = Item.one",
    ] {
        assert_eq!(
            prove(&format!("{declarations}\ntheorem goal {{ {goal} }}")),
            Outcome::Success
        );
    }
    assert_eq!(
        prove(&format!(
            "{declarations}\ntheorem goal {{ swapped(true, Item.one) = Item.two }}"
        )),
        Outcome::Exhausted
    );
}

#[test]
fn multiple_parameters_keep_invalid_declarations_and_arguments_rejected() {
    for source in [
        "define first<>(left: Bool) -> Bool { left }",
        "define first<T,>(left: T) -> T { left }",
        "define first<T U>(left: T) -> T { left }",
    ] {
        assert!(Statement::parse_str(source).is_err(), "{source}");
    }
    let mut env = Environment::new_test();
    env.bad("define duplicate<T, T>(left: T) -> T { left }");
    assert!(!env.bindings.has_identifier("duplicate"));
    assert!(!env.bindings.has_type_name("T"));
    env.add("define first<T, U>(left: T, right: U) -> T { left }");
    env.bad("let bad: Bool = first(true)");
    env.bad("let bad: Bool = first(true, true, true)");
    env.add("theorem same<T, U>(left: T, right: U) { left = left }");
    assert!(!env.bindings.has_type_name("T"));
    assert!(!env.bindings.has_type_name("U"));
    env.bad("theorem duplicate_theorem<T, T>(value: T) { value = value }");
    assert!(!env.bindings.has_identifier("duplicate_theorem"));
    assert!(!env.bindings.has_type_name("T"));
}

#[test]
fn type_parameter_lists_are_separate_from_value_argument_lists() {
    for source in [
        "define witness<T> -> T { axiom }",
        "define lower<t>(value: t) -> t { value }",
        "theorem identity<T> { true }",
        "axiom<T> { true }",
        "typeclass T: Reflect {\n reflexive { true }\n}",
    ] {
        let formatted = Statement::parse_str(source).unwrap().to_string();
        assert_eq!(
            Statement::parse_str(&formatted).unwrap().to_string(),
            formatted
        );
    }
    for source in [
        "forall<T>(flag: Bool) { true }",
        "typeclass T: Reflect {\n reflexive<U>(value: U) { value = value }\n}",
        "define bad<T, U(value: T) -> T { value }",
        "theorem bad<T,>(value: T) { value = value }",
    ] {
        assert!(Statement::parse_str(source).is_err(), "{source}");
    }
}
