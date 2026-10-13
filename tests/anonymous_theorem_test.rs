// Modified for Venticorn: anonymous declarations must retain proof obligations and source identity.
use venticorn::environment::Environment;
use venticorn::project::Project;
use venticorn::statement::Statement;

#[test]
fn anonymous_theorems_create_goals_without_leaking_parameter_bindings() {
    let mut env = Environment::new_test();
    for (i, source) in [
        "theorem { true }",
        "theorem(a: Bool, b: Bool) { a = b or a or b }",
        "theorem<T>(value: T) { value = value }",
    ]
    .iter()
    .enumerate()
    {
        let statement = Statement::parse_str(source).unwrap();
        env.add_statement(&mut Project::new_mock(), &statement)
            .unwrap();
        assert_eq!(env.nodes.len(), i + 1);
        assert_eq!(env.iter_goals().count(), i + 1);
        let node = env.nodes.last().unwrap();
        assert!(!node.structural);
        assert!(node.claim.name().is_none());
        assert_eq!(node.claim.source.description(), "an anonymous theorem");
        assert!(!env.bindings.has_identifier("a"));
        assert!(!env.bindings.has_identifier("b"));
        assert!(!env.bindings.has_type_name("T"));
    }
}

#[test]
fn theorem_goal_ranges_end_at_the_claim_not_the_proof_body() {
    let mut env = Environment::new_test();
    env.add("theorem named(b: Bool) {\n    b or not b\n} by {\n    true\n}\n");
    let node = env.nodes.last().unwrap();
    let range = node.claim.source.range;
    assert_eq!(range.start.line, 0);
    assert_eq!(range.start.character, 0);
    assert_eq!(range.end.line, 2);
    assert_eq!(range.end.character, 1);
    let context = env.iter_goals().last().unwrap().goal_context().unwrap();
    match context.goal {
        venticorn::goal::Goal::Prove(proposition) => assert_eq!(proposition.source.range, range),
        _ => panic!("expected theorem proof goal"),
    }
}

#[test]
fn malformed_theorem_bodies_leave_no_names_ranges_or_facts() {
    for source in [
        "theorem broken { true } by { missing }",
        "theorem { true } by { missing }",
        "theorem broken<T>(value: T) { value = value } by { missing }",
        "theorem<T>(value: T) { value = value } by { missing }",
    ] {
        let mut env = Environment::new_test();
        let statement = Statement::parse_str(source).unwrap();
        let error = env
            .add_statement(&mut Project::new_mock(), &statement)
            .unwrap_err();
        assert!(error.message.contains("missing"), "{error}");
        assert!(env.nodes.is_empty());
        assert!(!env.bindings.has_identifier("broken"));
        assert!(!env.bindings.has_identifier("value"));
        assert!(!env.bindings.has_type_name("T"));
        env.add("theorem broken { true }");
        assert_eq!(env.nodes.len(), 1);
    }
}

#[test]
fn theorem_parameter_collisions_are_errors_instead_of_panics() {
    for source in [
        "theorem f(f: Bool) { f or not f }",
        "theorem f<f>(value: f) { value = value }",
    ] {
        let mut env = Environment::new_test();
        let statement = Statement::parse_str(source).unwrap();
        let error = env
            .add_statement(&mut Project::new_mock(), &statement)
            .unwrap_err();
        assert_eq!(error.message, "theorem name conflicts with a parameter");
        assert!(env.nodes.is_empty());
        assert!(!env.bindings.has_identifier("f"));
        assert!(!env.bindings.has_type_name("f"));
        env.add("theorem f { true }");
    }
}

#[test]
fn anonymous_goal_names_have_a_source_location_fallback() {
    let mut env = Environment::new_test();
    env.add("inductive Choice {\n first\n second\n}\ntheorem { match Choice.first { Choice.first { true } Choice.second { false } } }");
    let context = env.iter_goals().last().unwrap().goal_context().unwrap();
    assert_eq!(context.name, "claim at line 5");
}
