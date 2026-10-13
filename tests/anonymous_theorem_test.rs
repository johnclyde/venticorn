// Modified for Venticorn: anonymous declarations must retain proof obligations and source identity.
use venticorn::environment::Environment;
use venticorn::project::Project;
use venticorn::statement::Statement;

#[test]
fn anonymous_declarations_are_guarded_without_mutating_the_environment() {
    let mut env = Environment::new_test();
    for source in [
        "theorem { true }",
        "theorem(a: Bool, b: Bool) { a = b or a or b }",
        "theorem<T>(value: T) { value = value }",
    ] {
        let statement = Statement::parse_str(source).unwrap();
        let error = env
            .add_statement(&mut Project::new_mock(), &statement)
            .unwrap_err();
        assert_eq!(
            error.message,
            "anonymous theorem and axiom declarations are not supported yet"
        );
        assert_eq!(error.token.line_number, 0);
        assert!(env.nodes.is_empty());
        assert!(!env.bindings.has_identifier("a"));
        assert!(!env.bindings.has_type_name("T"));
    }
    env.add("theorem named { true }");
    assert!(env.bindings.has_identifier("named"));
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
