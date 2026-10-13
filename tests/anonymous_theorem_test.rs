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
