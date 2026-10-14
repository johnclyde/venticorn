// Modified for Venticorn: constrained structures must preserve proof obligations and scope.
use venticorn::environment::Environment;
use venticorn::project::Project;
use venticorn::statement::{Statement, StatementInfo};

#[test]
fn constraint_syntax_retains_its_expression_and_closing_range() {
    let source =
        "structure Pair {\n first: Bool\n second: Bool\n} constraint {\n first or second\n}";
    let statement = Statement::parse_str(source).unwrap();
    assert_eq!(statement.range().end.line, 5);
    assert_eq!(statement.range().end.character, 1);
    match &statement.statement {
        StatementInfo::Structure(structure) => {
            assert_eq!(
                structure.constraint.as_ref().unwrap().to_string(),
                "first or second"
            );
        }
        _ => panic!("expected structure"),
    }
    assert_eq!(
        Statement::parse_str(&statement.to_string())
            .unwrap()
            .to_string(),
        statement.to_string()
    );
}

#[test]
fn constraint_syntax_is_rejected_until_its_semantics_are_available() {
    let mut env = Environment::new_test();
    let statement =
        Statement::parse_str("structure Pair {\n first: Bool\n} constraint { false }").unwrap();
    let error = env
        .add_statement(&mut Project::new_mock(), &statement)
        .unwrap_err();
    assert_eq!(
        error.message(),
        "constrained structures are not supported yet"
    );
    assert!(!env.bindings.has_type_name("Pair"));
    assert!(!env.bindings.has_identifier("Pair.new"));
    assert!(env.nodes.is_empty());
}
