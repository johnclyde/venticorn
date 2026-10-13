// Modified for Venticorn.

use venticorn::environment::Environment;
use venticorn::project::Project;
use venticorn::statement::Statement;

fn fixture() -> Environment {
    let mut env = Environment::new_test();
    env.add("inductive Foo {\n    bar(Bool)\n    baz\n}");
    env.add("let f: Foo = axiom");
    env
}

#[test]
fn match_statements_report_unsupported_semantics_without_adding_nodes() {
    let mut env = fixture();
    let node_count = env.nodes.len();
    let statement =
        Statement::parse_str("match f {\n    Foo.bar(b) { b or not b }\n    Foo.baz { true }\n}")
            .unwrap();
    let error = env
        .add_statement(&mut Project::new_mock(), &statement)
        .unwrap_err();
    assert!(error
        .message
        .contains("match statements are not supported yet"));
    assert_eq!(env.nodes.len(), node_count);
    assert!(!env.bindings.has_identifier("b"));
}

#[test]
fn match_case_block_construction_reports_unsupported_semantics() {
    use tower_lsp::lsp_types::Range;
    use venticorn::block::{Block, BlockParams};

    let env = fixture();
    let params = BlockParams::MatchCase(
        env.bindings.get_constant_value("f").unwrap(),
        env.bindings.get_constant_value("Foo.baz").unwrap(),
        Range::default(),
    );
    let result = Block::new(
        &mut Project::new_mock(),
        &env,
        vec![],
        vec![],
        params,
        0,
        0,
        None,
    );
    let error = match result {
        Err(error) => error,
        Ok(_) => panic!("expected an explicit unsupported error"),
    };
    assert!(error
        .message
        .contains("match case blocks are not supported yet"));
}

#[test]
fn match_statement_checks_its_scrutinee() {
    let mut env = fixture();
    let statement = Statement::parse_str("match missing { Foo.baz { true } }").unwrap();
    let error = env
        .add_statement(&mut Project::new_mock(), &statement)
        .unwrap_err();
    assert!(error.message.contains("missing"), "{}", error.message);
    assert!(!error.message.contains("not supported yet"));
}
