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
    assert!(error.message.contains("not supported yet"));
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

fn statement_error(env: &mut Environment, source: &str) -> String {
    let statement = Statement::parse_str(source).unwrap();
    env.add_statement(&mut Project::new_mock(), &statement)
        .unwrap_err()
        .message
}

#[test]
fn match_statement_requires_every_constructor() {
    let mut env = fixture();
    let error = statement_error(&mut env, "match f { Foo.baz { true } }");
    assert!(error.contains("not all cases are covered"), "{error}");
}

#[test]
fn match_statement_rejects_duplicate_cases_even_after_complete_coverage() {
    let mut env = fixture();
    let error = statement_error(
        &mut env,
        "match f { Foo.bar(first) { true } Foo.baz { true } Foo.bar(last) { false } }",
    );
    assert!(error.contains("duplicate pattern"), "{error}");
    assert!(!env.bindings.has_identifier("first"));
    assert!(!env.bindings.has_identifier("last"));
}

#[test]
fn match_statement_patterns_must_be_constructors() {
    let mut env = fixture();
    let error = statement_error(&mut env, "match f { f { true } }");
    assert!(error.contains("expected a constructor"), "{error}");
}

#[test]
fn match_statement_patterns_reject_invalid_or_existing_names() {
    let mut env = fixture();
    for source in [
        "match f { Foo.bar(true) { true } Foo.baz { true } }",
        "match f { Foo.bar(f) { true } Foo.baz { true } }",
        "match f { Foo.bar { true } Foo.baz { true } }",
    ] {
        let error = statement_error(&mut env, source);
        assert!(!error.contains("not supported yet"), "{source}: {error}");
    }
}

#[test]
fn pattern_evaluation_returns_the_nullary_constructor() {
    use venticorn::expression::Expression;
    let env = fixture();
    let pattern = Expression::expect_value("Foo.baz");
    let foo = env.bindings.get_type_for_name("Foo").unwrap();
    let (constructor, args, index, total) = env
        .bindings
        .evaluate_pattern(&Project::new_mock(), foo, &pattern)
        .unwrap();
    assert_eq!(
        constructor,
        env.bindings.get_constant_value("Foo.baz").unwrap()
    );
    assert!(args.is_empty());
    assert_eq!((index, total), (1, 2));
}
