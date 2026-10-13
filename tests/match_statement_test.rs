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
fn match_statements_retain_every_case_proof_obligation() {
    let mut env = fixture();
    let node_count = env.nodes.len();
    let statement =
        Statement::parse_str("match f {\n    Foo.bar(b) { b or not b }\n    Foo.baz { true }\n}")
            .unwrap();
    env.add_statement(&mut Project::new_mock(), &statement)
        .unwrap();
    assert_eq!(env.nodes.len(), node_count + 2);
    for node in &env.nodes[node_count..] {
        let block = node.block.as_ref().expect("case keeps its proof block");
        assert!(block.env.nodes.iter().any(|node| node.has_goal()));
    }
    assert_eq!(
        env.nodes[node_count].claim.value,
        venticorn::acorn_value::AcornValue::Bool(true)
    );
    env.nodes.last().unwrap().claim.value.validate().unwrap();
    assert!(!env.bindings.has_identifier("b"));
}

#[test]
fn errors_in_later_match_bodies_leave_the_parent_unchanged() {
    let mut env = fixture();
    let node_count = env.nodes.len();
    let error = statement_error(
        &mut env,
        "match f { Foo.bar(b) { true } Foo.baz { unknown } }",
    );
    assert!(error.contains("unknown"), "{error}");
    assert_eq!(env.nodes.len(), node_count);
    assert!(!env.bindings.has_identifier("b"));
}

#[test]
fn nullary_match_case_blocks_assume_the_constructor_equality() {
    use tower_lsp::lsp_types::Range;
    use venticorn::acorn_value::AcornValue;
    use venticorn::block::{Block, BlockParams};

    let env = fixture();
    let value = env.bindings.get_constant_value("f").unwrap();
    let constructor = env.bindings.get_constant_value("Foo.baz").unwrap();
    let params =
        BlockParams::MatchCase(value.clone(), constructor.clone(), vec![], Range::default());
    let block = Block::new(
        &mut Project::new_mock(),
        &env,
        vec![],
        vec![],
        params,
        0,
        0,
        None,
    )
    .unwrap();
    assert!(block.goal.is_none());
    assert_eq!(block.env.nodes.len(), 1);
    assert!(block.env.nodes[0].structural);
    assert_eq!(
        block.env.nodes[0].claim.value,
        AcornValue::new_equals(value, constructor)
    );
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

#[test]
fn match_case_blocks_keep_variables_local_and_retain_body_goals() {
    use venticorn::acorn_value::AcornValue;
    use venticorn::block::{Block, BlockParams};
    use venticorn::statement::StatementInfo;

    let env = fixture();
    let node_count = env.nodes.len();
    let statement =
        Statement::parse_str("match f {\n Foo.bar(b) {\n false\n }\n Foo.baz { true }\n}").unwrap();
    let StatementInfo::Match(ms) = statement.statement else {
        panic!("expected match fixture");
    };
    let (pattern, body) = &ms.cases[0];
    let value = env.bindings.get_constant_value("f").unwrap();
    let (constructor, args, _, _) = env
        .bindings
        .evaluate_pattern(&Project::new_mock(), &value.get_type(), pattern)
        .unwrap();
    let params = BlockParams::MatchCase(value.clone(), constructor.clone(), args, pattern.range());
    let block = Block::new(
        &mut Project::new_mock(),
        &env,
        vec![],
        vec![],
        params,
        body.left_brace.line_number,
        body.right_brace.line_number,
        Some(body),
    )
    .unwrap();
    let local = block.env.bindings.get_constant_value("b").unwrap();
    assert_eq!(
        block.env.nodes[0].claim.value,
        AcornValue::new_equals(value, AcornValue::new_apply(constructor, vec![local]))
    );
    assert!(block.env.nodes[0].structural);
    let goal = block.env.nodes.last().unwrap();
    assert!(!goal.structural);
    assert!(goal.has_goal());
    assert_eq!(goal.claim.value, AcornValue::Bool(false));
    assert_eq!(env.nodes.len(), node_count);
    assert!(!env.bindings.has_identifier("b"));
}

#[test]
fn match_statement_case_body_errors_are_reported_without_binding_leaks() {
    let mut env = fixture();
    let error = statement_error(
        &mut env,
        "match f { Foo.bar(b) { unknown } Foo.baz { true } }",
    );
    assert!(error.contains("unknown"), "{error}");
    assert!(!env.bindings.has_identifier("b"));
}
