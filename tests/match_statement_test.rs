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
        let block = node.block().expect("case keeps its proof block");
        assert!(block.env.nodes.iter().any(|node| node.has_goal()));
    }
    assert_eq!(
        env.nodes[node_count].proposition().value,
        venticorn::acorn_value::AcornValue::Bool(true)
    );
    env.nodes
        .last()
        .unwrap()
        .proposition()
        .value
        .validate()
        .unwrap();
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
    let value = env
        .bindings
        .get_constant_value("f")
        .and_then(|potential| potential.resolved())
        .unwrap();
    let constructor = env
        .bindings
        .get_constant_value("Foo.baz")
        .and_then(|potential| potential.resolved())
        .unwrap();
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
    assert!(block.env.nodes[0].is_structural());
    assert_eq!(
        block.env.nodes[0].proposition().value,
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
    assert!(error.message().contains("missing"), "{}", error.message());
    assert!(!error.message().contains("not supported yet"));
}

fn statement_error(env: &mut Environment, source: &str) -> String {
    let statement = Statement::parse_str(source).unwrap();
    env.add_statement(&mut Project::new_mock(), &statement)
        .unwrap_err()
        .message()
        .to_string()
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
        env.bindings
            .get_constant_value("Foo.baz")
            .and_then(|potential| potential.resolved())
            .unwrap()
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
    let value = env
        .bindings
        .get_constant_value("f")
        .and_then(|potential| potential.resolved())
        .unwrap();
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
    let local = block
        .env
        .bindings
        .get_constant_value("b")
        .and_then(|potential| potential.resolved())
        .unwrap();
    assert_eq!(
        block.env.nodes[0].proposition().value,
        AcornValue::new_equals(value, AcornValue::new_apply(constructor, vec![local]))
    );
    assert!(block.env.nodes[0].is_structural());
    let goal = block.env.nodes.last().unwrap();
    assert!(!goal.is_structural());
    assert!(goal.has_goal());
    assert_eq!(goal.proposition().value, AcornValue::Bool(false));
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

#[test]
fn quantified_match_statements_require_every_constructor() {
    let mut env = fixture();
    let node_count = env.nodes.len();
    let error = statement_error(
        &mut env,
        "forall(value: Foo) { match value { Foo.bar(bit) { bit } } }",
    );
    assert!(error.contains("not all cases are covered"), "{error}");
    assert_eq!(env.nodes.len(), node_count);
    assert!(!env.bindings.has_identifier("value"));
    assert!(!env.bindings.has_identifier("bit"));
}

#[test]
fn ordinary_methods_cannot_be_quantified_match_patterns() {
    let mut env = fixture();
    env.add("class Foo { define qux(self, bit: Bool) -> Foo { Foo.baz } }");
    let node_count = env.nodes.len();
    let error = statement_error(
        &mut env,
        "forall(value: Foo) { match value { Foo.bar(bit) { bit } Foo.qux { false } } }",
    );
    assert!(error.contains("expected a constructor"), "{error}");
    assert_eq!(env.nodes.len(), node_count);
    assert!(!env.bindings.has_identifier("value"));
    assert!(!env.bindings.has_identifier("bit"));
}

#[test]
fn quantified_match_patterns_reject_repeated_variable_names() {
    let mut env = Environment::new_test();
    env.add("inductive Pair {\n both(Bool, Bool)\n }\n");
    let node_count = env.nodes.len();
    let error = statement_error(
        &mut env,
        "forall(value: Pair) { match value { Pair.both(bit, bit) { bit } } }",
    );
    assert!(
        error.contains("cannot use a name twice in one pattern"),
        "{error}"
    );
    assert_eq!(env.nodes.len(), node_count);
    assert!(!env.bindings.has_identifier("bit"));
}

#[test]
fn quantified_match_patterns_reject_cases_after_complete_coverage() {
    let mut env = fixture();
    let node_count = env.nodes.len();
    let error = statement_error(&mut env,
        "forall(value: Foo) { match value { Foo.bar(first) { first } Foo.baz { false } Foo.bar(last) { last } } }",
    );
    assert!(error.contains("duplicate pattern"), "{error}");
    assert_eq!(env.nodes.len(), node_count);
    for name in ["value", "first", "last"] {
        assert!(!env.bindings.has_identifier(name));
    }
}

#[test]
fn each_match_case_selects_its_own_claim_and_keeps_following_statements() {
    use venticorn::block::NodeCursor;
    let mut env = Environment::new_test();
    let source = "inductive Choice {\n first\n second\n}\nlet value: Choice = axiom\nmatch value {\n Choice.first {\n  value = Choice.first\n }\n Choice.second {\n  value = Choice.second\n }\n}\ntheorem after { true }\n";
    env.add(source);
    let first_path = env.path_for_line(7).unwrap();
    let second_path = env.path_for_line(10).unwrap();
    assert_ne!(first_path[0], second_path[0]);
    for path in [&first_path, &second_path] {
        assert_eq!(path.len(), 2);
        assert!(NodeCursor::from_path(&env, path).current().has_goal());
    }
    let after = env.path_for_line(13).unwrap();
    assert_eq!(after.len(), 1);
    assert!(after[0] > second_path[0]);
    assert!(env.path_for_line(12).is_err());
}

#[test]
fn match_body_ranges_preserve_multiline_constructor_patterns() {
    use venticorn::statement::StatementInfo;
    let source = "match value {\n Foo.bar(\n  bit\n ) {\n  bit\n }\n Foo.baz {\n  true\n }\n}";
    let statement = Statement::parse_str(source).unwrap();
    let StatementInfo::Match(ms) = statement.statement else {
        panic!("expected match statement");
    };
    assert_eq!(ms.cases[0].1.range().start.line, 3);
    assert_eq!(ms.cases[0].1.range().end.line, 5);
    assert_eq!(ms.cases[1].1.range().start.line, 6);
    assert_eq!(ms.cases[1].1.range().end.line, 8);
}
