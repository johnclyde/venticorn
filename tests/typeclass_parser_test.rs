// Modified for Venticorn: typeclass syntax remains distinct from evaluator support.
use tower_lsp::lsp_types::{Position, Range};
use venticorn::builder::BuildStatus;
use venticorn::project::Project;
use venticorn::token::{keyword_map, keywords_with_prefix, Token, TokenType};

#[test]
fn typeclass_is_a_reserved_keyword_with_identifier_boundaries() {
    assert_eq!(keyword_map().get("typeclass"), Some(&TokenType::Typeclass));
    assert_eq!(
        keywords_with_prefix("type").collect::<Vec<_>>(),
        ["type", "typeclass"]
    );
    let tokens = Token::scan("typeclass typeclass_name typeclasses");
    assert_eq!(tokens[0].token_type, TokenType::Typeclass);
    assert_eq!(tokens[0].to_string(), "typeclass");
    assert_eq!(tokens[1].token_type, TokenType::Identifier);
    assert_eq!(tokens[2].token_type, TokenType::Identifier);
}

#[test]
fn unsupported_typeclass_conditions_report_an_error_without_verifying() {
    let mut project = Project::new_mock();
    project.mock(
        "/mock/main.ac",
        "typeclass T: Example {\n law { true }\n}\n",
    );
    let errors = project.errors();
    assert_eq!(errors.len(), 1);
    assert!(errors[0]
        .1
        .message()
        .contains("typeclass conditions are not supported yet"));
    assert_eq!(
        errors[0].1.range(),
        Range::new(Position::new(1, 1), Position::new(1, 4))
    );
    let report = project.sync_build_report();
    assert_eq!(report.status, BuildStatus::Error);
    assert!(report.events.iter().all(|event| event.verified.is_none()));
    assert_eq!(project.cached_build().num_modules(), 0);
}

use venticorn::environment::Environment;
use venticorn::statement::{Statement, StatementInfo};
use venticorn::token::TokenIter;

fn parse_error(source: &str, expected: &str) {
    let error = Statement::parse_str(source)
        .err()
        .expect("expected a parse error");
    assert!(error.message().contains(expected), "{source}: {error}");
}

#[test]
fn constant_members_round_trip_with_source_ranges_and_following_statements() {
    let source = "typeclass F: Foo {\n    bar: (F, F) -> Bool\n    baz: F\n    qux: Bool\n}";
    let statement = Statement::parse_str(source).unwrap();
    assert_eq!(statement.to_string(), source);
    assert_eq!(
        statement.range(),
        Range::new(Position::new(0, 0), Position::new(4, 1))
    );
    let StatementInfo::Typeclass(ref tc) = statement.statement else {
        panic!("expected typeclass")
    };
    assert_eq!(tc.instance_name.text(), "F");
    assert_eq!(tc.typeclass_name.text(), "Foo");
    assert_eq!(tc.constants.len(), 3);
    assert!(tc.conditions.is_empty());
    assert_eq!(
        tc.constants[0].0.range(),
        Range::new(Position::new(1, 4), Position::new(1, 7))
    );
    assert_eq!(tc.constants[0].1.to_string(), "(F, F) -> Bool");
    assert_eq!(
        Statement::parse_str(&statement.to_string())
            .unwrap()
            .to_string(),
        source
    );

    let mut tokens = TokenIter::new(Token::scan(&format!("{source}\ntheorem {{ true }}")));
    let (first, _) = Statement::parse(&mut tokens, false).unwrap();
    assert!(matches!(
        first.unwrap().statement,
        StatementInfo::Typeclass(_)
    ));
    let (second, _) = Statement::parse(&mut tokens, false).unwrap();
    assert!(matches!(
        second.unwrap().statement,
        StatementInfo::Theorem(_)
    ));
}

#[test]
fn malformed_typeclass_headers_and_members_return_diagnostics() {
    for source in [
        "typeclass",
        "typeclass F",
        "typeclass F:",
        "typeclass f: Foo {\n bar: Bool\n}",
        "typeclass F: foo {\n bar: Bool\n}",
        "typeclass F: Foo",
        "typeclass F: Foo {\n bar:\n}",
    ] {
        assert!(Statement::parse_str(source).is_err(), "{source}");
    }
    parse_error(
        "typeclass F: Foo {}",
        "must have some constants or conditions",
    );
    parse_error("typeclass F: Foo { value: F }", "must end with a newline");
    parse_error(
        "typeclass F: Foo {\n value: F\n",
        "unterminated typeclass statement",
    );
    parse_error("typeclass F: Foo {\n value = true\n}", "expected ':'");
    parse_error(
        "typeclass F: Foo {\n theorem { true }\n}",
        "unexpected token",
    );
}

#[test]
fn theorem_members_round_trip_with_nested_claims_and_no_arguments() {
    for source in [
        "typeclass F: Foo {\n some_bar(x: F) { true }\n}",
        "typeclass F: Foo {\n inhabited { exists(x: F) { x = x } }\n}",
        "typeclass F: Foo {\n bar: (F, F) -> Bool\n some_bar(x: F) { exists(y: F) { x.bar(y) } }\n}",
        "typeclass T: MyTypeclass {\n two_nonequal { exists(x: T, y: T) { x != y } }\n always_a_third(x: T, y: T) { exists(z: T) { x != z and y != z } }\n}",
    ] {
        let parsed = Statement::parse_str(source).unwrap();
        let formatted = parsed.to_string();
        assert_eq!(Statement::parse_str(&formatted).unwrap().to_string(), formatted);
        let StatementInfo::Typeclass(tc) = parsed.statement else { panic!("expected typeclass") };
        assert!(!tc.conditions.is_empty());
        assert_eq!(tc.conditions[0].name.start_pos().line, if tc.constants.is_empty() { 1 } else { 2 });
    }
    let source = "typeclass F: Foo {\n first { true }\n second(value: F) { value = value }\n}";
    let parsed = Statement::parse_str(source).unwrap();
    let StatementInfo::Typeclass(tc) = parsed.statement else {
        panic!("expected typeclass")
    };
    assert_eq!(tc.conditions.len(), 2);
    assert!(tc.conditions[0].args.is_empty());
    assert_eq!(tc.conditions[1].args.len(), 1);
    assert_eq!(tc.conditions[0].claim.to_string(), "true");
    assert_eq!(tc.conditions[1].claim.to_string(), "value = value");
}

#[test]
fn rejected_typeclasses_leave_the_environment_unchanged() {
    let mut env = Environment::new_test();
    env.add("let kept: Bool = true");
    let nodes = env.nodes.len();
    let last_line = env.last_line();
    let kept = env
        .bindings
        .get_constant_value("kept")
        .and_then(|potential| potential.resolved())
        .unwrap();
    let statement =
        Statement::parse_str("typeclass T: Example {\n value: T\n identity { value = value }\n}")
            .unwrap();
    let error = env
        .add_statement(&mut Project::new_mock(), &statement)
        .unwrap_err();
    assert!(error
        .message()
        .contains("typeclass conditions are not supported yet"));
    assert_eq!(env.nodes.len(), nodes);
    assert_eq!(env.last_line(), last_line);
    assert_eq!(
        env.bindings
            .get_constant_value("kept")
            .and_then(|potential| potential.resolved())
            .unwrap(),
        kept
    );
    for name in ["T", "Example", "value"] {
        assert!(!env.bindings.has_identifier(name));
    }
}

#[test]
fn truncated_typeclass_input_never_panics() {
    let source = "typeclass F: Foo {\n value: (F, F) -> Bool\n}";
    for end in source.char_indices().map(|(i, _)| i).chain([source.len()]) {
        let mut tokens = TokenIter::new(Token::scan(&source[..end]));
        let _ = Statement::parse(&mut tokens, false);
    }
}

#[test]
fn malformed_theorem_members_and_generic_parameters_return_diagnostics() {
    parse_error(
        "typeclass F: Foo { identity<T>(x: T) { x = x } }",
        "type parameters are not supported",
    );
    for source in [
        "typeclass F: Foo { identity() { true } }",
        "typeclass F: Foo { identity(x) { true } }",
        "typeclass F: Foo { identity(x: F) true }",
        "typeclass F: Foo { identity { } }",
        "typeclass F: Foo { identity { true } by { true } }",
        "typeclass F: Foo { identity(x: F) { exists(y: F) { x = y } }",
    ] {
        assert!(Statement::parse_str(source).is_err(), "{source}");
    }
}

#[test]
fn theorem_braces_preserve_following_typeclass_members_and_statements() {
    let source = "typeclass T: Example {\n nested(x: T) { forall(y: T) { exists(z: T) { x = y or x = z } } }\n value: T\n}\ntheorem { true }";
    let mut tokens = TokenIter::new(Token::scan(source));
    let (first, _) = Statement::parse(&mut tokens, false).unwrap();
    let first = first.unwrap();
    assert_eq!(first.range().end, Position::new(3, 1));
    let StatementInfo::Typeclass(tc) = first.statement else {
        panic!("expected typeclass")
    };
    assert_eq!(tc.conditions.len(), 1);
    assert_eq!(tc.constants.len(), 1);
    let (second, _) = Statement::parse(&mut tokens, false).unwrap();
    assert!(matches!(
        second.unwrap().statement,
        StatementInfo::Theorem(_)
    ));
}

#[test]
fn nested_theorem_truncations_never_panic() {
    let source = "typeclass F: Foo {\n law(x𐐀: F) { forall(y: F) { x𐐀 = y } }\n}";
    for end in source.char_indices().map(|(i, _)| i).chain([source.len()]) {
        let mut tokens = TokenIter::new(Token::scan(&source[..end]));
        let _ = Statement::parse(&mut tokens, false);
    }
}

#[test]
fn instance_keyword_preserves_identifier_boundaries_and_completion_order() {
    use tower_lsp::lsp_types::SemanticTokenType;
    assert_eq!(keyword_map().get("instance"), Some(&TokenType::Instance));
    assert_eq!(
        keywords_with_prefix("in").collect::<Vec<_>>(),
        ["inductive", "instance"]
    );
    let tokens = Token::scan("instance instance_name instances");
    assert_eq!(tokens[0].token_type, TokenType::Instance);
    assert_eq!(tokens[0].to_string(), "instance");
    assert_eq!(tokens[0].lsp_type(), Some(SemanticTokenType::KEYWORD));
    assert_eq!(tokens[1].token_type, TokenType::Identifier);
    assert_eq!(tokens[2].token_type, TokenType::Identifier);
    assert_eq!(TokenType::Instance.generate().text(), "instance");
}

#[test]
fn argument_free_typeclass_conditions_preserve_exact_formatting() {
    let source = indoc::indoc! {"
        typeclass T: MyTypeclass {
            two_nonequal {
                exists(x: T, y: T) { x != y }
            }
            always_a_third(x: T, y: Y) {
                exists(z: T) { x != z and y != z }
            }
        }"};
    let statement = Statement::parse_str(source).unwrap();
    assert_eq!(statement.to_string(), source);
}
