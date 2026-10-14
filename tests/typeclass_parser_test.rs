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
fn unsupported_typeclass_declarations_report_an_error_without_verifying() {
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", "typeclass T: Example {\n value: T\n}\n");
    let errors = project.errors();
    assert_eq!(errors.len(), 1);
    assert!(errors[0]
        .1
        .message()
        .contains("typeclass declarations are not supported yet"));
    assert_eq!(
        errors[0].1.range(),
        Range::new(Position::new(0, 0), Position::new(0, 9))
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
    assert_eq!(tc.instance_type.text(), "F");
    assert_eq!(tc.name.text(), "Foo");
    assert_eq!(tc.constants.len(), 3);
    assert!(tc.theorems.is_empty());
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
        "must have some constants or theorems",
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
fn theorem_members_are_explicitly_rejected_until_supported() {
    for source in [
        "typeclass F: Foo {\n some_bar(x: F) { true }\n}",
        "typeclass F: Foo {\n inhabited { exists(x: F) { x = x } }\n}",
    ] {
        parse_error(source, "typeclass theorem members are not supported yet");
    }
}

#[test]
fn rejected_typeclasses_leave_the_environment_unchanged() {
    let mut env = Environment::new_test();
    env.add("let kept: Bool = true");
    let nodes = env.nodes.len();
    let last_line = env.last_line();
    let kept = env.bindings.get_constant_value("kept").unwrap();
    let statement = Statement::parse_str("typeclass T: Example {\n value: T\n}").unwrap();
    let error = env
        .add_statement(&mut Project::new_mock(), &statement)
        .unwrap_err();
    assert!(error
        .message()
        .contains("typeclass declarations are not supported yet"));
    assert_eq!(env.nodes.len(), nodes);
    assert_eq!(env.last_line(), last_line);
    assert_eq!(env.bindings.get_constant_value("kept").unwrap(), kept);
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
