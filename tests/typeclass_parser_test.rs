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
