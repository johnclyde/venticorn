// Modified for Venticorn: compiler ranges use the editor protocol's UTF-16 units.
use tower_lsp::lsp_types::{Position, Range};
use venticorn::compilation::Error;
use venticorn::project::Project;
use venticorn::token::Token;

fn assert_error_span(code: &str, text: &str) {
    assert_diagnostic(code, text, "unknown identifier");
}

fn assert_diagnostic(code: &str, text: &str, message: &str) {
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", code);
    let errors = project.errors();
    assert_eq!(errors.len(), 1);
    let error = errors[0].1;
    assert!(error.message().contains(message), "{error}");
    let start = code.find(text).unwrap();
    let position = |end: usize| {
        let prefix = &code[..end];
        Position::new(
            prefix.bytes().filter(|byte| *byte == b'\n').count() as u32,
            prefix.rsplit('\n').next().unwrap().encode_utf16().count() as u32,
        )
    };
    assert_eq!(
        error.range(),
        Range::new(position(start), position(start + text.len()))
    );
}

#[test]
fn diagnostic_columns_count_utf16_before_and_within_the_span() {
    assert_error_span("let x𐐀é: Bool = missing", "missing");
    assert_error_span("let x: Bool = y𐐀é", "y𐐀é");
}

#[test]
fn token_storage_stays_in_bytes_while_positions_use_utf16() {
    let tokens = Token::scan("x𐐀é other");
    assert_eq!(tokens[0].text(), "x𐐀é");
    assert_eq!(tokens[0].len, 7);
    assert_eq!(tokens[0].end_pos(), Position::new(0, 4));
    assert_eq!(tokens[1].text(), "other");
    assert_eq!(tokens[1].start, 8);
    assert_eq!(
        tokens[1].range(),
        Range::new(Position::new(0, 5), Position::new(0, 10))
    );
}

#[test]
fn empty_and_end_of_line_errors_keep_a_visible_caret() {
    let empty = Token::empty();
    let error = Error::new(&empty, &empty, "missing expression");
    assert_eq!(
        error.range(),
        Range::new(Position::new(0, 0), Position::new(0, 0))
    );
    assert!(error.to_string().ends_with("\n^\n"));
    let tokens = Token::scan("x𐐀é");
    let last = tokens.last().unwrap();
    let error = Error::new(last, last, "missing expression");
    assert_eq!(
        error.range(),
        Range::new(Position::new(0, 4), Position::new(0, 4))
    );
    assert!(error.to_string().ends_with("   ^\n"));
}

#[test]
fn secondary_import_errors_cover_the_import_without_duplicate_root_diagnostics() {
    use venticorn::builder::BuildStatus;
    use venticorn::module::ModuleRef;
    let mut project = Project::new_mock();
    project.mock("/mock/broken.ac", "theorem broken { missing }");
    project.mock("/mock/main.ac", "import broken");
    let errors = project.errors();
    assert_eq!(errors.len(), 2);
    let secondary = errors.iter().find(|(_, error)| error.secondary).unwrap().1;
    assert_eq!(
        secondary.range(),
        Range::new(Position::new(0, 0), Position::new(0, 13))
    );
    let (status, events) = project.sync_build();
    assert_eq!(status, BuildStatus::Error);
    let located: Vec<_> = events
        .iter()
        .filter(|event| event.diagnostic.is_some())
        .collect();
    assert_eq!(located.len(), 1);
    assert_eq!(located[0].module, ModuleRef::Name("broken".to_string()));
    assert!(events.iter().all(|event| event.verified.is_none()));
}

#[test]
fn error_ranges_preserve_endpoints_across_lines() {
    let tokens = Token::scan("start\n  end𐐀");
    let last = tokens.iter().find(|token| token.text() == "end𐐀").unwrap();
    let error = Error::secondary(&tokens[0], last, "unavailable dependency");
    assert_eq!(
        error.range(),
        Range::new(Position::new(0, 0), Position::new(1, 7))
    );
}

#[test]
fn numeric_class_type_errors_cover_the_complete_type_expression() {
    assert_diagnostic(
        "type Number: axiom\nclass Number {\n let 0: (Bool -> Bool) = axiom\n}",
        "(Bool -> Bool)",
        "numeric class variables must be the class type",
    );
}

#[test]
fn grouped_list_errors_cover_the_entire_expression() {
    use venticorn::expression::{Expression, Terminator};
    use venticorn::token::{TokenIter, TokenType};
    let mut tokens = TokenIter::new(Token::scan("left and right"));
    let (expression, _) =
        Expression::parse_value(&mut tokens, Terminator::Is(TokenType::NewLine)).unwrap();
    let error = expression.flatten_list(false).unwrap_err();
    assert!(error.message().contains("expected a grouped list"));
    assert_eq!(
        error.range(),
        Range::new(Position::new(0, 0), Position::new(0, 14))
    );
}

#[test]
fn misplaced_binders_are_highlighted_as_complete_parser_expressions() {
    assert_diagnostic(
        "theorem bad { true forall(x: Bool) { x } }",
        "forall(x: Bool) { x }",
        "expected a grouping",
    );
}
