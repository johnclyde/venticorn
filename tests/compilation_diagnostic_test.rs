// Modified for Venticorn: compiler ranges use the editor protocol's UTF-16 units.
use tower_lsp::lsp_types::{Position, Range};
use venticorn::compilation::Error;
use venticorn::project::Project;
use venticorn::token::Token;

fn assert_error_span(code: &str, text: &str) {
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", code);
    let errors = project.errors();
    assert_eq!(errors.len(), 1);
    let error = errors[0].1;
    assert!(error.message().contains("unknown identifier"), "{error}");
    let start = code.find(text).unwrap();
    let first = code[..start].encode_utf16().count() as u32;
    let last = first + text.encode_utf16().count() as u32;
    assert_eq!(
        error.range(),
        Range::new(Position::new(0, first), Position::new(0, last))
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
    let error = Error::new(&Token::empty(), "missing expression");
    assert_eq!(
        error.range(),
        Range::new(Position::new(0, 0), Position::new(0, 0))
    );
    assert!(error.to_string().ends_with("\n^\n"));
    let tokens = Token::scan("x𐐀é");
    let error = Error::new(tokens.last().unwrap(), "missing expression");
    assert_eq!(
        error.range(),
        Range::new(Position::new(0, 4), Position::new(0, 4))
    );
    assert!(error.to_string().ends_with("   ^\n"));
}
