use venticorn::statement::Statement;

#[test]
fn generic_structure_syntax_round_trips() {
    let source = "structure Pair<T, U> {\n    first: T\n    second: U\n}";
    let formatted = Statement::parse_str(source).unwrap().to_string();
    assert_eq!(
        Statement::parse_str(&formatted).unwrap().to_string(),
        formatted
    );
    assert!(formatted.contains("Pair<T, U>"));
    for source in [
        "structure Pair<> { first: Bool }",
        "structure Pair<T,> { first: T }",
        "structure Pair<T U> { first: T }",
    ] {
        assert!(Statement::parse_str(source).is_err(), "{source}");
    }
}
