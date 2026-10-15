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

#[test]
fn proof_scope_generalizes_only_its_declared_parameters() {
    use venticorn::acorn_type::AcornType;
    use venticorn::acorn_value::AcornValue;
    let outer = AcornType::Arbitrary("Outer".into(), None);
    let inner = AcornType::Arbitrary("Inner".into(), None);
    let value = AcornValue::ForAll(
        vec![outer.clone(), inner.clone()],
        Box::new(AcornValue::Bool(true)),
    );
    let exported = value.parametrize(10, &["Inner".into()]);
    assert_eq!(
        exported,
        AcornValue::ForAll(
            vec![outer, AcornType::Variable("Inner".into(), None)],
            Box::new(AcornValue::Bool(true))
        )
    );
    let mut env = venticorn::environment::Environment::new_test();
    env.add("theorem reflexive<T>(value: T) { value = value } by { value = value }");
    assert!(!env.bindings.has_type_name("T"));
}

#[test]
fn generic_class_syntax_round_trips() {
    let source = "class Pair<T, U> {\n    define swap(self) -> Pair<U, T> { Pair.new(self.second, self.first) }\n}";
    let formatted = Statement::parse_str(source).unwrap().to_string();
    assert_eq!(
        Statement::parse_str(&formatted).unwrap().to_string(),
        formatted
    );
    assert!(formatted.contains("Pair<T, U>"));
}
