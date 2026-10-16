use venticorn::statement::{Statement, StatementInfo};

#[test]
fn structured_function_parameters_preserve_names_order_and_ranges() {
    let source = "define first<T, U>(left: T, right: U) -> T { left }";
    let statement = Statement::parse_str(source).unwrap();
    let StatementInfo::Define(definition) = &statement.statement else {
        panic!()
    };
    assert_eq!(
        definition
            .type_params
            .iter()
            .map(|p| p.name.text())
            .collect::<Vec<_>>(),
        ["T", "U"]
    );
    assert!(definition.type_params.iter().all(|p| p.typeclass.is_none()));
    assert_eq!(definition.type_params[0].name.start_pos().character, 13);
    assert_eq!(definition.type_params[1].name.start_pos().character, 16);
    let code = statement.to_string();
    assert_eq!(Statement::parse_str(&code).unwrap().to_string(), code);
}
