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

#[test]
fn bound_expressions_parse_and_round_trip_without_erasure() {
    let source = "define choose<T: algebra.Magma, U>(left: T, right: U) -> T { left }";
    let statement = Statement::parse_str(source).unwrap();
    let StatementInfo::Define(definition) = &statement.statement else {
        panic!()
    };
    assert_eq!(
        definition.type_params[0]
            .typeclass
            .as_ref()
            .unwrap()
            .to_string(),
        "algebra.Magma"
    );
    assert!(definition.type_params[1].typeclass.is_none());
    let code = statement.to_string();
    assert_eq!(Statement::parse_str(&code).unwrap().to_string(), code);
    let mut env = venticorn::environment::Environment::new_test();
    env.add("typeclass M: Magma {\n mul: (M, M) -> M\n}");
    let statement =
        Statement::parse_str("define identity<T: Magma>(value: T) -> T { value }").unwrap();
    let error = env
        .add_statement(&mut venticorn::project::Project::new_mock(), &statement)
        .unwrap_err();
    assert!(error
        .message()
        .contains("typeclass bounds are not supported yet"));
    assert!(!env.bindings.name_in_use("identity"));
    assert!(!env.bindings.name_in_use("T"));
}

#[test]
fn malformed_bound_lists_are_rejected() {
    for source in [
        "define f<T:>(value: T) -> T { value }",
        "define f<T: Magma,>(value: T) -> T { value }",
        "define f<T: Magma U>(value: T) -> T { value }",
        "define f<T::Magma>(value: T) -> T { value }",
        "define f<: Magma>(value: Bool) -> Bool { value }",
    ] {
        assert!(Statement::parse_str(source).is_err(), "{source}");
    }
}

#[test]
fn all_declaration_parameter_lists_retain_bounds_without_accepting_them() {
    use venticorn::environment::Environment;
    use venticorn::project::Project;
    for source in [
        "theorem reflexive<T: Magma>(value: T) { value = value }",
        "structure Box<T: Magma> {\n value: T\n}",
        "class Pair<T: Magma> {\n define same(self) -> Bool { true }\n}",
    ] {
        let statement = Statement::parse_str(source).unwrap();
        let code = statement.to_string();
        assert!(code.contains("T: Magma"));
        assert_eq!(Statement::parse_str(&code).unwrap().to_string(), code);
        let mut env = Environment::new_test();
        env.add("typeclass M: Magma {\n mul: (M, M) -> M\n}\nstructure Pair<U> {\n value: U\n}");
        let error = env
            .add_statement(&mut Project::new_mock(), &statement)
            .unwrap_err();
        assert!(
            error
                .message()
                .contains("typeclass bounds are not supported yet"),
            "{error}"
        );
        for name in ["T", "Box", "Box.new", "Pair.same", "reflexive"] {
            assert!(!env.bindings.name_in_use(name), "{name}");
        }
    }
}
