// Modified for Venticorn: explicit typeclass admission expectations.
use venticorn::environment::Environment;

#[test]
#[ignore = "typeclass member admission is not implemented yet"]
fn constant_only_typeclass_is_admitted() {
    let mut env = Environment::new_test();
    env.add(
        r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }
            "#,
    );
}

#[test]
fn class_headers_validate_names_without_leaking_temporary_types() {
    use venticorn::acorn_type::Typeclass;
    use venticorn::project::Project;
    use venticorn::statement::Statement;

    for (source, expected) in [
        (
            "typeclass Existing: Magma {\n value: Bool\n}",
            "Existing already defined",
        ),
        (
            "typeclass M: Existing {\n value: M\n}",
            "Existing already defined",
        ),
        (
            "typeclass M: Reserved {\n value: M\n}",
            "Reserved already defined",
        ),
        ("typeclass M: M {\n value: M\n}", "names must be distinct"),
        ("typeclass M: Magma {\n value: M\n}", "not supported yet"),
    ] {
        let mut env = Environment::new_test();
        env.add("type Existing: axiom");
        env.bindings.add_typeclass(
            "Reserved",
            Typeclass {
                module_id: env.module_id,
                name: "Reserved".into(),
            },
        );
        let nodes = env.nodes.len();
        let last_line = env.last_line();
        let statement = Statement::parse_str(source).unwrap();
        let error = env
            .add_statement(&mut Project::new_mock(), &statement)
            .unwrap_err();
        assert!(error.message().contains(expected), "{error}");
        assert_eq!(error.range().start.line, 0);
        assert_eq!(env.nodes.len(), nodes);
        assert_eq!(env.last_line(), last_line);
        assert!(!env.bindings.name_in_use("M"));
        assert!(!env.bindings.name_in_use("Magma"));
        assert!(!env.bindings.has_identifier("Magma.value"));
        assert!(env.bindings.has_type_name("Existing"));
        assert!(env.bindings.get_typeclass_for_name("Reserved").is_some());
    }
}

#[test]
fn class_name_is_not_a_member_return_type() {
    let mut env = Environment::new_test();
    let source = r#"
            typeclass M: Magma {
                mul: (M, M) -> Magma
            }
            "#;
    env.bad(source);
    let statement = venticorn::statement::Statement::parse_str(source).unwrap();
    let error = env
        .add_statement(&mut venticorn::project::Project::new_mock(), &statement)
        .unwrap_err();
    assert_eq!(error.message(), "expected type name");
    assert_eq!(error.range().start.line, 2);
}

#[test]
fn member_validation_is_selective_and_transactional() {
    use venticorn::project::Project;
    use venticorn::statement::Statement;
    for (source, expected) in [
        (
            "typeclass M: Magma {\n mul: (M, M) -> M\n bad: Missing\n}",
            "expected type name",
        ),
        (
            "typeclass M: Magma {\n mul: (M, M) -> M\n mul: Bool\n}",
            "member already defined",
        ),
        (
            "typeclass M: Magma {\n bad: Outer\n}",
            "cannot capture an outer arbitrary type",
        ),
        (
            "typeclass M: Magma {\n mul: (M, M) -> M\n law(a: M) { false }\n}",
            "conditions are not supported",
        ),
    ] {
        let mut env = Environment::new_test();
        env.add("let keep: Bool = true");
        env.bindings.add_arbitrary_type("Outer");
        let nodes = env.nodes.len();
        let last_line = env.last_line();
        let error = env
            .add_statement(
                &mut Project::new_mock(),
                &Statement::parse_str(source).unwrap(),
            )
            .unwrap_err();
        assert!(error.message().contains(expected), "{error}");
        assert_eq!(env.nodes.len(), nodes);
        assert_eq!(env.last_line(), last_line);
        for name in ["M", "Magma", "Magma.mul", "Magma.bad"] {
            assert!(!env.bindings.name_in_use(name), "{name}");
        }
        assert!(env.bindings.has_identifier("keep"));
        assert!(env.bindings.has_type_name("Outer"));
    }
}
