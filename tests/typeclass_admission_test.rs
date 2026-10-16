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
    env.bad(
        r#"
            typeclass M: Magma {
                mul: (M, M) -> Magma
            }
            "#,
    );
}
