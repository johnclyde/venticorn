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
    env.add_statement(&mut venticorn::project::Project::new_mock(), &statement)
        .unwrap();
    assert!(env.bindings.name_in_use("identity"));
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
fn declaration_parameter_lists_retain_bounds_at_family_consumers() {
    use venticorn::environment::Environment;
    use venticorn::project::Project;
    let mut env = Environment::new_test();
    env.add("typeclass M: Magma {\n mul: (M, M) -> M\n}\nstructure Pair<U> {\n value: U\n}");
    for source in [
        "structure Box<T: Magma> {\n value: T\n}",
        "class Box<Renamed: Magma> {\n define same(self) -> Bool { true }\n}",
    ] {
        let statement = Statement::parse_str(source).unwrap();
        let code = statement.to_string();
        assert!(code.contains(": Magma"));
        assert_eq!(Statement::parse_str(&code).unwrap().to_string(), code);
        env.add_statement(&mut Project::new_mock(), &statement)
            .unwrap();
    }
    let error = env
        .add_statement(
            &mut Project::new_mock(),
            &Statement::parse_str("class Pair<T: Magma> {\n define same(self) -> Bool { true }\n}")
                .unwrap(),
        )
        .unwrap_err();
    assert!(error.message().contains("bound conflicts"), "{error}");
    for name in ["T", "Renamed", "Pair.same"] {
        assert!(!env.bindings.name_in_use(name));
    }
}

#[test]
fn bounded_function_declarations_preserve_qualified_class_identity() {
    use venticorn::acorn_type::{AcornType, Typeclass};
    let mut project = venticorn::project::Project::new_mock();
    for module in ["left", "right"] {
        project.mock(
            &format!("/mock/{module}.ac"),
            "typeclass M: Magma {\n mul: (M, M) -> M\n}",
        );
    }
    project.mock("/mock/main.ac", "import left\nimport right\ndefine left_id<T: left.Magma>(value: T) -> T { value }\ndefine right_id<T: right.Magma>(value: T) -> T { value }");
    let id = project.expect_ok("main");
    let left = project.expect_ok("left");
    let right = project.expect_ok("right");
    let env = project.get_env_by_id(id).unwrap();
    for (name, module) in [("left_id", left), ("right_id", right)] {
        let parameter = AcornType::Variable(venticorn::acorn_type::TypeParam {
            name: "T".into(),
            typeclass: Some(Typeclass {
                module_id: module,
                name: "Magma".into(),
            }),
        });
        assert_eq!(
            env.bindings.get_constant_value(name).unwrap().get_type(),
            AcornType::new_functional(vec![parameter.clone()], parameter)
        );
    }
    assert_ne!(left, right);
    assert!(!env.bindings.name_in_use("T"));
}

#[test]
fn invalid_bounds_and_erased_theorem_formals_reject_without_publication() {
    use venticorn::environment::Environment;
    use venticorn::project::Project;
    let mut env = Environment::new_test();
    env.add("typeclass M: Magma {\n mul: (M, M) -> M\n}\ndefine identity<T: Magma>(value: T) -> T { value }");
    for (source, expected) in [
        (
            "define bad<T: Bool>(value: T) -> T { value }",
            "expected a typeclass",
        ),
        (
            "axiom bad<T: Magma> { false }",
            "must occur in the exported proposition",
        ),
        (
            "theorem bad<T: Magma> { true }",
            "must occur in the exported proposition",
        ),
        (
            "let bad: Bool = identity<Bool>(true)",
            "does not satisfy the class bound",
        ),
        ("let bad: Bool = identity(true)", "expected type"),
        (
            "define bad<U>(value: U) -> U { identity(value) }",
            "expected type",
        ),
        (
            "define bad<U>(value: U) -> U { identity<U>(value) }",
            "does not satisfy the class bound",
        ),
    ] {
        let nodes = env.nodes.len();
        let error = env
            .add_statement(
                &mut Project::new_mock(),
                &Statement::parse_str(source).unwrap(),
            )
            .unwrap_err();
        assert!(error.message().contains(expected), "{source}: {error}");
        assert!(!env.bindings.name_in_use("bad"));
        assert!(!env.bindings.name_in_use("T"));
        assert_eq!(env.nodes.len(), nodes);
    }
}

#[test]
fn evaluated_parameter_lists_keep_order_canonical_bounds_and_locations() {
    use venticorn::project::Project;
    let mut project = Project::new_mock();
    for module in ["left", "right"] {
        project.mock(
            &format!("/mock/{module}.ac"),
            "typeclass M: Magma {\n mul: (M, M) -> M\n}",
        );
    }
    project.mock(
        "/mock/main.ac",
        "import left\nimport right\nlet occupied: Bool = true",
    );
    let id = project.expect_ok("main");
    let bindings = &project.get_env_by_id(id).unwrap().bindings;
    let declaration = Statement::parse_str(
        "define choose<T: left.Magma, U: right.Magma, V>(value: T) -> T { value }",
    )
    .unwrap();
    let StatementInfo::Define(definition) = declaration.statement else {
        panic!()
    };
    let params = bindings
        .evaluate_type_params(&project, &definition.type_params)
        .unwrap();
    assert_eq!(
        params.iter().map(|p| p.name.as_str()).collect::<Vec<_>>(),
        ["T", "U", "V"]
    );
    assert_ne!(params[0].typeclass, params[1].typeclass);
    assert_eq!(params[0].typeclass.as_ref().unwrap().name, "Magma");
    assert_eq!(params[1].typeclass.as_ref().unwrap().name, "Magma");
    assert!(params[2].typeclass.is_none());
    for (source, message, bound_error) in [
        (
            "define bad<T, T>(x: T) -> T { x }",
            "duplicate type parameter",
            false,
        ),
        (
            "define bad<T, occupied>(x: T) -> T { x }",
            "already defined",
            false,
        ),
        (
            "define bad<T, U: Bool>(x: T) -> T { x }",
            "expected a typeclass",
            true,
        ),
        (
            "define bad<T, U: missing>(x: T) -> T { x }",
            "unknown identifier",
            true,
        ),
    ] {
        let statement = Statement::parse_str(source).unwrap();
        let StatementInfo::Define(definition) = statement.statement else {
            panic!()
        };
        let last = definition.type_params.last().unwrap();
        let expected = if bound_error {
            last.typeclass.as_ref().unwrap().range()
        } else {
            last.name.range()
        };
        let error = bindings
            .evaluate_type_params(&project, &definition.type_params)
            .unwrap_err();
        assert!(error.message().contains(message), "{source}: {error}");
        assert_eq!(error.range(), expected);
    }
    for name in ["T", "U", "V", "bad", "choose"] {
        assert!(!bindings.name_in_use(name));
    }
}

#[test]
fn invalid_parameter_lists_leave_no_partial_scope_bindings() {
    use venticorn::environment::Environment;
    use venticorn::project::Project;
    let mut env = Environment::new_test();
    env.add("typeclass M: Magma {\n mul: (M, M) -> M\n}\nstructure Pair<T, U> {\n first: T\n second: U\n}");
    for source in [
        "define bad<T, U: Bool>(x: T) -> T { x }",
        "define bad<T, T>(x: T) -> T { x }",
        "structure Bad<T, U: Bool> {\n first: T\n second: U\n}",
        "structure Bad<T, T> {\n first: T\n}",
        "structure Bad<Bad> {\n first: Bad\n}",
        "class Pair<T, U: Bool> { define bad(self) -> T { self.first } }",
        "class Pair<T, T> { define bad(self) -> T { self.first } }",
    ] {
        let nodes = env.nodes.len();
        let statement = Statement::parse_str(source).unwrap();
        assert!(
            env.add_statement(&mut Project::new_mock(), &statement)
                .is_err(),
            "{source}"
        );
        assert_eq!(env.nodes.len(), nodes);
        for name in ["T", "U", "Bad", "bad", "Pair.bad"] {
            assert!(!env.bindings.name_in_use(name), "{source}: {name}");
        }
    }
    env.add("define identity<T: Magma, U>(x: T, unused: U) -> T { x }");
    env.add("class Pair<A, B> { define first_value(self) -> A { self.first } }");
}
