// Modified for Venticorn: explicit typeclass admission expectations.
use venticorn::environment::Environment;

#[test]
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
    assert_eq!(
        error.message(),
        "name refers to a typeclass but we expected a type"
    );
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

#[test]
fn admitted_members_keep_instance_parameters_and_scope_cleanup() {
    use venticorn::acorn_type::{AcornType, Typeclass};
    use venticorn::binding_map::PotentialValue;
    let mut env = Environment::new_test();
    env.add("typeclass M: Magma {\n mul: (M, M) -> M\n flag: Bool\n}");
    let class = Typeclass {
        module_id: env.module_id,
        name: "Magma".into(),
    };
    assert_eq!(env.bindings.get_typeclass_for_name("Magma"), Some(&class));
    assert!(!env.bindings.name_in_use("M"));
    assert!(!env.bindings.has_type_name("Magma"));
    assert!(env.nodes.is_empty());
    for name in ["Magma.mul", "Magma.flag"] {
        assert_eq!(
            env.bindings.get_params(name),
            [venticorn::acorn_type::TypeParam {
                name: "M".into(),
                typeclass: Some(class.clone())
            }]
        );
        assert!(matches!(
            env.bindings.get_constant_value(name),
            Some(PotentialValue::Unresolved(_))
        ));
    }
    let instance = AcornType::Variable(venticorn::acorn_type::TypeParam {
        name: "M".into(),
        typeclass: Some(class),
    });
    assert_eq!(
        env.bindings
            .get_constant_value("Magma.mul")
            .unwrap()
            .get_type(),
        AcornType::new_functional(vec![instance.clone(), instance.clone()], instance)
    );
    env.add("type M: axiom");
    env.add("typeclass N: Other {\n value: N\n}");
}

#[test]
fn failed_members_allow_safe_name_reuse_and_conditions_create_no_axioms() {
    let mut env = Environment::new_test();
    env.add("let keep: Bool = true");
    let nodes = env.nodes.len();
    for source in [
        "typeclass M: Magma {\n mul: (M, M) -> M\n bad: Missing\n}",
        "typeclass M: Magma {\n flag: Bool\n flag: Bool\n}",
        "typeclass M: Magma {\n mul: (M, M) -> M\n law { false }\n}",
    ] {
        env.bad(source);
        assert_eq!(env.nodes.len(), nodes);
        assert!(!env.includes_explicit_false);
        assert!(!env.bindings.name_in_use("Magma"));
        assert!(!env.bindings.name_in_use("M"));
        assert!(!env.bindings.name_in_use("Magma.mul"));
    }
    env.add("typeclass M: Magma {\n mul: (M, M) -> M\n}");
}

#[test]
fn nested_class_declarations_are_located_and_cannot_escape_or_conflate() {
    use venticorn::project::Project;
    use venticorn::statement::Statement;
    let mut parent = Environment::new_test();
    parent.add("let keep: Bool = true");
    for _ in 0..2 {
        let mut child = parent.child(0, false);
        child.add("let local: Bool = true");
        let nodes = child.nodes.len();
        let last_line = child.last_line();
        let statement = Statement::parse_str("typeclass T: Local {\n value: T\n}").unwrap();
        let error = child
            .add_statement(&mut Project::new_mock(), &statement)
            .unwrap_err();
        assert!(error.message().contains("only supported at the top level"));
        assert_eq!(error.range().start.line, 0);
        assert_eq!(error.range().start.character, 0);
        assert_eq!(child.nodes.len(), nodes);
        assert_eq!(child.last_line(), last_line);
        for name in ["T", "Local", "Local.value"] {
            assert!(!child.bindings.name_in_use(name));
            assert!(!parent.bindings.name_in_use(name));
        }
        assert!(child.bindings.has_identifier("local"));
    }
    parent.add("typeclass T: Local {\n value: T\n}");
}

#[test]
fn bounded_instance_method_template_is_admitted() {
    let mut env = Environment::new_test();
    env.add(
        r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }
            define squared<T: Magma>(a: T) -> T {
                a.mul(a)
            }
            "#,
    );
}

#[test]
fn bounded_qualified_member_template_is_admitted() {
    let mut env = Environment::new_test();
    env.add(
        r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }
            define squared<T: Magma>(a: T) -> T {
                Magma.mul(a, a)
            }
            "#,
    );
}

#[test]
fn bounded_function_without_member_access_is_admitted() {
    let mut env = Environment::new_test();
    env.add(
        r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }
            define true_fn<T: Magma>(a: T) -> Bool {
                true
            }
            "#,
    );
}

#[test]
fn bounded_instance_method_declarations_are_admitted() {
    let mut env = Environment::new_test();
    let source = r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }
            define squared<T: Magma>(a: T) -> T {
                a.mul(a)
            }
            "#;
    env.add(source);
}

#[test]
fn bounded_theorem_admission_does_not_assume_class_laws() {
    let mut env = Environment::new_test();
    let source = r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }
            theorem wrong_but_syntactic<Q: Magma>(a: Q, b: Q) {
                a.mul(b) = b.mul(a)
            }
            "#;
    env.add(source);
    use venticorn::project::Project;
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", source);
    let module = project.expect_ok("main");
    let node = project
        .get_env_by_id(module)
        .unwrap()
        .get_node_by_name("wrong_but_syntactic");
    let mut prover = venticorn::prover::Prover::new(&project, false);
    for fact in node.usable_facts(&project) {
        prover.add_fact(fact);
    }
    prover.set_goal(&node.goal_context().unwrap());
    let mut ordinary = prover.clone();
    assert!(matches!(
        ordinary.quick_search(),
        venticorn::prover::Outcome::Exhausted
            | venticorn::prover::Outcome::Timeout
            | venticorn::prover::Outcome::Constrained
    ));
    assert_eq!(
        prover.quick_verification_search(),
        venticorn::prover::Outcome::Exhausted
    );
}
