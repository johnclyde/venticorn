use venticorn::acorn_type::Class;
// Modified for Venticorn: validate application types before admitting logical facts.
use venticorn::acorn_type::AcornType;
use venticorn::acorn_value::AcornValue;

fn identity(t: AcornType) -> AcornValue {
    AcornValue::new_constant(
        10,
        "identity".into(),
        vec![],
        AcornType::new_functional(vec![t.clone()], t),
    )
}

#[test]
fn malformed_applications_fail_validation_without_panicking() {
    let nat = AcornType::Data(Class::new(10, "Nat".into()), vec![]);
    for value in [
        AcornValue::new_apply(AcornValue::Bool(true), vec![AcornValue::Bool(false)]),
        AcornValue::new_apply(identity(nat), vec![AcornValue::Bool(false)]),
        AcornValue::new_apply(
            identity(AcornType::Bool),
            vec![AcornValue::Bool(false), AcornValue::Bool(true)],
        ),
        AcornValue::new_apply(
            AcornValue::new_apply(AcornValue::Bool(true), vec![AcornValue::Bool(false)]),
            vec![AcornValue::Bool(true)],
        ),
    ] {
        assert!(value.validate().is_err());
    }
    assert!(
        AcornValue::new_apply(identity(AcornType::Bool), vec![AcornValue::Bool(false)])
            .validate()
            .is_ok()
    );
}

#[test]
fn parametrization_updates_recursive_constant_types() {
    let specific = identity(AcornType::Data(Class::new(10, "T".into()), vec![]));
    let generic = specific.parametrize(10, &["T".into()]);
    assert_eq!(
        generic.get_type(),
        AcornType::new_functional(
            vec![AcornType::Variable(venticorn::acorn_type::TypeParam {
                name: "T".into(),
                typeclass: None
            })],
            AcornType::Variable(venticorn::acorn_type::TypeParam {
                name: "T".into(),
                typeclass: None
            })
        )
    );
}

#[test]
fn constant_types_specialize_symmetrically_with_parametrization() {
    let specific = identity(AcornType::Data(Class::new(10, "T".into()), vec![]));
    let generic = specific.parametrize(10, &["T".into()]);
    let concrete = generic.instantiate(&[("T".into(), AcornType::Bool)]);
    assert_eq!(concrete.get_type(), identity(AcornType::Bool).get_type());
    assert!(!concrete.is_generic());
    assert!(
        AcornValue::new_apply(concrete, vec![AcornValue::Bool(true)])
            .validate()
            .is_ok()
    );
}

#[test]
fn generic_callbacks_use_their_declared_types_without_reinference() {
    use venticorn::environment::Environment;
    use venticorn::project::Project;
    use venticorn::statement::Statement;
    let mut env = Environment::new_test();
    env.add("define apply<T>(f: T -> T, value: T) -> T { f(value) }");
    env.get_definition("apply").unwrap().validate().unwrap();
    assert!(!env.bindings.has_type_name("T"));

    for source in [
        "define bad<T>(f: T -> T, value: T) -> T { f(true) }",
        "define bad<T>(f: T -> Bool, value: T) -> T { f(value) }",
    ] {
        let error = env
            .add_statement(
                &mut Project::new_mock(),
                &Statement::parse_str(source).unwrap(),
            )
            .unwrap_err();
        assert!(error.message().contains("expected type"), "{error}");
        assert!(!env.bindings.has_identifier("bad"));
        assert!(!env.bindings.has_type_name("T"));
    }
}

#[test]
fn resolved_simple_constants_keep_their_plain_normalized_identity() {
    use venticorn::normalizer::Normalizer;
    let resolved = AcornValue::new_constant(10, "p".into(), vec![], AcornType::Bool);
    assert_eq!(resolved.as_simple_constant(), Some((10, "p".to_string())));
    assert!(!Normalizer::new()
        .normalize(&resolved, true)
        .expect_clauses()
        .is_empty());
    let generic = AcornType::Variable(venticorn::acorn_type::TypeParam {
        name: "T".into(),
        typeclass: None,
    });
    let instance = AcornValue::new_constant(
        10,
        "f".into(),
        vec![AcornType::Bool],
        generic.instantiate(&[("T".into(), AcornType::Bool)]),
    );
    assert_eq!(instance.as_simple_constant(), None);
}

#[test]
fn pending_generic_names_cannot_create_alias_facts() {
    use venticorn::environment::Environment;
    use venticorn::project::Project;
    use venticorn::statement::Statement;
    let mut env = Environment::new_test();
    env.add("let known: Bool = axiom\ndefine pending<T>(value: T) -> T { value }");
    let node_count = env.nodes.len();
    let statement = Statement::parse_str("let alias: Bool = pending = known").unwrap();
    let error = env
        .add_statement(&mut Project::new_mock(), &statement)
        .unwrap_err();
    assert_eq!(error.message(), "value pending requires type arguments");
    assert_eq!(error.range().start.character, 18);
    assert_eq!(error.range().end.character, 25);
    assert!(!env.bindings.has_identifier("alias"));
    assert_eq!(env.nodes.len(), node_count);
    env.add("let alias: Bool = known");
    let value = env
        .bindings
        .get_constant_value("alias")
        .unwrap()
        .resolved()
        .unwrap();
    assert_eq!(value.as_name(), Some((env.module_id, "known".to_string())));
    value.validate().unwrap();
}

#[test]
fn direct_and_qualified_generic_imports_preserve_resolved_types() {
    use venticorn::project::Project;
    let mut project = Project::new_mock();
    project.mock(
        "/mock/generic.ac",
        "define identity<T>(value: T) -> T { value }",
    );
    project.mock(
        "/mock/direct.ac",
        "from generic import identity\ntheorem goal { identity(true) = true }",
    );
    project.mock(
        "/mock/qualified.ac",
        "import generic\ntheorem goal { generic.identity(true) = true }",
    );
    for module in ["direct", "qualified"] {
        let id = project.expect_ok(module);
        for node in project.get_env_by_id(id).unwrap().iter_goals() {
            node.goal_context()
                .unwrap()
                .goal
                .value()
                .validate()
                .unwrap();
        }
    }
}

#[test]
fn inference_preserves_declared_parameter_order_instead_of_sorting_names() {
    use venticorn::environment::Environment;
    use venticorn::expression::Expression;
    use venticorn::project::Project;
    let mut env = Environment::new_test();
    env.add("inductive Nat {\n zero\n suc(Nat)\n}");
    let z = AcornType::Variable(venticorn::acorn_type::TypeParam {
        name: "Z".into(),
        typeclass: None,
    });
    let a = AcornType::Variable(venticorn::acorn_type::TypeParam {
        name: "A".into(),
        typeclass: None,
    });
    env.bindings.add_constant(
        "choose",
        vec![
            venticorn::acorn_type::TypeParam::unconstrained("Z"),
            venticorn::acorn_type::TypeParam::unconstrained("A"),
        ],
        AcornType::new_functional(vec![z, a.clone()], a),
        None,
        None,
    );
    let value = env
        .bindings
        .evaluate_value(
            &Project::new_mock(),
            &Expression::expect_value("choose(true, Nat.zero)"),
            None,
        )
        .unwrap();
    value.validate().unwrap();
    let nat = AcornType::Data(Class::new(env.module_id, "Nat".into()), vec![]);
    assert_eq!(value.get_type(), nat);
    let AcornValue::Application(app) = value else {
        panic!("expected application")
    };
    let AcornValue::Constant(c) = *app.function else {
        panic!("expected resolved constant")
    };
    assert_eq!(c.params, vec![AcornType::Bool, nat]);
}

#[test]
fn ordinary_partial_and_higher_order_calls_check_the_expected_result() {
    use venticorn::environment::Environment;
    use venticorn::project::Project;
    use venticorn::statement::Statement;
    let mut env = Environment::new_test();
    env.add("inductive Nat {\n zero\n suc(Nat)\n}");
    env.add("define keep(first: Bool, second: Bool) -> Bool { first }");
    env.add("define apply(f: Bool -> Bool, flag: Bool) -> Bool { f(flag) }");
    env.add("define id_nat(value: Nat) -> Nat { value }");
    env.add("let partial: Bool -> Bool = keep(true)\nlet full: Bool = partial(false)");
    for source in [
        "let bad: Nat = keep(true, false)",
        "let bad: Bool = keep(true)",
        "let bad: Nat = apply(partial, true)",
        "let bad: Nat -> Bool = function(n: Nat) { keep(true) }",
        "let bad: Nat = id_nat(forall(flag: Bool) { flag = flag })",
        "let bad: Nat = id_nat(exists(flag: Bool) { flag = flag })",
    ] {
        let error = env
            .add_statement(
                &mut Project::new_mock(),
                &Statement::parse_str(source).unwrap(),
            )
            .unwrap_err();
        assert!(error.message().contains("expected type"), "{error}");
        assert!(!env.bindings.has_identifier("bad"));
    }
}

#[test]
fn pending_generic_values_are_rejected_before_declaration_admission() {
    use venticorn::environment::Environment;
    use venticorn::project::Project;
    use venticorn::statement::Statement;
    let mut env = Environment::new_test();
    env.add("define identity<T>(value: T) -> T { value }");
    for source in [
        "theorem bad { identity = identity }",
        "define bad<T>(value: T) -> (T -> T) { identity }",
        "define bad<T>(value: T) -> Bool { identity = identity }",
    ] {
        let node_count = env.nodes.len();
        let error = env
            .add_statement(
                &mut Project::new_mock(),
                &Statement::parse_str(source).unwrap(),
            )
            .unwrap_err();
        assert_eq!(error.message(), "value identity requires type arguments");
        assert!(error.range().end.character > error.range().start.character);
        assert!(!env.bindings.has_identifier("bad"));
        assert!(!env.bindings.has_type_name("T"));
        assert_eq!(env.nodes.len(), node_count);
    }
    env.add("let good: Bool = identity(true)");
}

#[test]
fn resolved_type_transformations_preserve_declaration_namespaces() {
    let t = AcornType::Variable(venticorn::acorn_type::TypeParam {
        name: "T".into(),
        typeclass: None,
    });
    let plain = identity(t.clone());
    assert!(plain.is_generic());
    assert_eq!(
        plain.to_arbitrary().get_type(),
        identity(AcornType::Arbitrary(venticorn::acorn_type::TypeParam {
            name: "T".into(),
            typeclass: None
        }))
        .get_type()
    );
    let a = AcornType::Variable(venticorn::acorn_type::TypeParam {
        name: "A".into(),
        typeclass: None,
    });
    let template = AcornType::new_functional(vec![a.clone()], a);
    let instance = AcornValue::new_constant(
        10,
        "f".into(),
        vec![t.clone()],
        template.instantiate(&[("A".into(), t)]),
    );
    let specialized = instance.instantiate(&[("T".into(), AcornType::Bool)]);
    assert_eq!(specialized.get_type(), identity(AcornType::Bool).get_type());
    let AcornValue::Constant(c) = instance.to_arbitrary() else {
        panic!("constant expected")
    };
    assert_eq!(
        c.instance_type,
        identity(AcornType::Arbitrary(venticorn::acorn_type::TypeParam {
            name: "T".into(),
            typeclass: None
        }))
        .get_type()
    );
    assert_eq!(
        c.params,
        vec![AcornType::Arbitrary(venticorn::acorn_type::TypeParam {
            name: "T".into(),
            typeclass: None
        })]
    );
}

#[test]
fn quantified_function_bodies_must_match_the_declared_result() {
    use venticorn::environment::Environment;
    use venticorn::project::Project;
    use venticorn::statement::Statement;
    let mut env = Environment::new_test();
    env.add("type Nat: axiom");
    for source in [
        "let bad: Nat = forall(flag: Bool) { flag = flag }",
        "let bad: Nat = exists(flag: Bool) { flag = flag }",
        "define bad(value: Nat) -> Nat { forall(flag: Bool) { flag = flag } }",
        "define bad(value: Nat) -> Nat { exists(flag: Bool) { flag = flag } }",
    ] {
        let count = env.nodes.len();
        let error = env
            .add_statement(
                &mut Project::new_mock(),
                &Statement::parse_str(source).unwrap(),
            )
            .unwrap_err();
        assert!(
            error
                .message()
                .contains("expected type Nat, but this is Bool"),
            "{error}"
        );
        assert!(!env.bindings.has_identifier("bad"));
        assert_eq!(env.nodes.len(), count);
    }
}

#[test]
fn constant_admission_validates_definitions_before_mutating_bindings() {
    use std::panic::{catch_unwind, AssertUnwindSafe};
    use venticorn::binding_map::BindingMap;
    let mut bindings = BindingMap::new(10);
    let malformed = AcornValue::new_apply(
        identity(AcornType::Bool),
        vec![AcornValue::new_constant(
            10,
            "item".into(),
            vec![],
            AcornType::Data(Class::new(10, "Item".into()), vec![]),
        )],
    );
    assert!(catch_unwind(AssertUnwindSafe(|| bindings.add_constant(
        "invalid",
        vec![],
        AcornType::Bool,
        Some(malformed),
        None
    )))
    .is_err());
    assert!(!bindings.has_identifier("invalid"));
    bindings.add_constant(
        "invalid",
        vec![],
        AcornType::Bool,
        Some(AcornValue::Bool(true)),
        None,
    );
}
