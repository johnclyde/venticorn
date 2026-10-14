// Modified for Venticorn: validate application types before admitting logical facts.
use venticorn::acorn_type::AcornType;
use venticorn::acorn_value::AcornValue;

fn identity(t: AcornType) -> AcornValue {
    AcornValue::Unresolved(
        10,
        "identity".into(),
        AcornType::new_functional(vec![t.clone()], t),
        vec![],
    )
}

#[test]
fn malformed_applications_fail_validation_without_panicking() {
    let nat = AcornType::Data(10, "Nat".into());
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
    let specific = identity(AcornType::Data(10, "T".into()));
    let generic = specific.parametrize(10, &["T".into()]);
    assert_eq!(
        generic.get_type(),
        AcornType::new_functional(
            vec![AcornType::Variable("T".into(), None)],
            AcornType::Variable("T".into(), None)
        )
    );
}

#[test]
fn constant_types_specialize_symmetrically_with_parametrization() {
    let specific = identity(AcornType::Data(10, "T".into()));
    let generic = specific.parametrize(10, &["T".into()]);
    let concrete = generic.specialize(&[("T".into(), AcornType::Bool)]);
    assert_eq!(concrete.get_type(), identity(AcornType::Bool).get_type());
    assert!(!concrete.is_parametric());
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
    let resolved = AcornValue::Constant(10, "p".into(), AcornType::Bool, vec![]);
    let transitional = AcornValue::Unresolved(10, "p".into(), AcornType::Bool, vec![]);
    assert_eq!(resolved.as_simple_constant(), Some((10, "p")));
    assert_eq!(
        Normalizer::new()
            .normalize(&resolved, true)
            .expect_clauses(),
        Normalizer::new()
            .normalize(&transitional, true)
            .expect_clauses()
    );
    let generic = AcornType::Variable("T".into(), None);
    let instance =
        AcornValue::Constant(10, "f".into(), generic, vec![("T".into(), AcornType::Bool)]);
    assert_eq!(instance.as_simple_constant(), None);
}

#[test]
fn unresolved_generic_metadata_cannot_bypass_normalization_through_aliases() {
    use venticorn::normalizer::{Normalization, Normalizer};
    let mut normalizer = Normalizer::new();
    let known = AcornValue::Constant(10, "known".into(), AcornType::Bool, vec![]);
    let known_clauses = normalizer.normalize(&known, true).expect_clauses();
    let pending = AcornValue::Unresolved(10, "pending".into(), AcornType::Bool, vec!["T".into()]);
    assert!(pending.as_simple_constant().is_none());
    assert!(matches!(
        normalizer.normalize(&AcornValue::new_equals(pending, known), true),
        Normalization::Error(_)
    ));
    let ordinary = AcornValue::Constant(10, "pending".into(), AcornType::Bool, vec![]);
    assert_ne!(
        normalizer.normalize(&ordinary, true).expect_clauses(),
        known_clauses,
        "rejected pending metadata must not register a constant alias"
    );
}

#[test]
fn generic_imports_have_a_clear_limit_and_qualified_calls_remain_supported() {
    use venticorn::module::Module;
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
    let id = project.load_module_by_name("direct").unwrap();
    match project.get_module_by_id(id) {
        Module::Error(error) => assert!(
            error
                .message()
                .contains("direct imports of generic constants are not supported"),
            "{error}"
        ),
        _ => panic!("generic import must be rejected before losing its parameter metadata"),
    }
    project.mock(
        "/mock/qualified.ac",
        "import generic\ntheorem goal { generic.identity(true) = true }",
    );
    let id = project.expect_ok("qualified");
    for node in project.get_env_by_id(id).unwrap().iter_goals() {
        node.goal_context()
            .unwrap()
            .goal
            .value()
            .validate()
            .unwrap();
    }
}

#[test]
fn inference_preserves_declared_parameter_order_instead_of_sorting_names() {
    use venticorn::environment::Environment;
    use venticorn::expression::Expression;
    use venticorn::project::Project;
    let mut env = Environment::new_test();
    env.add("inductive Nat {\n zero\n suc(Nat)\n}");
    let z = AcornType::Variable("Z".into(), None);
    let a = AcornType::Variable("A".into(), None);
    env.bindings.add_constant(
        "choose",
        vec!["Z".into(), "A".into()],
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
    let nat = AcornType::Data(env.module_id, "Nat".into());
    assert_eq!(value.get_type(), nat);
    let AcornValue::Application(app) = value else {
        panic!("expected application")
    };
    let AcornValue::Constant(_, _, _, params) = *app.function else {
        panic!("expected resolved constant")
    };
    assert_eq!(
        params,
        vec![("Z".into(), AcornType::Bool), ("A".into(), nat)]
    );
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
