use venticorn::acorn_type::{AcornType, Typeclass};
use venticorn::binding_map::Stack;
use venticorn::environment::Environment;
use venticorn::expression::Expression;
use venticorn::project::Project;

#[test]
fn instance_lookup_uses_the_parameter_name_and_canonical_class() {
    let mut env = Environment::new_test();
    env.add("typeclass M: Magma {\n mul: (M, M) -> M\n}");
    let class = Typeclass {
        module_id: env.module_id,
        name: "Magma".into(),
    };
    for parameter in [
        AcornType::Variable(venticorn::acorn_type::TypeParam {
            name: "T".into(),
            typeclass: None,
        }),
        AcornType::Arbitrary(venticorn::acorn_type::TypeParam {
            name: "T".into(),
            typeclass: None,
        }),
    ] {
        let mut stack = Stack::new();
        stack.insert("value".into(), parameter);
        let error = env
            .bindings
            .evaluate_value_with_stack(
                &mut stack,
                &Project::new_mock(),
                &Expression::expect_value("value.mul"),
                None,
            )
            .unwrap_err();
        assert_eq!(error.message(), "unqualified type T has no attributes");
    }
    for parameter in [
        AcornType::Variable(venticorn::acorn_type::TypeParam {
            name: "T".into(),
            typeclass: Some(class.clone()),
        }),
        AcornType::Arbitrary(venticorn::acorn_type::TypeParam {
            name: "T".into(),
            typeclass: Some(class.clone()),
        }),
    ] {
        let mut stack = Stack::new();
        stack.insert("value".into(), parameter);
        let error = env
            .bindings
            .evaluate_value_with_stack(
                &mut stack,
                &Project::new_mock(),
                &Expression::expect_value("value.absent"),
                None,
            )
            .unwrap_err();
        assert_eq!(error.message(), "unknown attribute 'Magma.absent'");
        let member = env
            .bindings
            .evaluate_value_with_stack(
                &mut stack,
                &Project::new_mock(),
                &Expression::expect_value("value.mul"),
                None,
            )
            .unwrap();
        assert!(member.get_type().is_functional());
    }
    let mut stack = Stack::new();
    stack.insert(
        "value".into(),
        AcornType::Arbitrary(venticorn::acorn_type::TypeParam {
            name: "T".into(),
            typeclass: Some(Typeclass {
                module_id: env.module_id + 1,
                name: "Magma".into(),
            }),
        }),
    );
    let error = env
        .bindings
        .evaluate_value_with_stack(
            &mut stack,
            &Project::new_mock(),
            &Expression::expect_value("value.mul"),
            None,
        )
        .unwrap_err();
    assert_eq!(
        error.message(),
        "could not load bindings for attribute module"
    );
}

#[test]
fn class_names_are_distinct_entities_with_qualified_member_completion() {
    let mut project = Project::new_mock();
    project.mock(
        "/mock/left.ac",
        "typeclass M: Magma {\n mul: (M, M) -> M\n}",
    );
    project.mock(
        "/mock/right.ac",
        "typeclass M: Magma {\n other: (M, M) -> M\n}",
    );
    project.mock(
        "/mock/main.ac",
        "import left\nimport right\ntypeclass N: Local {\n value: N\n}",
    );
    let id = project.expect_ok("main");
    let env = project.get_env_by_id(id).unwrap();
    for (prefix, expected) in [
        ("left.Magma.", "mul"),
        ("right.Magma.", "other"),
        ("Local.", "value"),
    ] {
        let items = env
            .bindings
            .get_completions(&project, prefix, false)
            .unwrap();
        assert_eq!(
            items.iter().map(|i| i.label.as_str()).collect::<Vec<_>>(),
            [expected]
        );
    }
    for input in ["Local", "left.Magma"] {
        let error = env
            .bindings
            .evaluate_value(&project, &Expression::expect_value(input), None)
            .unwrap_err();
        assert!(
            error
                .message()
                .contains("typeclass but we expected a value"),
            "{error}"
        );
    }
    for input in [
        "Local.value<Bool>",
        "left.Magma.mul(true, true)",
        "left.Magma.mul<Bool>(true, true)",
    ] {
        let error = env
            .bindings
            .evaluate_value(&project, &Expression::expect_value(input), None)
            .unwrap_err();
        assert!(
            error.message().contains("class bound") || error.message().contains("expected type"),
            "{error}"
        );
    }
    let mut direct = Project::new_mock();
    direct.mock(
        "/mock/dependency.ac",
        "typeclass M: Magma {\n mul: (M, M) -> M\n}",
    );
    direct.mock("/mock/main.ac", "from dependency import Magma");
    assert!(direct
        .errors()
        .iter()
        .any(|(_, e)| e.message().contains("cannot import typeclasses indirectly")));
}

#[test]
fn bounded_operators_are_admitted_without_asserting_commutativity() {
    let mut env = venticorn::environment::Environment::new_test();
    env.add(
        r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }
            
            // Not true but syntactically valid
            theorem commutative<T: Magma>(a: T, b: T) {
                a * b = b * a
            }
            "#,
    );
}

#[test]
fn static_bounded_attributes_keep_phantom_actuals_and_canonical_owner() {
    use venticorn::acorn_value::AcornValue;
    let mut project = Project::new_mock();
    project.mock("/mock/left.ac", "typeclass F: Flagged {\n flag: Bool\n}");
    project.mock("/mock/right.ac", "typeclass F: Flagged {\n flag: Bool\n}");
    project.mock("/mock/main.ac", "import left\nimport right\ndefine left_flag<F: left.Flagged>(value: F) -> Bool { F.flag }\ndefine right_flag<F: right.Flagged>(value: F) -> Bool { F.flag }\ntheorem goal<F: left.Flagged> { F.flag or not F.flag }");
    let main = project.expect_ok("main");
    let left = project.expect_ok("left");
    let right = project.expect_ok("right");
    let env = project.get_env_by_id(main).unwrap();
    for (name, owner) in [("left_flag", left), ("right_flag", right)] {
        let definition = env.bindings.get_definition(name).unwrap();
        let mut constants = vec![];
        definition.find_constants(
            &|c| c.name.local_name.to_string() == "Flagged.flag",
            &mut constants,
        );
        assert_eq!(constants.len(), 1);
        let c = &constants[0];
        assert_eq!(c.name.module_id, owner);
        assert_eq!(c.params.len(), 1);
        let AcornType::Variable(param) = &c.params[0] else {
            panic!("{c:?}")
        };
        assert_eq!(param.name, "F");
        assert_eq!(param.typeclass.as_ref().unwrap().module_id, owner);
        let AcornType::Function(function) = definition.get_type() else {
            panic!()
        };
        assert_eq!(function.applied_type(1), AcornType::Bool);
    }
    let node = env.get_node_by_name("goal");
    let scope = &node.current().block.as_ref().unwrap().env.bindings;
    let value = scope
        .evaluate_value(&project, &Expression::expect_value("F.flag"), None)
        .unwrap();
    let AcornValue::Constant(c) = &value else {
        panic!()
    };
    assert_eq!(c.params.len(), 1);
    assert!(
        matches!(&c.params[0], AcornType::Arbitrary(param) if param.typeclass.as_ref().unwrap().module_id == left)
    );
    let code = scope.value_to_code(&value).unwrap();
    assert_eq!(code, "left.Flagged.flag<F>");
    assert_eq!(
        scope
            .evaluate_value(&project, &Expression::expect_value(&code), None)
            .unwrap(),
        value
    );
    for bad in ["F.missing", "F.flag<Bool>", "right.Flagged.flag<F>"] {
        assert!(
            scope
                .evaluate_value(&project, &Expression::expect_value(bad), None)
                .is_err(),
            "{bad}"
        );
    }
    let mut unbounded = Environment::new_test();
    unbounded.bad("define bad<T>(value: T) -> Bool { T.flag }");
}
