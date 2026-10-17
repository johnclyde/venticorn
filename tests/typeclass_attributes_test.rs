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
