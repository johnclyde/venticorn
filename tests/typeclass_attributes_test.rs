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
        AcornType::Variable("T".into(), None),
        AcornType::Arbitrary("T".into(), None),
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
        AcornType::Variable("T".into(), Some(class.clone())),
        AcornType::Arbitrary("T".into(), Some(class.clone())),
    ] {
        let mut stack = Stack::new();
        stack.insert("value".into(), parameter);
        for (input, expected) in [
            ("value.absent", "unknown attribute 'Magma.absent'"),
            (
                "value.mul",
                "typeclass member specialization is not supported yet",
            ),
        ] {
            let error = env
                .bindings
                .evaluate_value_with_stack(
                    &mut stack,
                    &Project::new_mock(),
                    &Expression::expect_value(input),
                    None,
                )
                .unwrap_err();
            assert_eq!(error.message(), expected);
        }
    }
    let mut stack = Stack::new();
    stack.insert(
        "value".into(),
        AcornType::Arbitrary(
            "T".into(),
            Some(Typeclass {
                module_id: env.module_id + 1,
                name: "Magma".into(),
            }),
        ),
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
