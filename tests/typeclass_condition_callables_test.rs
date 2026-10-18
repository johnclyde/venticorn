use venticorn::acorn_type::{AcornType, TypeParam};
use venticorn::acorn_value::AcornValue;
use venticorn::environment::Environment;
use venticorn::expression::Expression;
use venticorn::project::Project;
use venticorn::prover::Outcome;
use venticorn::statement::Statement;

const SINGLETON: &str = "typeclass S: Singleton {\n value: S\n unique(x: S) { x = S.value }\n}";

#[test]
fn callable_laws_support_explicit_generic_reasoning_and_keep_false_controls() {
    for (claim, positive) in [("a = b", true), ("a != b", false)] {
        let mut project = Project::new_mock();
        project.mock("/mock/main.ac", &format!("{SINGLETON}\ntheorem goal<T: Singleton>(a: T, b: T) {{ {claim} }} by {{\n Singleton.unique(a)\n a = T.value\n T.unique(b)\n b = T.value\n}}"));
        let module = project.expect_ok("main");
        let env = project.get_env_by_id(module).unwrap();
        let goal_count = env.iter_goals().count();
        // The named citations are structural; the two explicit equalities and
        // the containing theorem are the three actual obligations.
        assert_eq!(goal_count, 3);
        assert_eq!(
            env.iter_goals()
                .map(|node| {
                    let goal = node.goal_context().unwrap();
                    (goal.first_line, goal.last_line)
                })
                .collect::<Vec<_>>(),
            [(6, 6), (8, 8), (4, 9)]
        );
        let mut count = 0;
        project.for_each_prover_slow(env, &mut |mut prover, goal| {
            let mut shallow = prover.clone();
            let result = prover.quick_search();
            assert!(!matches!(result, Outcome::Error(_)), "{:?}", prover.error());
            let containing_goal = goal.first_line == 4 && goal.last_line == 9;
            assert_eq!(containing_goal, count == 2);
            if positive || !containing_goal {
                assert_eq!(result, Outcome::Success);
                assert_eq!(shallow.quick_verification_search(), Outcome::Success);
            } else {
                assert!(matches!(
                    result,
                    Outcome::Exhausted | Outcome::Timeout | Outcome::Constrained
                ));
                assert_eq!(shallow.quick_verification_search(), Outcome::Exhausted);
            }
            count += 1;
            true
        });
        assert_eq!(count, goal_count);
    }
}

#[test]
fn zero_argument_condition_callables_preserve_phantom_actuals_and_class_ownership() {
    let mut project = Project::new_mock();
    for module in ["left", "right"] {
        project.mock(
            &format!("/mock/{module}.ac"),
            "typeclass F: Flagged {\n flag: Bool\n enabled { F.flag }\n}",
        );
    }
    project.mock("/mock/main.ac", "import left\nimport right");
    let main = project.expect_ok("main");
    let left = project.expect_ok("left");
    let right = project.expect_ok("right");
    let left_class = project
        .get_env_by_id(left)
        .unwrap()
        .bindings
        .get_typeclass_for_name("Flagged")
        .unwrap()
        .clone();
    let right_class = project
        .get_env_by_id(right)
        .unwrap()
        .bindings
        .get_typeclass_for_name("Flagged")
        .unwrap()
        .clone();
    assert_ne!(left_class, right_class);
    let mut env = project.get_env_by_id(main).unwrap().child(0, false);
    let actual = env.bindings.add_arbitrary_type_param(TypeParam {
        name: "F".into(),
        typeclass: Some(left_class.clone()),
    });
    let wrong = env.bindings.add_arbitrary_type_param(TypeParam {
        name: "G".into(),
        typeclass: Some(right_class),
    });
    assert_ne!(actual, wrong);
    let value = env
        .bindings
        .evaluate_value(
            &project,
            &Expression::expect_value("F.enabled"),
            Some(&AcornType::Bool),
        )
        .unwrap();
    let AcornValue::Constant(constant) = &value else {
        panic!()
    };
    assert_eq!(constant.name.module_id, left);
    assert_eq!(constant.name.local_name.to_string(), "Flagged.enabled");
    assert_eq!(constant.params, [actual.clone()]);
    assert_eq!(constant.instance_type, AcornType::Bool);
    let owner = &project.get_env_by_id(left).unwrap().bindings;
    let params = owner.get_params("Flagged.enabled");
    assert_eq!(params.len(), 1);
    assert_eq!(params[0].typeclass.as_ref(), Some(&left_class));
    assert!(owner
        .get_definition("Flagged.enabled")
        .unwrap()
        .has_type_variable(&params[0].name));
    let code = env.bindings.value_to_code(&value).unwrap();
    assert_eq!(
        env.bindings
            .evaluate_value(&project, &Expression::expect_value(&code), None)
            .unwrap(),
        value
    );
    for expression in ["left.Flagged.enabled<Bool>", "left.Flagged.enabled<G>"] {
        let error = env
            .bindings
            .evaluate_value(&project, &Expression::expect_value(expression), None)
            .unwrap_err();
        assert!(error.message().contains("class bound"), "{error}");
    }
}

#[test]
fn callable_conditions_are_atomic_and_do_not_weaken_erased_theorem_rejection() {
    let mut env = Environment::new_test();
    env.add("theorem always<T> { true }");
    let before = env.nodes.len();
    let statement = Statement::parse_str(
        "typeclass S: Singleton {\n value: S\n unique(x: S) { x = S.value }\n bad { always<S> }\n}",
    )
    .unwrap();
    let error = env
        .add_statement(&mut Project::new_mock(), &statement)
        .unwrap_err();
    assert!(
        error
            .message()
            .contains("must occur in the exported proposition"),
        "{error}"
    );
    assert_eq!(env.nodes.len(), before);
    assert!(!env.bindings.is_theorem("Singleton.unique"));
    for name in [
        "S",
        "Singleton",
        "Singleton.value",
        "Singleton.unique",
        "Singleton.bad",
    ] {
        assert!(!env.bindings.name_in_use(name), "{name}");
    }
    env.add(SINGLETON);
    assert!(env.bindings.is_theorem("Singleton.unique"));
    for source in [
        "axiom bad<T: Singleton> { false }",
        "axiom bad<T: Singleton> { always<T> }",
        "theorem bad<T: Singleton> { true } by { forall(x: T) { x = x } }",
    ] {
        let before = env.nodes.len();
        let error = env
            .add_statement(
                &mut Project::new_mock(),
                &Statement::parse_str(source).unwrap(),
            )
            .unwrap_err();
        assert!(
            error
                .message()
                .contains("must occur in the exported proposition"),
            "{error}"
        );
        assert_eq!(env.nodes.len(), before);
        assert!(!env.bindings.name_in_use("bad"));
    }
}

#[test]
fn later_conditions_expand_earlier_callable_laws_without_erasing_the_class_bound() {
    let mut env = Environment::new_test();
    env.add("typeclass S: Singleton {\n value: S\n unique(x: S) { x = S.value }\n again(x: S) { Singleton.unique(x) }\n}");
    let class = env.bindings.get_typeclass_for_name("Singleton").unwrap();
    let info = env.bindings.get_typeclass_info(class).unwrap();
    let condition = &info.conditions["again"];
    assert!(condition.claim.has_type_variable(&info.instance_param.name));
    assert!(!condition.claim.has_arbitrary());
    let mut expanded_calls = vec![];
    condition.claim.find_constants(
        &|c| c.name.local_name.to_string() == "Singleton.unique",
        &mut expanded_calls,
    );
    assert!(expanded_calls.is_empty());
    let mut members = vec![];
    condition.claim.find_constants(
        &|c| c.name.local_name.to_string() == "Singleton.value",
        &mut members,
    );
    assert!(!members.is_empty());
    for member in members {
        assert_eq!(
            member.params,
            [AcornType::Variable(info.instance_param.clone())]
        );
    }
    assert_eq!(
        env.bindings.get_params("Singleton.again"),
        [info.instance_param.clone()]
    );
    assert_eq!(env.nodes.len(), 2);
    assert_eq!(env.nodes[1].proposition().unwrap().value, condition.claim);
}
