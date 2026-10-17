use venticorn::acorn_type::{AcornType, TypeParam, Typeclass};
use venticorn::acorn_value::{AcornValue, BinaryOp};
use venticorn::clause::Clause;
use venticorn::constant_name::{GlobalConstantName, LocalConstantName};
use venticorn::expression::Expression;
use venticorn::fact::Fact;
use venticorn::literal::Literal;
use venticorn::monomorphizer::Monomorphizer;
use venticorn::normalizer::Normalizer;
use venticorn::project::Project;
use venticorn::proof_step::Truthiness;
use venticorn::proposition::Source;

fn name(class_module: u16) -> GlobalConstantName {
    GlobalConstantName::new(
        10,
        LocalConstantName::instance(
            &Typeclass {
                module_id: class_module,
                name: "Marked".into(),
            },
            "flag",
            "State",
        ),
    )
}

fn value(name: GlobalConstantName, actuals: Vec<AcornType>) -> AcornValue {
    AcornValue::constant_named(name, actuals, AcornType::Bool)
}

#[test]
fn transforms_and_normalization_preserve_canonical_instance_owners() {
    let first = value(name(11), vec![]);
    let second = value(name(12), vec![]);
    assert_eq!(first.to_string(), second.to_string());
    assert_ne!(first, second);
    for local in [false, true] {
        let mut normalizer = Normalizer::new();
        let a = normalizer.term_from_value(&first, local).unwrap();
        let b = normalizer.term_from_value(&second, local).unwrap();
        assert_ne!(a.head, b.head);
        let roundtrip = normalizer.denormalize(&Clause::new(vec![Literal::new(true, a, b)]));
        let AcornValue::Binary(BinaryOp::Equals, a, b) = roundtrip else {
            panic!("expected equality");
        };
        assert!((*a == first && *b == second) || (*a == second && *b == first));
    }
    let variable = AcornType::Variable(TypeParam::unconstrained("T"));
    let generic = value(name(11), vec![variable]);
    let instantiated = generic.instantiate(&[("T".into(), AcornType::Bool)]);
    let AcornValue::Constant(instance) = instantiated else {
        panic!("expected constant");
    };
    assert_eq!(instance.name, name(11));
    assert_eq!(instance.params, [AcornType::Bool]);
    assert_eq!(generic.to_arbitrary().to_generic(), generic);
    let mut normalizer = Normalizer::new();
    assert_ne!(
        normalizer
            .term_from_value(&value(name(11), vec![AcornType::Bool]), false)
            .unwrap()
            .head,
        normalizer
            .term_from_value(&value(name(12), vec![AcornType::Bool]), false)
            .unwrap()
            .head
    );
}

#[test]
fn generic_demand_does_not_cross_same_spelling_class_owners() {
    let mut monomorphizer = Monomorphizer::new();
    let generic = value(
        name(11),
        vec![AcornType::Variable(TypeParam::unconstrained("T"))],
    );
    monomorphizer.add_fact(Fact {
        value: generic,
        source: Source::mock(),
        truthiness: Truthiness::Factual,
    });
    assert!(monomorphizer.take_facts().is_empty());
    monomorphizer.add_monomorphs(&value(name(12), vec![AcornType::Bool]));
    assert!(monomorphizer.take_facts().is_empty());
    let expected = value(name(11), vec![AcornType::Bool]);
    monomorphizer.add_monomorphs(&expected);
    let output = monomorphizer.take_facts();
    assert_eq!(output.len(), 1);
    assert_eq!(output[0].value, expected);
}

#[test]
fn renderer_refuses_wrong_canonical_owner_and_disguised_instance_variants() {
    let mut project = Project::new_mock();
    let class = "typeclass T: Marked {\n flag: Bool\n}";
    project.mock("/mock/left.ac", class);
    project.mock("/mock/right.ac", class);
    project.mock("/mock/owner.ac", "import left\ninductive State {\n only\n}\ninstance State: left.Marked {\n let flag: Bool = true\n}");
    project.mock("/mock/main.ac", "from owner import State\nimport right");
    let main = project.expect_ok("main");
    let owner = project.expect_ok("owner");
    let wrong_class = project.expect_ok("right");
    for id in [owner, main] {
        let bindings = &project.get_env_by_id(id).unwrap().bindings;
        let genuine = bindings
            .evaluate_value(
                &project,
                &Expression::expect_value("State.Marked.flag"),
                None,
            )
            .unwrap();
        let code = bindings.value_to_code(&genuine).unwrap();
        assert_eq!(
            bindings
                .evaluate_value(&project, &Expression::expect_value(&code), None)
                .unwrap(),
            genuine
        );
        let AcornValue::Constant(mut wrong) = genuine.clone() else {
            panic!("expected constant");
        };
        let LocalConstantName::Instance(class, _, _) = &mut wrong.name.local_name else {
            panic!("typed instance required");
        };
        class.module_id = wrong_class;
        if id == owner {
            assert!(bindings
                .get_constant_value_named(&wrong.name.local_name)
                .is_none());
        }
        assert_ne!(AcornValue::Constant(wrong.clone()), genuine);
        if id == owner {
            let mut unknown = std::collections::HashMap::new();
            assert!(bindings
                .find_unknown_local_constants(&AcornValue::Constant(wrong.clone()), &mut unknown)
                .is_err());
            assert!(unknown.is_empty());
        }
        assert!(bindings
            .value_to_code(&AcornValue::Constant(wrong))
            .is_err());
        for fake in [
            LocalConstantName::unqualified("State.Marked.flag"),
            LocalConstantName::attribute("State.Marked", "flag"),
            LocalConstantName::attribute("State", "Marked.flag"),
        ] {
            if id == owner {
                assert!(bindings.get_constant_value_named(&fake).is_none());
            }
            assert!(bindings
                .value_to_code(&value(GlobalConstantName::new(owner, fake), vec![]))
                .is_err());
        }
    }
}

#[test]
fn validated_instance_member_aliases_preserve_their_canonical_target() {
    let mut project = Project::new_mock();
    project.mock("/mock/owner.ac", "typeclass T: Marked {\n value: T\n}\ninductive State {\n clean\n}\ninstance State: Marked {\n let value: State = State.clean\n}\ntheorem goal { State.Marked.value = State.clean }");
    project.mock(
        "/mock/main.ac",
        "from owner import State\ntheorem goal { State.Marked.value = State.clean }",
    );
    for module in ["owner", "main"] {
        let id = project.expect_ok(module);
        let env = project.get_env_by_id(id).unwrap();
        let member = env
            .bindings
            .evaluate_value(
                &project,
                &Expression::expect_value("State.Marked.value"),
                None,
            )
            .unwrap();
        let target = env
            .bindings
            .evaluate_value(&project, &Expression::expect_value("State.clean"), None)
            .unwrap();
        assert_eq!(member, target);
        let goals: Vec<_> = env.iter_goals().collect();
        assert_eq!(goals.len(), 1);
        for node in goals {
            let mut prover = project.prover_for_node(&node, false);
            prover.set_goal(&node.goal_context().unwrap());
            assert_eq!(
                prover.quick_shallow_search(),
                venticorn::prover::Outcome::Success
            );
        }
    }
}
