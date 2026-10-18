use tower_lsp::lsp_types::{Position, Range};
use venticorn::acorn_type::{AcornType, Typeclass};
use venticorn::environment::Environment;
use venticorn::project::Project;
use venticorn::prover::Outcome;
use venticorn::statement::Statement;

const SINGLETON: &str = "typeclass S: Singleton {\n value: S\n unique(x: S) { x = S.value }\n}";

fn search(source: &str, shallow: bool) -> Vec<Outcome> {
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", source);
    let module = project.expect_ok("main");
    let env = project.get_env_by_id(module).unwrap();
    let expected_goals = env.iter_goals().count();
    assert!(expected_goals > 0);
    let mut outcomes = vec![];
    // Use the shared per-goal entry rather than inventing a separate membership policy.
    project.for_each_prover_slow(env, &mut |mut prover, _| {
        let outcome = if shallow {
            prover.quick_verification_search()
        } else {
            prover.quick_search()
        };
        assert!(
            !matches!(outcome, Outcome::Error(_)),
            "{:?}",
            prover.error()
        );
        outcomes.push(outcome);
        true
    });
    assert_eq!(outcomes.len(), expected_goals);
    outcomes
}

fn reject_false(source: &str) {
    assert!(search(source, false).iter().all(|outcome| matches!(
        outcome,
        Outcome::Exhausted | Outcome::Timeout | Outcome::Constrained
    )));
    assert!(search(source, true)
        .iter()
        .all(|outcome| *outcome == Outcome::Exhausted));
}

#[test]
fn generic_conditions_retain_the_bound_source_and_callable_metadata() {
    let mut env = Environment::new_test();
    env.add(SINGLETON);
    let class = Typeclass {
        module_id: env.module_id,
        name: "Singleton".into(),
    };
    let info = env.bindings.get_typeclass_info(&class).unwrap();
    assert_eq!(info.instance_param.typeclass.as_ref(), Some(&class));
    assert_eq!(
        info.attributes
            .keys()
            .map(String::as_str)
            .collect::<Vec<_>>(),
        ["value"]
    );
    assert_eq!(
        info.conditions
            .keys()
            .map(String::as_str)
            .collect::<Vec<_>>(),
        ["unique"]
    );
    let condition = &info.conditions["unique"];
    assert_eq!(
        condition.range,
        Range::new(Position::new(2, 1), Position::new(2, 27))
    );
    condition.claim.validate().unwrap();
    condition.definition.validate().unwrap();
    assert!(condition.claim.is_generic());
    assert!(!condition.claim.has_arbitrary());
    let AcornType::Function(function) = condition.definition.get_type() else {
        panic!()
    };
    assert_eq!(
        function.arg_types,
        [AcornType::Variable(info.instance_param.clone())]
    );
    assert_eq!(*function.return_type, AcornType::Bool);
    let mut members = vec![];
    condition.claim.find_constants(
        &|c| c.name.local_name.to_string() == "Singleton.value",
        &mut members,
    );
    assert_eq!(members.len(), 1);
    assert_eq!(members[0].name.module_id, env.module_id);
    assert_eq!(
        members[0].params,
        [AcornType::Variable(info.instance_param.clone())]
    );
    assert_eq!(env.nodes.len(), 1);
    assert!(env.nodes[0].is_structural());
    assert_eq!(env.nodes[0].claim.value, condition.claim);
    assert_eq!(env.nodes[0].claim.source.range, condition.range);
    assert!(env.iter_goals().next().is_none());
    assert!(!env.bindings.name_in_use("S"));
    assert_eq!(
        env.bindings.get_params("Singleton.unique"),
        [info.instance_param.clone()]
    );
    assert_eq!(
        env.bindings.get_definition("Singleton.unique"),
        Some(&condition.definition)
    );
    assert!(env.bindings.is_theorem("Singleton.unique"));
}

#[test]
fn generic_law_facts_prove_bounded_claims_without_proving_their_negation() {
    let positive = format!("{SINGLETON}\ntheorem goal<T: Singleton>(a: T) {{ a = T.value }}");
    assert_eq!(search(&positive, false), [Outcome::Success]);
    assert_eq!(search(&positive, true), [Outcome::Success]);
    reject_false(&format!(
        "{SINGLETON}\ntheorem goal<T: Singleton>(a: T) {{ a != T.value }}"
    ));
}

#[test]
fn invalid_conditions_roll_back_all_members_facts_ranges_and_class_identity() {
    for (body, message) in [
        (
            "unique(x: S) { x = S.value }\n bad(x: S) { x }",
            "expected type Bool",
        ),
        (
            "unique(x: S) { x = S.value }\n unique(x: S) { x = x }",
            "member already defined",
        ),
        ("value(x: S) { x = x }", "member already defined"),
        (
            "unique(x: S) { x = S.value }\n closed { false }",
            "must occur in the exported proposition",
        ),
        (
            "unique(x: S) { x = S.value }\n closed { always<S> }",
            "must occur in the exported proposition",
        ),
        (
            "unique(x: S) { x = S.value }\n captured(x: Outer) { x = x }",
            "cannot capture an outer arbitrary type",
        ),
        (
            "unique(x: S) { x = S.value }\n absent { axiom }",
            "conditions must have values",
        ),
    ] {
        let mut env = Environment::new_test();
        env.add("let kept: Bool = true\ntheorem always<T> { true }");
        env.bindings.add_arbitrary_type("Outer");
        let nodes = env.nodes.len();
        let line = env.last_line();
        let source = format!("typeclass S: Singleton {{\n value: S\n {body}\n}}");
        let error = env
            .add_statement(
                &mut Project::new_mock(),
                &Statement::parse_str(&source).unwrap(),
            )
            .unwrap_err();
        assert!(error.message().contains(message), "{source}: {error}");
        assert!(error.range().start.line >= 2);
        assert_eq!(env.nodes.len(), nodes);
        assert_eq!(env.last_line(), line);
        assert!(!env.includes_explicit_false);
        for name in [
            "S",
            "Singleton",
            "Singleton.value",
            "Singleton.unique",
            "Singleton.closed",
        ] {
            assert!(!env.bindings.name_in_use(name), "{name}");
        }
        assert!(env.bindings.has_identifier("kept"));
        assert!(env
            .bindings
            .get_typeclass_info(&Typeclass {
                module_id: env.module_id,
                name: "Singleton".into()
            })
            .is_none());
        env.add(SINGLETON);
        assert_eq!(env.nodes.len(), nodes + 1);
    }
}

#[test]
fn argument_free_bounded_and_condition_only_classes_keep_their_actual_metadata() {
    let mut env = Environment::new_test();
    env.add("typeclass F: Flagged {\n flag: Bool\n enabled { F.flag }\n}\ntypeclass T: Identity {\n reflexive(x: T) { x = x }\n}");
    let flagged = env.bindings.get_typeclass_for_name("Flagged").unwrap();
    let info = env.bindings.get_typeclass_info(flagged).unwrap();
    assert!(info.conditions["enabled"].claim.has_type_variable("F"));
    assert_eq!(
        info.conditions["enabled"].definition.get_type(),
        AcornType::Bool
    );
    let identity = env.bindings.get_typeclass_for_name("Identity").unwrap();
    let info = env.bindings.get_typeclass_info(identity).unwrap();
    assert!(info.attributes.is_empty());
    assert_eq!(info.conditions.len(), 1);
    assert_eq!(env.nodes.len(), 2);
    assert!(env.iter_goals().next().is_none());
    // A hypothetical class with no possible instance cannot become an unconditional axiom.
    reject_false(
        "typeclass T: Impossible {\n impossible(x: T) { false }\n}\ntheorem goal { false }",
    );
}

#[test]
fn law_bearing_instances_create_a_real_obligation_before_membership_is_usable() {
    let mut env = Environment::new_test();
    env.add(&format!("{SINGLETON}\ninductive State {{\n clean\n}}"));
    env.add("instance State: Singleton {\n let value: State = State.clean\n}");
    assert_eq!(env.iter_goals().count(), 1);
    let class = env.bindings.get_typeclass_for_name("Singleton").unwrap();
    assert!(env
        .bindings
        .proof_scope()
        .has_membership(env.module_id, "State", class));
    let node = env.iter_goals().next().unwrap();
    let block = node.current().block().unwrap();
    assert!(!block
        .entry_scope()
        .has_membership(env.module_id, "State", class));
    assert!(!block
        .env
        .bindings
        .proof_scope()
        .has_membership(env.module_id, "State", class));
    assert_eq!(
        node.current().claim.value,
        venticorn::acorn_value::AcornValue::Bool(true)
    );
    assert!(!block.goal.as_ref().unwrap().value().is_generic());
    // A law-free declaration still adds no obligation of its own.
    env.add("typeclass T: Pointed {\n value: T\n}\ninstance State: Pointed {\n let value: State = State.clean\n}");
    assert_eq!(env.iter_goals().count(), 1);
}

#[test]
fn imported_same_named_classes_keep_distinct_canonical_law_metadata() {
    let mut project = Project::new_mock();
    for module in ["left", "right"] {
        project.mock(&format!("/mock/{module}.ac"), SINGLETON);
    }
    project.mock(
        "/mock/main.ac",
        "import left\nimport right\ninductive State {\n clean\n}",
    );
    let id = project.expect_ok("main");
    let classes: Vec<_> = ["left", "right"]
        .into_iter()
        .map(|module| {
            let id = project.expect_ok(module);
            let env = project.get_env_by_id(id).unwrap();
            let class = env
                .bindings
                .get_typeclass_for_name("Singleton")
                .unwrap()
                .clone();
            let info = env.bindings.get_typeclass_info(&class).unwrap();
            assert_eq!(info.instance_param.typeclass.as_ref(), Some(&class));
            assert_eq!(info.conditions.len(), 1);
            class
        })
        .collect();
    assert_ne!(classes[0], classes[1]);
    // Each fresh consumer lowers only its declared owner's conditions.
    for (owner, class) in ["left", "right"].into_iter().zip(&classes) {
        let mut env = project.get_env_by_id(id).unwrap().child(0, false);
        env.top_level = true;
        env.add_statement(
            &mut project,
            &Statement::parse_str(&format!(
                "instance State: {owner}.Singleton {{\n let value: State = State.clean\n}}"
            ))
            .unwrap(),
        )
        .unwrap();
        assert_eq!(env.iter_goals().count(), 1);
        let block = env.iter_goals().next().unwrap().current().block().unwrap();
        assert!(!block.entry_scope().has_membership(id, "State", class));
        assert!(env
            .bindings
            .proof_scope()
            .has_membership(id, "State", class));
        let mut references = vec![];
        block.goal.as_ref().unwrap().value().find_constants(
            &|constant| {
                constant.name.module_id == class.module_id
                    && constant.name.local_name.to_string() == "Singleton.value"
            },
            &mut references,
        );
        assert!(
            references.is_empty(),
            "the selected class member must be lowered"
        );
    }
}
