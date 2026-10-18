use venticorn::environment::Environment;
use venticorn::proposition::SourceType;

#[test]
fn every_instance_has_a_node_without_changing_real_obligations() {
    for (law, proof, count, structural) in [
        ("", "", 0, true),
        ("", " by {\n true\n}", 2, false),
        (" law(x: T) { x = x }\n", "", 1, false),
    ] {
        let source = format!("inductive Unit {{\n only\n}}\ntypeclass T: Marked {{\n flag: Bool\n{law}}}\ninstance Unit: Marked {{\n let flag: Bool = true\n}}{proof}");
        let mut env = Environment::new_test();
        env.add(&source);
        assert_eq!(env.iter_goals().count(), count);
        let instances = env
            .nodes
            .iter()
            .filter(|node| {
                node.source().is_some_and(|source| {
                    matches!(
                        &source.source_type,
                        SourceType::Instance(name, class) if name == "Unit" && class == "Marked"
                    )
                })
            })
            .collect::<Vec<_>>();
        assert_eq!(instances.len(), 1);
        let node = instances[0];
        assert_eq!(node.is_structural(), structural);
        assert_eq!(node.get_block().is_none(), structural);
        assert!(node.proposition().is_none());
        assert_eq!(node.fact_name().as_deref(), Some("Unit.instance.Marked"));
        assert!(node.importable());
        let class = env.bindings.get_typeclass_for_name("Marked").unwrap();
        assert!(!node
            .proof_scope()
            .has_membership(env.module_id, "Unit", class));
        assert!(env
            .bindings
            .proof_scope()
            .has_membership(env.module_id, "Unit", class));
    }
}

#[test]
fn extracted_instance_relations_preserve_source_without_granting_authority() {
    use venticorn::fact::Fact;
    use venticorn::project::Project;
    use venticorn::prover::Outcome;

    let mut project = Project::new_mock();
    project.mock("/mock/owner.ac", "typeclass T: Marked {\n flag: Bool\n reflexive(x: T) { x = x }\n}\ninductive Unit {\n only\n}\ninstance Unit: Marked {\n let flag: Bool = true\n}");
    project.mock("/mock/main.ac", "import owner\ntheorem goal { true }");
    let module = project.expect_ok("main");
    let owner = project.expect_ok("owner");
    let env = project.get_env_by_id(owner).unwrap();
    assert_eq!(env.iter_goals().count(), 1);
    let node = env
        .nodes
        .iter()
        .find(|node| {
            matches!(
                node.source().map(|s| &s.source_type),
                Some(SourceType::Instance(..))
            )
        })
        .unwrap();
    let fact = node.get_fact().unwrap();
    assert!(fact.is_instance());
    assert!(fact.as_proposition().is_none());
    assert!(fact.truthiness().is_none());
    assert_eq!(fact.source(), node.source().unwrap());
    let Fact::Instance(data, class, source) = &fact else {
        panic!("expected relation")
    };
    assert_eq!(data.module_id, owner);
    assert_eq!(class.module_id, owner);
    assert_eq!(source.module, owner);
    assert_eq!(source.depth, 0);
    assert!(source.importable);
    assert!(!node.proof_scope().has_class_membership(data, class));
    let goal = project
        .get_env_by_id(module)
        .unwrap()
        .get_node_by_name("goal");
    let relations = goal
        .usable_facts(&project)
        .into_iter()
        .filter(Fact::is_instance)
        .collect::<Vec<_>>();
    assert_eq!(relations.len(), 1);
    assert_eq!(relations[0].source(), source);
    assert!(goal.goal_scope().has_class_membership(data, class));
    for env in [env, project.get_env_by_id(module).unwrap()] {
        let goals = env.iter_goals().collect::<Vec<_>>();
        assert_eq!(goals.len(), 1);
        for goal in goals {
            let mut prover = project.prover_for_node(&goal, false);
            prover.set_goal(&goal.goal_context().unwrap());
            let mut shallow = prover.clone();
            assert_eq!(prover.quick_search(), Outcome::Success);
            assert_eq!(shallow.quick_verification_search(), Outcome::Success);
        }
    }
}
