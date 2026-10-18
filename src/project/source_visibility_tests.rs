use super::*;

fn fixture(local_claim: bool) -> Project {
    let mut project = Project::new_mock();
    project.mock(
        "/mock/dep.ac",
        "let flag: Bool = axiom\nif true { flag }\ntheorem { true }",
    );
    let local = if local_claim {
        "if true { dep.flag }\n"
    } else {
        ""
    };
    project.mock(
        "/mock/main.ac",
        &format!("import dep\n{local}theorem goal {{ dep.flag }}"),
    );
    project.expect_ok("main");
    project
}

#[test]
fn normal_and_guided_imports_exclude_block_claims_but_keep_anonymous_declarations() {
    let project = fixture(false);
    let dependency = project
        .get_env_by_ref(&ModuleRef::Name("dep".into()))
        .unwrap();
    assert!(dependency
        .nodes
        .iter()
        .any(
            |node| node.proposition().source.fact_name().as_deref() == Some("2")
                && !node.proposition().source.importable
        ));
    let exported = dependency.exported_facts();
    assert_eq!(exported.len(), 1);
    assert_eq!(
        exported[0]
            .as_proposition()
            .unwrap()
            .source
            .fact_name()
            .as_deref(),
        Some("3")
    );
    assert!(exported[0].as_proposition().unwrap().source.importable);
    assert!(dependency
        .exported_facts_filtered(Some(&HashSet::from(["2".into()])))
        .is_empty());
    assert_eq!(
        dependency
            .exported_facts_filtered(Some(&HashSet::from(["3".into()])))
            .len(),
        1
    );
    let env = project
        .get_env_by_ref(&ModuleRef::Name("main".into()))
        .unwrap();
    let node = env.get_node_by_name("goal");
    let goal = node.goal_context().unwrap();
    let mut full = project.prover_for_node(&node, false);
    full.set_goal(&goal);
    assert_eq!(full.verification_search(), Outcome::Exhausted);
    let excluded = PremiseSet::from([(
        ModuleRef::Name("dep".into()),
        ["2".into()].into_iter().collect(),
    )]);
    assert!(
        project.make_guided_prover(env, &node, &excluded).is_none(),
        "the direct dependency-node guidance path must not reintroduce excluded exports"
    );
    let mut guided = project
        .make_guided_prover(env, &node, &PremiseSet::new())
        .unwrap();
    guided.set_goal(&goal);
    assert_eq!(guided.verification_search(), Outcome::Exhausted);
}

#[test]
fn guidance_keeps_non_importable_current_module_claims_without_hint_names() {
    let project = fixture(true);
    let env = project
        .get_env_by_ref(&ModuleRef::Name("main".into()))
        .unwrap();
    let node = env.get_node_by_name("goal");
    let goal = node.goal_context().unwrap();
    let mut full = project.prover_for_node(&node, false);
    full.set_goal(&goal);
    assert_eq!(full.verification_search(), Outcome::Success);
    let mut guided = project
        .make_guided_prover(env, &node, &PremiseSet::new())
        .unwrap();
    guided.set_goal(&goal);
    assert_eq!(guided.verification_search(), Outcome::Success);
    assert_eq!(guided.get_useful_fact_names(), Some(Default::default()));
}

fn witness_project(claim: &str) -> Project {
    let mut project = Project::new_mock();
    project.mock(
        "/mock/owner.ac",
        "type Item: axiom\nlet a: Item = axiom\nlet w: Item satisfy { w = a }",
    );
    project.mock(
        "/mock/main.ac",
        &format!("import owner\ntheorem goal {{ {claim} }}"),
    );
    project.expect_ok("main");
    project
}

#[test]
fn chosen_witness_exports_its_condition_after_a_real_existence_obligation() {
    let project = witness_project("owner.w = owner.a");
    let owner = project
        .get_env_by_ref(&ModuleRef::Name("owner".into()))
        .unwrap();
    let obligations = owner.iter_goals().collect::<Vec<_>>();
    assert_eq!(obligations.len(), 1);
    assert!(!obligations[0].current().proposition().source.importable);
    let exported = owner.exported_facts();
    assert_eq!(exported.len(), 1);
    assert!(exported[0].as_proposition().unwrap().source.importable);
    assert_eq!(
        exported[0]
            .as_proposition()
            .unwrap()
            .source
            .fact_name()
            .as_deref(),
        Some("3")
    );
    assert_eq!(
        exported[0].as_proposition().unwrap().source.range,
        obligations[0].current().proposition().source.range
    );
    assert_ne!(
        exported[0].as_proposition().unwrap().value,
        obligations[0].current().proposition().value
    );
    assert_eq!(
        owner
            .exported_facts_filtered(Some(&HashSet::from(["3".into()])))
            .len(),
        1,
        "the shared line name must select only the exported specific condition"
    );
    let env = project
        .get_env_by_ref(&ModuleRef::Name("main".into()))
        .unwrap();
    assert_eq!(env.iter_goals().count(), 1);
    let node = env.get_node_by_name("goal");
    for selected in [&obligations[0], &node] {
        for shallow in [false, true] {
            let mut prover = project.prover_for_node(selected, false);
            prover.set_goal(&selected.goal_context().unwrap());
            assert_eq!(
                if shallow {
                    prover.quick_shallow_search()
                } else {
                    prover.verification_search()
                },
                Outcome::Success,
                "{:?}",
                prover.error()
            );
        }
    }
    let premises = PremiseSet::from([(
        ModuleRef::Name("owner".into()),
        ["3".into()].into_iter().collect(),
    )]);
    let mut guided = project.make_guided_prover(env, &node, &premises).unwrap();
    guided.set_goal(&node.goal_context().unwrap());
    assert_eq!(guided.verification_search(), Outcome::Success);
    assert_eq!(
        guided.get_useful_fact_names(),
        Some([(owner.module_id, "3".into())].into_iter().collect())
    );
    let report = project.sync_build_report();
    assert_eq!(report.status, BuildStatus::Good);
    assert_eq!(report.goals_total, 2);
    assert_eq!(report.num_success, 2);
}

#[test]
fn exported_witness_condition_cannot_prove_a_false_importer_claim() {
    let project = witness_project("owner.w != owner.a");
    let env = project
        .get_env_by_ref(&ModuleRef::Name("main".into()))
        .unwrap();
    let node = env.get_node_by_name("goal");
    let goal = node.goal_context().unwrap();
    for shallow in [false, true] {
        let mut prover = project.prover_for_node(&node, false);
        prover.set_goal(&goal);
        assert_eq!(
            if shallow {
                prover.quick_shallow_search()
            } else {
                prover.verification_search()
            },
            Outcome::Exhausted,
            "{:?}",
            prover.error()
        );
    }
    let premises = PremiseSet::from([(
        ModuleRef::Name("owner".into()),
        ["3".into()].into_iter().collect(),
    )]);
    let mut guided = project.make_guided_prover(env, &node, &premises).unwrap();
    guided.set_goal(&goal);
    assert_eq!(guided.verification_search(), Outcome::Exhausted);
    let report = project.sync_build_report();
    assert_eq!(report.status, BuildStatus::Warning);
    assert_eq!(report.goals_total, 2);
    assert_eq!(report.num_success, 1);
    if let Some(cache) = report.cache {
        assert!(cache.get(&ModuleRef::Name("main".into())).is_none());
    }
}
