use venticorn::acorn_type::AcornType;
use venticorn::fact::Fact;
use venticorn::project::Project;
use venticorn::proof_step::Truthiness;
use venticorn::proposition::SourceType;
use venticorn::prover::{Outcome, Prover};

#[test]
fn declaration_roles_and_lexical_nesting_define_source_importability() {
    let source = "typeclass T: Marked {\n flag: Bool\n reflexive(x: T) { x = x }\n}\ntype Item: axiom\ninstance Item: Marked {\n let flag: Bool = true\n} by { true }\ninductive Choice {\n one\n two\n three\n}\naxiom { true }\ntheorem { true }\naxiom named { true }\nif true { true }\ntheorem outer { true } by {\n define inner<T>(x: T) -> T { x }\n theorem local { true }\n true\n}";
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", source);
    let module = project.expect_ok("main");
    let env = project.get_env_by_id(module).unwrap();
    let mut seen = [false; 7];
    for node in &env.nodes {
        let source = &node.proposition().unwrap().source;
        match &source.source_type {
            SourceType::Anonymous => {
                seen[0] = true;
                assert!(!source.importable);
            }
            SourceType::Theorem(None) => {
                seen[1] = true;
                assert!(source.importable);
            }
            SourceType::Axiom(None) => {
                seen[2] = true;
                assert!(source.importable);
            }
            SourceType::Instance(_, _) => {
                seen[3] = true;
                assert!(source.importable);
            }
            SourceType::TypeDefinition(_, _) => {
                seen[4] = true;
                assert!(source.importable);
            }
            SourceType::Axiom(Some(name)) if name == "Marked.reflexive" => {
                seen[5] = true;
                assert!(source.importable);
            }
            SourceType::Axiom(Some(name)) if name == "named" => {
                seen[6] = true;
                assert!(source.importable);
            }
            _ => assert!(source.importable),
        }
    }
    assert!(seen.into_iter().all(|value| value));
    let outer = env.get_node_by_name("outer");
    let children = &outer.current().block().unwrap().env.nodes;
    assert!(!children.is_empty());
    assert!(children
        .iter()
        .all(|node| !node.proposition().unwrap().source.importable));
    let definition = children
        .iter()
        .find(|node| node.proposition().unwrap().source.fact_name().as_deref() == Some("inner"))
        .unwrap();
    let fact = Fact::new(
        definition.proposition().unwrap().clone(),
        Truthiness::Hypothetical,
    );
    let specialized = fact.instantiate(&[("T".into(), AcornType::Bool)]);
    assert!(!specialized.as_proposition().unwrap().source.importable);
    assert_eq!(
        specialized.as_proposition().unwrap().source.range,
        fact.as_proposition().unwrap().source.range
    );
    assert_eq!(
        specialized
            .as_proposition()
            .unwrap()
            .source
            .qualified_fact_name(),
        fact.as_proposition().unwrap().source.qualified_fact_name()
    );
}

#[test]
fn local_claims_remain_proof_inputs_but_do_not_become_reusable_hints() {
    let mut project = Project::new_mock();
    project.mock(
        "/mock/main.ac",
        "let p: Bool = axiom\nif true { p }\ntheorem goal { p }",
    );
    let module = project.expect_ok("main");
    let env = project.get_env_by_id(module).unwrap();
    let node = env.get_node_by_name("goal");
    let mut prover = project.prover_for_node(&node, false);
    prover.set_goal(&node.goal_context().unwrap());
    assert_eq!(prover.verification_search(), Outcome::Success);
    assert_eq!(prover.get_useful_fact_names(), Some(Default::default()));
}

#[test]
fn anonymous_theorem_declarations_remain_importable_hint_sources() {
    let mut project = Project::new_mock();
    project.mock(
        "/mock/main.ac",
        "let p: Bool = axiom\naxiom { p }\ntheorem goal { p }",
    );
    let module = project.expect_ok("main");
    let env = project.get_env_by_id(module).unwrap();
    let node = env.get_node_by_name("goal");
    let mut prover = project.prover_for_node(&node, false);
    prover.set_goal(&node.goal_context().unwrap());
    assert_eq!(prover.verification_search(), Outcome::Success);
    assert_eq!(
        prover.get_useful_fact_names(),
        Some([(module, "2".into())].into_iter().collect())
    );
    // Importability never overrides the independent hypothetical-source guard.
    let mut hypothetical =
        Prover::with_scope(&project, false, node.goal_context().unwrap().proof_scope);
    let axiom = env
        .nodes
        .iter()
        .find(|node| {
            matches!(
                node.proposition().unwrap().source.source_type,
                SourceType::Axiom(None)
            )
        })
        .unwrap();
    hypothetical.add_fact(Fact::new(
        axiom.proposition().unwrap().clone(),
        Truthiness::Hypothetical,
    ));
    hypothetical.set_goal(&node.goal_context().unwrap());
    assert_eq!(hypothetical.verification_search(), Outcome::Success);
    assert_eq!(
        hypothetical.get_useful_fact_names(),
        Some(Default::default())
    );
}

#[test]
fn witness_conditions_follow_the_declaration_scope_without_changing_obligations() {
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", "let chosen: Bool satisfy { chosen }\ntheorem goal { chosen } by {\n let local: Bool satisfy { local }\n local\n}");
    let module = project.expect_ok("main");
    let env = project.get_env_by_id(module).unwrap();
    let witness: Vec<_> = env
        .nodes
        .iter()
        .filter(|n| {
            matches!(
                n.proposition().unwrap().source.source_type,
                SourceType::Anonymous
            )
        })
        .collect();
    assert_eq!(witness.len(), 2);
    assert!(!witness[0].proposition().unwrap().source.importable);
    assert!(witness[1].proposition().unwrap().source.importable);
    assert_eq!(
        witness[0].proposition().unwrap().source.range,
        witness[1].proposition().unwrap().source.range
    );
    let goal = env.get_node_by_name("goal");
    let children = &goal.current().block().unwrap().env.nodes;
    assert_eq!(
        children
            .iter()
            .filter(|n| matches!(
                n.proposition().unwrap().source.source_type,
                SourceType::Anonymous
            ))
            .count(),
        3
    );
    assert!(children
        .iter()
        .all(|n| !n.proposition().unwrap().source.importable));
    let goals: Vec<_> = env.iter_goals().collect();
    assert_eq!(goals.len(), 4);
    for node in goals {
        let mut prover = project.prover_for_node(&node, false);
        prover.set_goal(&node.goal_context().unwrap());
        assert_eq!(prover.verification_search(), Outcome::Success);
    }
}
