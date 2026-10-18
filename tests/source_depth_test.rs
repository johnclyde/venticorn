use tower_lsp::lsp_types::Range;
use venticorn::acorn_value::AcornValue;
use venticorn::environment::Environment;
use venticorn::goal::Goal;
use venticorn::project::Project;
use venticorn::proposition::{Proposition, SourceType};

fn check_node_depths(env: &Environment, expected: u32) -> usize {
    assert_eq!(env.depth, expected);
    let mut total = 0;
    for node in &env.nodes {
        total += 1;
        assert_eq!(node.claim.source.depth, expected);
        if let Some(block) = &node.block {
            total += check_node_depths(&block.env, expected + 1);
        }
    }
    total
}

#[test]
fn lexical_depth_survives_same_scope_staging_and_real_children() {
    let source = "typeclass T: Marked {\n flag: Bool\n reflexive(x: T) { x = x }\n}\ntype Item: axiom\ninstance Item: Marked {\n let flag: Bool = true\n} by { true }\naxiom named { true }\naxiom { true }\ntheorem outer { true } by {\n theorem inner { true } by { true }\n if true { true }\n true\n}";
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", source);
    let module = project.expect_ok("main");
    let env = project.get_env_by_id(module).unwrap();
    assert!(check_node_depths(env, 0) > env.nodes.len());
    let condition = env
        .nodes
        .iter()
        .find(|n| {
            matches!(&n.claim.source.source_type,
        SourceType::Axiom(Some(name)) if name == "Marked.reflexive")
        })
        .unwrap();
    assert_eq!(condition.claim.source.depth, 0);
    assert!(condition.claim.source.importable);
    let instance = env
        .nodes
        .iter()
        .find(|n| {
            matches!(&n.claim.source.source_type,
        SourceType::Instance(name, class) if name == "Item" && class == "Marked")
        })
        .unwrap();
    let instance_block = instance.block.as_ref().unwrap();
    assert_eq!(instance_block.env.depth, 1);
    let Some(Goal::Prove(instance_goal)) = &instance_block.goal else {
        panic!("real instance obligation")
    };
    assert_eq!(instance_goal.source.depth, 0);
    assert_ne!(instance_goal.value, AcornValue::Bool(true));
    let outer = env.get_node_by_name("outer");
    let block = outer.current().block.as_ref().unwrap();
    let Some(Goal::Prove(goal)) = &block.goal else {
        panic!("theorem goal")
    };
    assert_eq!(goal.source.depth, 1);
    let inner = block
        .env
        .nodes
        .iter()
        .find(|n| n.claim.theorem_name() == Some("inner"))
        .unwrap();
    let inner = inner.block.as_ref().unwrap();
    let Some(Goal::Prove(goal)) = &inner.goal else {
        panic!("nested theorem goal")
    };
    assert_eq!(goal.source.depth, 2);
    assert!(block.env.nodes.iter().all(|n| !n.claim.source.importable));
}

#[test]
fn value_and_source_transforms_preserve_depth_and_visibility() {
    let original =
        Proposition::anonymous(AcornValue::Bool(true), 7, Range::default()).with_depth(4);
    let replaced = original.with_value(AcornValue::Bool(false));
    let specialized = original.instantiate(&[]);
    for transformed in [replaced, specialized] {
        assert_eq!(transformed.source, original.source);
        assert_eq!(transformed.source.depth, 4);
        assert!(!transformed.source.importable);
    }
    let negated = original.with_negated_goal(AcornValue::Bool(false));
    assert_eq!(negated.source.depth, 4);
    assert_eq!(negated.source.module, original.source.module);
    assert_eq!(negated.source.range, original.source.range);
    assert!(!negated.source.importable);
    assert!(matches!(
        negated.source.source_type,
        SourceType::NegatedGoal
    ));
}

#[test]
fn lexical_role_does_not_rewrite_explicit_compatibility_fact_roles() {
    use venticorn::fact::Fact;
    use venticorn::proof_step::Truthiness;
    let prop = Proposition::anonymous(AcornValue::Bool(true), 7, Range::default());
    assert_eq!(prop.truthiness(), Truthiness::Factual);
    assert_eq!(
        prop.clone().with_depth(2).truthiness(),
        Truthiness::Hypothetical
    );
    assert_eq!(
        prop.with_negated_goal(AcornValue::Bool(false)).truthiness(),
        Truthiness::Counterfactual
    );
    let fact = Fact::new(prop.clone(), Truthiness::Hypothetical);
    assert_eq!(fact.truthiness(), Some(Truthiness::Hypothetical));
    assert_eq!(fact.as_proposition().unwrap().source, prop.source);
}
