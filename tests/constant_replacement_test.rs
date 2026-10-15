// Modified for Venticorn: preserve scope and declaration order during constant replacement.
use venticorn::acorn_type::AcornType;
use venticorn::acorn_value::AcornValue;
use venticorn::project::Project;
use venticorn::prover::{Outcome, Prover};

#[test]
fn recursive_replacement_shifts_closed_definitions_beneath_mixed_binders() {
    let item = AcornType::Data(10, "Item".into(), vec![]);
    let function_type = AcornType::new_functional(vec![AcornType::Bool], AcornType::Bool);
    let inner = AcornValue::new_constant(10, "inner".into(), vec![], function_type.clone());
    let outer = AcornValue::new_constant(10, "outer".into(), vec![], function_type);
    let inner_definition = AcornValue::new_lambda(
        vec![AcornType::Bool],
        AcornValue::Variable(0, AcornType::Bool),
    );
    let outer_definition = AcornValue::new_lambda(
        vec![AcornType::Bool],
        AcornValue::new_apply(inner, vec![AcornValue::Variable(0, AcornType::Bool)]),
    );
    let value = AcornValue::new_forall(
        vec![item],
        AcornValue::new_exists(
            vec![AcornType::Bool],
            AcornValue::new_apply(outer, vec![AcornValue::Variable(1, AcornType::Bool)]),
        ),
    );
    let replaced = value.replace_constants(0, &|c, depth| match c.name.as_str() {
        "outer" => Some(outer_definition.clone().insert_stack(0, depth)),
        "inner" => Some(inner_definition.clone().insert_stack(0, depth)),
        _ => None,
    });
    replaced.validate().unwrap();
    let expanded = replaced.expand_lambdas(0);
    expanded.validate().unwrap();
    assert!(!expanded.to_string().contains("inner"));
    assert!(!expanded.to_string().contains("outer"));
}

fn prove(source: &str) -> Vec<Outcome> {
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", source);
    let id = project.expect_ok("main");
    let env = project.get_env_by_id(id).unwrap();
    env.iter_goals()
        .map(|node| {
            let context = node.goal_context().unwrap();
            context.goal.value().validate().unwrap();
            let mut prover = Prover::new(&project, false);
            for fact in node.usable_facts(&project) {
                fact.value.validate().unwrap();
                prover.add_fact(fact);
            }
            prover.set_goal(&context);
            prover.quick_verification_search()
        })
        .collect()
}

#[test]
fn generic_theorem_expansion_preserves_distinct_outer_binders() {
    let declarations = r#"
        type Item: axiom
        theorem reflexive<T>(value: T) { value = value }
        theorem wrapper(value: Bool) { reflexive(value) }
    "#;
    let proof =
        "by { (forall(item: Item) { forall(flag: Bool) { wrapper(flag) and reflexive(item) } }) }";
    let source =
        format!("{declarations}\ntheorem goal {{ forall(item: Item) {{ item = item }} }} {proof}");
    let outcomes = prove(&source);
    assert!(!outcomes.is_empty());
    assert!(outcomes.iter().all(|outcome| *outcome == Outcome::Success));
    let false_source = format!("{declarations}\ntheorem goal {{ true = false }} {proof}");
    let outcomes = prove(&false_source);
    assert_eq!(outcomes.last(), Some(&Outcome::Exhausted));
    assert!(outcomes[..outcomes.len() - 1]
        .iter()
        .all(|outcome| *outcome == Outcome::Success));
}
