// Modified for Venticorn: theorem expansion preserves surrounding binder identities.
use venticorn::project::Project;
use venticorn::prover::{Outcome, Prover};

fn outcomes(source: &str) -> Vec<Outcome> {
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
fn ordinary_theorem_expansion_preserves_heterogeneous_nested_binders() {
    let declarations = r#"
        type Item: axiom
        theorem reflexive(flag: Bool) { flag = flag }
        theorem wrapped(flag: Bool) { reflexive(flag) }
    "#;
    let proof = "by { (forall(item: Item) { forall(flag: Bool) { wrapped(flag) } }) }";
    let source = format!("{declarations}\ntheorem goal {{ forall(item: Item) {{ forall(flag: Bool) {{ flag = flag }} }} }} {proof}");
    assert_eq!(outcomes(&source), vec![Outcome::Success; 3]);
    let false_source = format!("{declarations}\ntheorem goal {{ true = false }} {proof}");
    assert_eq!(
        outcomes(&false_source),
        vec![Outcome::Success, Outcome::Success, Outcome::Exhausted]
    );
}
#[test]
fn generic_block_goals_bind_types_before_values() {
    let positive = r#"
        define identity<T>(value: T) -> T { value }
        theorem lifted<T>(outer: T) {
            forall(inner: Bool) { identity(outer) = outer and inner = inner }
        }
    "#;
    assert_eq!(outcomes(positive), vec![Outcome::Success]);
    let negative = r#"
        define identity<T>(value: T) -> T { value }
        theorem rejected<T>(outer: T) {
            forall(inner: Bool) { identity(outer) != outer and inner = inner }
        }
    "#;
    assert_eq!(outcomes(negative), vec![Outcome::Exhausted]);
}

#[test]
fn generic_block_premises_share_the_bound_argument_type() {
    let source = r#"
        define identity<T>(value: T) -> T { value }
        theorem lifted<T>(outer: T) {
            identity(outer) = outer implies forall(inner: Bool) { identity(outer) = outer and inner = inner }
        }
    "#;
    assert_eq!(outcomes(source), vec![Outcome::Success]);
}
