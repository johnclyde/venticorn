// Modified for Venticorn: retain type and binder identity when generic constants are instantiated.
use venticorn::project::Project;
use venticorn::prover::{Outcome, Prover};

fn prove_all(source: &str) -> Vec<Outcome> {
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", source);
    let id = project.expect_ok("main");
    let env = project.get_env_by_id(id).unwrap();
    let mut outcomes = Vec::new();
    for node in env.iter_goals() {
        let context = node.goal_context().unwrap();
        context.goal.value().validate().unwrap();
        let mut prover = Prover::new(&project, false);
        for fact in node.usable_facts(&project) {
            fact.value.validate().unwrap();
            prover.add_fact(fact);
        }
        prover.set_goal(&context);
        let outcome = prover.quick_verification_search();
        assert!(
            !matches!(outcome, Outcome::Error(_)),
            "{:?}\n{}",
            prover.error(),
            source
        );
        outcomes.push(outcome);
    }
    outcomes
}

#[test]
fn nested_generic_calls_preserve_argument_types_across_instances() {
    let declarations = r#"
        inductive Nat {
            zero
            suc(Nat)
        }
        define first<T>(left: T, right: Bool) -> T { left }
        define swapped<T>(left: Bool, right: T) -> T { first(right, left) }
        define nested<T>(left: Bool, right: T) -> T { swapped(left, right) }
    "#;
    for goal in [
        "theorem goal { nested(true, Nat.zero) = Nat.zero }",
        "theorem goal { nested(true, true) = true }",
    ] {
        let outcomes = prove_all(&format!("{declarations}\n{goal}"));
        assert!(!outcomes.is_empty());
        assert!(outcomes.iter().all(|outcome| *outcome == Outcome::Success));
    }
    assert_eq!(
        prove_all(&format!(
            "{declarations}\ntheorem goal {{ nested(true, Nat.zero) = Nat.zero.suc }}"
        )),
        vec![Outcome::Exhausted]
    );
}

#[test]
fn generic_theorem_references_keep_nested_quantifier_bindings() {
    let declarations = r#"
        theorem reflexive<T>(value: T) { value = value }
        theorem lifted<T>(outer: T, other: Bool) {
            forall(inner: Bool) { inner = inner and outer = outer }
        } by {
            (forall(inner: Bool) { reflexive(inner) and reflexive(outer) })
        }
    "#;
    let proof = "by { (forall(flag: Bool) { lifted(flag, false) }) }";
    let outcomes = prove_all(&format!("{declarations}\ntheorem goal {{ true }} {proof}"));
    assert!(!outcomes.is_empty());
    assert!(outcomes.iter().all(|outcome| *outcome == Outcome::Success));
    let outcomes = prove_all(&format!(
        "{declarations}\ntheorem goal {{ true = false }} {proof}"
    ));
    assert_eq!(outcomes.last(), Some(&Outcome::Exhausted));
    assert!(outcomes[..outcomes.len() - 1]
        .iter()
        .all(|outcome| *outcome == Outcome::Success));
}
