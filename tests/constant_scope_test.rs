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
            assert!(!context.goal.value().is_generic());
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

#[test]
fn concrete_definition_instances_support_generic_axioms() {
    let declarations = r#"
        inductive Nat {
            zero
            suc(Nat)
        }
        define repeat<T>(f: T -> T, value: T, n: Nat) -> T { axiom }
        axiom repeat_base<T>(f: T -> T, value: T) { repeat(f, value, Nat.zero) = value }
        class Nat {
            define add(self, other: Nat) -> Nat { repeat(Nat.suc, self, other) }
        }
    "#;
    assert_eq!(
        outcomes(&format!(
            "{declarations} theorem goal(value: Nat) {{ value.add(Nat.zero) = value }}"
        )),
        vec![Outcome::Success]
    );
    assert_eq!(
        outcomes(&format!(
            "{declarations} theorem goal(value: Nat) {{ value.add(Nat.zero) != value }}"
        )),
        vec![Outcome::Exhausted]
    );
}

#[test]
fn nested_generic_definitions_preserve_automatic_proofs() {
    let declarations = r#"
        define identity<T>(value: T) -> T { value }
        define nested<T>(value: T) -> T { identity(value) }
        define outer<T>(value: T) -> T { nested(value) }
    "#;
    for name in ["identity", "nested", "outer"] {
        assert_eq!(
            outcomes(&format!(
                "{declarations} theorem goal {{ {name}(true) = true }}"
            )),
            vec![Outcome::Success]
        );
        assert_eq!(
            outcomes(&format!(
                "{declarations} theorem goal {{ {name}(true) = false }}"
            )),
            vec![Outcome::Exhausted]
        );
    }
}

#[test]
fn generic_goals_keep_phantom_type_arguments_concrete() {
    let declarations = r#"
        define phantom<T>(flag: Bool) -> Bool { flag }
    "#;
    for (goal, expected) in [
        ("phantom<T>(true)", Outcome::Success),
        ("not phantom<T>(true)", Outcome::Exhausted),
    ] {
        assert_eq!(
            outcomes(&format!("{declarations} theorem goal<T> {{ {goal} }}")),
            vec![expected],
        );
    }
}

#[test]
fn solve_goals_inside_generic_theorems_use_the_opaque_local_type() {
    let source = r#"
        define identity<T>(value: T) -> T { value }
        theorem goal<T>(value: T) { value = value } by {
            solve identity<T>(value) by {}
        }
    "#;
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", source);
    let id = project.expect_ok("main");
    let env = project.get_env_by_id(id).unwrap();
    let mut saw_solve = false;
    for node in env.iter_goals() {
        let context = node.goal_context().unwrap();
        if matches!(context.goal, venticorn::goal::Goal::Solve(..)) {
            saw_solve = true;
            context.goal.value().validate().unwrap();
            assert!(!context.goal.value().is_generic());
            let mut prover = Prover::new(&project, false);
            for fact in node.usable_facts(&project) {
                prover.add_fact(fact);
            }
            prover.set_goal(&context);
            assert_eq!(prover.error(), None);
        }
    }
    assert!(saw_solve);
}
