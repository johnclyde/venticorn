use venticorn::project::Project;
use venticorn::prover::{Outcome, Prover};

const PAIR: &str = "structure Pair<T, U> {\n first: T\n second: U\n}\nclass Pair<T, U> {\n define swap(self) -> Pair<U, T> { Pair.new(self.second, self.first) }\n}\n";

fn verify(source: &str) -> Outcome {
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", source);
    let id = project.expect_ok("main");
    for node in project.get_env_by_id(id).unwrap().iter_goals() {
        let mut prover = Prover::new(&project, false);
        for fact in node.usable_facts(&project) {
            fact.as_proposition().unwrap().value.validate().unwrap();
            prover.add_fact(fact);
        }
        let context = node.goal_context().unwrap();
        assert!(!context.goal.value().has_generic());
        prover.set_goal(&context);
        let outcome = prover.quick_verification_search();
        assert!(
            !matches!(outcome, Outcome::Error(_)),
            "{:?}",
            prover.error()
        );
        if outcome != Outcome::Success {
            return outcome;
        }
    }
    Outcome::Success
}

#[test]
fn double_swap_is_found_by_generic_proof_search() {
    for (relation, expected) in [("=", Outcome::Success), ("!=", Outcome::Exhausted)] {
        let source =
            format!("{PAIR}theorem goal<T, U>(p: Pair<T, U>) {{ p.swap.swap {relation} p }}");
        let mut project = Project::new_mock();
        project.mock("/mock/main.ac", &source);
        let id = project.expect_ok("main");
        let env = project.get_env_by_id(id).unwrap();
        let node = env.get_node_by_name("goal");
        let mut prover = Prover::new(&project, false);
        for fact in node.usable_facts(&project) {
            prover.add_fact(fact);
        }
        prover.set_goal(&node.goal_context().unwrap());
        let outcome = prover.quick_search();
        if expected == Outcome::Success {
            assert_eq!(outcome, Outcome::Success);
        } else {
            assert!(
                matches!(
                    outcome,
                    Outcome::Exhausted | Outcome::Timeout | Outcome::Constrained
                ),
                "false inequality was not rejected: {outcome:?}"
            );
            assert_eq!(verify(&source), Outcome::Exhausted);
        }
    }
}

#[test]
fn generated_generic_method_witness_replays_with_false_control() {
    for actual in ["Bool", "(Bool -> Bool) -> Bool"] {
        let source = format!(
            "structure Marker<T> {{\n value: Bool\n}}\n\
             class Marker<T> {{\n define chosen(self) -> Marker<T> {{ axiom }}\n}}\n\
             let seed: Marker<{actual}> = axiom\n\
             let mul: (Marker<{actual}>, Marker<{actual}>) -> Marker<{actual}> = axiom\n\
             define marked(n: Marker<{actual}>) -> Bool {{ exists(d: Marker<{actual}>) {{ mul(seed, d) = n }} }}\n\
             axiom marker_right(a: Marker<{actual}>, b: Marker<{actual}>) {{ b = seed.chosen -> mul(a, b) = seed.chosen }}\n\
             theorem goal {{ marked(seed.chosen) }}"
        );
        let mut project = Project::new_mock();
        project.mock("/mock/main.ac", &source);
        let id = project.expect_ok("main");
        let env = project.get_env_by_id(id).unwrap();
        let node = env.get_node_by_name("goal");
        let mut prover = Prover::new(&project, false);
        for fact in node.usable_facts(&project) {
            prover.add_fact(fact);
        }
        prover.set_goal(&node.goal_context().unwrap());
        assert_eq!(prover.quick_search(), Outcome::Success);
        let code = prover
            .get_and_print_proof()
            .unwrap()
            .to_code(&env.bindings)
            .unwrap();
        assert!(!code.is_empty());
        assert!(code.join("\n").contains("chosen"), "{code:?}");
        assert_eq!(
            verify(&format!("{source} by {{\n{}\n}}", code.join("\n"))),
            Outcome::Success
        );
        assert_eq!(
            verify(&format!(
                "{source} by {{ exists(p: Marker<{actual}>) {{ p != p }} }}"
            )),
            Outcome::Exhausted
        );
    }
}

#[test]
fn generic_recursive_member_constants_keep_class_parameters() {
    let source = "inductive Nat {\n zero\n suc(Nat)\n}\nstructure Box<T, U> {\n value: T\n}\nclass Box<T, U> {\n define repeat(self, n: Nat) -> T { match n {\n Nat.zero { self.value }\n Nat.suc(previous) { self.repeat(previous) }\n} }\n}\ntheorem goal<T, U>(value: T) { Box.new<T, U>(value).repeat(Nat.suc(Nat.zero)) = value }";
    assert_eq!(verify(source), Outcome::Success);
    assert_eq!(
        verify(&source.replace("= value }", "!= value }")),
        Outcome::Exhausted
    );
}

#[test]
fn generic_swap_defining_equation_keeps_both_parameter_orders() {
    assert_eq!(
        verify(&format!(
            "{PAIR}theorem goal<T, U>(p: Pair<T, U>) {{ p.swap = Pair.new(p.second, p.first) }}"
        )),
        Outcome::Success
    );
}
