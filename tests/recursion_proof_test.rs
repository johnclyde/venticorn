// Modified for Venticorn: check recursive equations through real proof search.
use venticorn::project::Project;
use venticorn::prover::{Outcome, Prover};

fn prove(text: &str) -> Outcome {
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", text);
    let id = project.expect_ok("main");
    let env = project.get_env_by_id(id).unwrap();
    let node = env.get_node_by_name("goal");
    let context = node.goal_context().unwrap();
    let mut prover = Prover::new(&project, false);
    for fact in node.usable_facts(&project) {
        prover.add_fact(fact);
    }
    prover.set_goal(&context);
    let outcome = prover.quick_verification_search();
    assert!(
        !matches!(outcome, Outcome::Error(_)),
        "{:?}\n{}",
        prover.error,
        text
    );
    outcome
}

const NAT: &str = "inductive Nat {\n zero\n suc(Nat)\n}\n";

#[test]
fn recursive_base_equations_prove_true_claims_only() {
    let definition = r#"
        define add(a: Nat, b: Nat) -> Nat {
            match a {
                Nat.zero { b }
                Nat.suc(pred) { add(pred, b).suc }
            }
        }
    "#;
    assert_eq!(
        prove(&format!(
            "{NAT}{definition}\ntheorem goal(n: Nat) {{ add(Nat.zero, n) = n }}"
        )),
        Outcome::Success
    );
    assert_eq!(
        prove(&format!(
            "{NAT}{definition}\ntheorem goal {{ add(Nat.zero, Nat.zero) = Nat.zero.suc }}"
        )),
        Outcome::Exhausted
    );
}

#[test]
fn generic_recursive_equations_specialize_at_distinct_types() {
    let repeat = r#"
        inductive Color {
            red
            blue
        }
        define stay(color: Color) -> Color { color }
        define repeat<T>(n: Nat, f: T -> T, a: T) -> T {
            match n {
                Nat.zero { a }
                Nat.suc(pred) { repeat(pred, f, f(a)) }
            }
        }
    "#;
    for goal in [
        "theorem goal(n: Nat) { repeat(Nat.zero, Nat.suc, n) = n }",
        "theorem goal { repeat(Nat.zero.suc, Nat.suc, Nat.zero) = Nat.zero.suc }",
        "theorem goal(color: Color) { repeat(Nat.zero, stay, color) = color }",
    ] {
        assert_eq!(prove(&format!("{NAT}{repeat}\n{goal}")), Outcome::Success);
    }
    assert_eq!(
        prove(&format!(
            "{NAT}{repeat}\ntheorem goal {{ repeat(Nat.zero.suc, Nat.suc, Nat.zero) = Nat.zero }}"
        )),
        Outcome::Exhausted
    );
}
