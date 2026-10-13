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
    prover.quick_verification_search()
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
