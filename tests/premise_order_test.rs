use std::collections::{BTreeMap, BTreeSet};
use venticorn::builder::BuildStatus;
use venticorn::module::ModuleRef;
use venticorn::project::Project;
use venticorn::prover::{Outcome, Prover};

const NAT: &str = r#"
        inductive Nat {
            0
            suc(Nat)
        }

        let nz: Nat = axiom
        axiom nz_nonzero {
            nz != Nat.0
        }
        "#;
const MAIN: &str = r#"
            from nat import Nat
            let x: Nat = axiom
            let y: Nat = axiom

            theorem goal1(a: Nat) {
                a != x or a != y or x = y
            } by {
                if a = x {
                    if a = y {
                        x = y
                    }
                    a != y or x = y
                }
                a != x or a != y or x = y
            }

            // Relies on imported things
            theorem goal2 {
                exists(b: Nat) { nat.nz = b.suc }
            }
            "#;

fn project(main: &str) -> Project {
    let mut project = Project::new_mock();
    project.mock("/mock/nat.ac", NAT);
    project.mock("/mock/main.ac", main);
    project
}

#[test]
fn imported_existential_records_sorted_complete_premises() {
    let project = project(MAIN);
    let report = project.sync_build_report();
    assert_eq!(report.status, BuildStatus::Good);
    assert_eq!(
        (report.num_success, report.num_cached, report.goals_done),
        (5, 0, 5)
    );
    let cache = report.cache.unwrap();
    let hints = cache
        .get(&ModuleRef::Name("main".into()))
        .unwrap()
        .theorem_premises();
    println!("ordered premise sets: {hints:?}");
    assert_eq!(hints.len(), 2);
    assert!(hints["goal1"].is_empty());
    assert_eq!(
        hints["goal2"],
        BTreeMap::from([(
            ModuleRef::Name("nat".into()),
            BTreeSet::from(["Nat.new".into(), "nz_nonzero".into()])
        )])
    );
    assert_eq!(
        hints["goal2"][&ModuleRef::Name("nat".into())]
            .iter()
            .map(String::as_str)
            .collect::<Vec<_>>(),
        ["Nat.new", "nz_nonzero"]
    );
}

#[test]
fn imported_existential_replays_its_emitted_proof() {
    let project = project(MAIN);
    let env = project
        .get_env_by_ref(&ModuleRef::Name("main".into()))
        .unwrap();
    let node = env.get_node_by_name("goal2");
    let mut prover = Prover::new(&project, false);
    for fact in node.usable_facts(&project) {
        prover.add_fact(fact);
    }
    prover.set_goal(&node.goal_context().unwrap());
    assert_eq!(prover.verification_search(), Outcome::Success);
    let code = prover
        .get_condensed_proof()
        .unwrap()
        .to_code(&env.bindings)
        .unwrap();
    println!("imported existential emitted {} proof lines", code.len());
    let replay = format!("{MAIN} by {{\n{}\n}}", code.join("\n"));
    assert_eq!(
        self::project(&replay).sync_build_report().status,
        BuildStatus::Good
    );
    let rejected =
        self::project(&format!("{MAIN} by {{ exists(b: Nat) {{ b != b }} }}")).sync_build_report();
    assert_eq!(rejected.status, BuildStatus::Warning);
}
