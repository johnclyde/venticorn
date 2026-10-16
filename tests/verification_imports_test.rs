use venticorn::builder::{BuildStatus, Builder};
use venticorn::module::ModuleRef;
use venticorn::project::Project;
use venticorn::prover::Outcome;

const NAT: &str = r#"
        inductive Nat {
            0
            suc(Nat)
        }
        "#;
const MAIN: &str = r#"
            from nat import Nat
            let x: Nat = axiom
            let y: Nat = axiom

            theorem goal(a: Nat) {
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

            // Relies on an imported definition
            theorem goal2(a: Nat) {
                a != Nat.0 implies exists(b: Nat) { a = b.suc }
            }
            "#;

fn project(main: &str) -> Project {
    let mut project = Project::new_mock();
    project.mock("/mock/nat.ac", NAT);
    project.mock("/mock/main.ac", main);
    project
}

#[test]
fn nested_and_imported_definition_obligations_all_run() {
    let project = project(MAIN);
    let env = project
        .get_env_by_ref(&ModuleRef::Name("main".into()))
        .unwrap();
    assert_eq!(env.iter_goals().count(), 5);
    let mut expected_ranges = vec![];
    project.for_each_prover_slow(env, &mut |mut prover, goal| {
        assert_eq!(
            prover.verification_search(),
            Outcome::Success,
            "{}",
            goal.description()
        );
        expected_ranges.push((goal.first_line, goal.last_line));
        true
    });
    let mut events = vec![];
    {
        let mut builder = Builder::new(|event| events.push(event));
        project.build(&mut builder);
        assert_eq!(builder.status, BuildStatus::Good);
        assert_eq!(
            (
                builder.searches_total,
                builder.num_success,
                builder.num_cached,
                builder.goals_done
            ),
            (5, 5, 0, 5)
        );
    }
    assert_eq!(
        events.iter().filter_map(|e| e.verified).collect::<Vec<_>>(),
        expected_ranges
    );
    assert!(events.iter().all(|e| e.diagnostic.is_none()));
}

#[test]
fn imported_definition_does_not_validate_a_false_existential() {
    let source = MAIN.replace(
        "a != Nat.0 implies exists(b: Nat) { a = b.suc }",
        "exists(b: Nat) { b != b }",
    );
    let report = project(&source).sync_build_report();
    assert_eq!(report.status, BuildStatus::Warning);
    assert_eq!(
        (report.num_success, report.num_cached, report.goals_done),
        (4, 0, 5)
    );
    assert!(report.events.iter().any(|e| e.diagnostic.is_some()));
    assert!(report
        .cache
        .unwrap()
        .get(&ModuleRef::Name("main".into()))
        .is_none());
}

#[test]
fn completed_named_theorems_publish_imported_premises() {
    let source = MAIN.replace("theorem goal(a", "theorem goal1(a");
    let project = project(&source);
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
    println!("named premise sets: {hints:?}");
    assert_eq!(hints.len(), 2);
    assert!(hints["goal1"].is_empty());
    assert_eq!(
        hints["goal2"],
        std::collections::BTreeMap::from([(
            ModuleRef::Name("nat".into()),
            std::collections::BTreeSet::from([if cfg!(feature = "onnx") {
                "Nat.induction"
            } else {
                "Nat.new"
            }
            .into()])
        )])
    );
}

#[test]
fn self_premise_exclusion_keeps_imported_homonyms() {
    let mut project = Project::new_mock();
    project.mock(
        "/mock/dependency.ac",
        "let flag: Bool = axiom\naxiom goal { flag }",
    );
    project.mock(
        "/mock/main.ac",
        "import dependency\ntheorem goal { dependency.flag }",
    );
    let report = project.sync_build_report();
    assert_eq!(report.status, BuildStatus::Good);
    let cache = report.cache.unwrap();
    let hints = cache
        .get(&ModuleRef::Name("main".into()))
        .unwrap()
        .theorem_premises();
    assert_eq!(
        hints["goal"],
        std::collections::BTreeMap::from([(
            ModuleRef::Name("dependency".into()),
            std::collections::BTreeSet::from(["goal".into()])
        )])
    );
}

#[test]
fn an_unchanged_second_verification_performs_no_searches() {
    let source = MAIN.replace("theorem goal(a", "theorem goal1(a");
    let project = project(&source);
    let cold = project.sync_build_report();
    assert_eq!(cold.status, BuildStatus::Good);
    assert_eq!((cold.num_success, cold.num_cached), (5, 0));
    let mut warm = project.builder(|_| {});
    project.build(&mut warm);
    assert_eq!(warm.status, BuildStatus::Good);
    assert_eq!(
        (
            warm.searches_total,
            warm.num_success,
            warm.num_cached,
            warm.goals_done
        ),
        (0, 0, 5, 5)
    );
}
