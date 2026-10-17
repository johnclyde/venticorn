use venticorn::builder::BuildStatus;
use venticorn::persistent_cache::CachePolicy;
use venticorn::project::Project;
use venticorn::prover::Outcome;

#[test]
fn bounded_axiom_does_not_apply_to_a_noninstance() {
    let text = r#"
            inductive Z1 {
                zero
            }

            inductive Z2 {
                zero
                one
            }

            define is_equal<T>(x: T, y: T) -> Bool {
                x = y
            }

            typeclass S: Singleton {
                element: S
            }

            instance Z1: Singleton {
                let element: Z1 = Z1.zero
            }

            // TODO: constrain/prove instead of axiom
            axiom all_equal<S: Singleton>(x: S, y: S) {
                is_equal(x, y)
            }

            theorem goal {
                is_equal(Z2.zero, Z2.one)
            }
        "#;
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", text);
    let module = project.expect_ok("main");
    let env = project.get_env_by_id(module).unwrap();
    assert_eq!(env.iter_goals().count(), 1);
    for node in env.iter_goals() {
        let goal = node.goal_context().unwrap();
        let mut shallow = project.prover_for_node(&node, false);
        shallow.set_goal(&goal);
        assert_eq!(shallow.quick_shallow_search(), Outcome::Exhausted);
        let mut ordinary = project.prover_for_node(&node, false);
        ordinary.set_goal(&goal);
        assert!(matches!(
            ordinary.quick_search(),
            Outcome::Exhausted | Outcome::Constrained | Outcome::Timeout
        ));
    }
    project.set_cache_policy(CachePolicy::Disabled);
    let report = project.sync_build_report();
    assert_eq!(report.status, BuildStatus::Warning);
    assert_eq!(
        (report.goals_done, report.num_success, report.num_cached),
        (1, 0, 0)
    );
}
