use venticorn::builder::BuildStatus;
use venticorn::persistent_cache::CachePolicy;
use venticorn::project::Project;
use venticorn::prover::Outcome;

#[test]
fn bounded_class_laws_prove_a_member_without_a_body() {
    let text = r#"
            typeclass F: FooTrue {
                foo: F -> Bool
                bar: F -> Bool

                foo_true(a: F) {
                    a.foo
                }

                foo_imp_bar(a: F) {
                    a.foo implies a.bar
                }
            }
            
            theorem bar_true<F: FooTrue>(a: F) {
                a.bar
            }
        "#;
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", text);
    let module = project.expect_ok("main");
    let env = project.get_env_by_id(module).unwrap();
    assert_eq!(env.iter_goals().count(), 1);
    for node in env.iter_goals() {
        let mut ordinary = project.prover_for_node(&node, false);
        ordinary.set_goal(&node.goal_context().unwrap());
        let mut shallow = ordinary.clone();
        assert_eq!(shallow.quick_shallow_search(), Outcome::Success);
        assert_eq!(ordinary.quick_search(), Outcome::Success);
        assert!(ordinary.get_proof().is_some());
    }
    project.set_cache_policy(CachePolicy::Disabled);
    let report = project.sync_build_report();
    assert_eq!(report.status, BuildStatus::Good);
    assert_eq!(
        (report.goals_done, report.num_success, report.num_cached),
        (1, 1, 0)
    );
}
