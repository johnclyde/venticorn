use venticorn::builder::BuildStatus;
use venticorn::persistent_cache::CachePolicy;
use venticorn::project::Project;
use venticorn::prover::Outcome;

#[test]
fn checked_instance_aliases_prove_the_member_equation() {
    let text = r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }

            inductive Foo {
                foo
            }

            class Foo {
                define mul(self, other: Foo) -> Foo {
                    Foo.foo
                }
            }

            instance Foo: Magma {
                let mul: (Foo, Foo) -> Foo = Foo.mul
            }

            theorem goal(a: Foo) {
                Magma.mul(a, a) = a * a
            }
        "#;
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", text);
    let module = project.expect_ok("main");
    let env = project.get_env_by_id(module).unwrap();
    assert_eq!(env.iter_goals().count(), 1);
    let node = env.get_node_by_name("goal");
    let context = node.goal_context().unwrap();
    let mut prover = project.prover_for_node(&node, false);
    prover.set_goal(&context);
    assert_eq!(prover.quick_search(), Outcome::Success);
    assert!(prover.get_proof().is_some());
    project.set_cache_policy(CachePolicy::Disabled);
    let report = project.sync_build_report();
    assert_eq!(report.status, BuildStatus::Good);
    assert_eq!(
        (report.goals_done, report.num_success, report.num_cached),
        (1, 1, 0)
    );
}
