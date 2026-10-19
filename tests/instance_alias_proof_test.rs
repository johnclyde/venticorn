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

#[test]
fn checked_instance_alias_finishes_as_an_assumption_and_replays_at_its_goal() {
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
    let goal = node.goal_context().unwrap();
    let mut prover = project.prover_for_node(&node, false);
    prover.set_goal(&goal);
    assert_eq!(prover.quick_search(), Outcome::Success);
    assert!(prover.get_final_step().unwrap().rule.is_assumption());
    let code = prover
        .get_proof()
        .unwrap()
        .to_code(&node.bindings_for_codegen())
        .unwrap();
    let lines = text.lines().collect::<Vec<_>>();
    let insertion = goal.proof_insertion_line as usize;
    assert!(goal.insert_block);
    assert_eq!(lines[insertion].trim(), "}");
    let suffix = lines[insertion + 1..].join("\n");
    for (body, valid) in [(code.join("\n"), true), ("false".into(), false)] {
        let replay = format!(
            "{} by {{\n{body}\n}}\n{suffix}",
            lines[..=insertion].join("\n")
        );
        let mut replay_project = Project::new_mock();
        replay_project.mock("/mock/main.ac", &replay);
        let module = replay_project.expect_ok("main");
        let env = replay_project.get_env_by_id(module).unwrap();
        let goals = env.iter_goals().collect::<Vec<_>>();
        assert!(!goals.is_empty());
        if valid {
            for node in &goals {
                let mut ordinary = replay_project.prover_for_node(node, false);
                ordinary.set_goal(&node.goal_context().unwrap());
                let mut shallow = ordinary.clone();
                assert_eq!(ordinary.quick_search(), Outcome::Success);
                assert_eq!(shallow.quick_shallow_search(), Outcome::Success);
            }
        } else {
            assert_eq!(goals.len(), 2);
            let first = &goals[0];
            let context = first.goal_context().unwrap();
            assert_eq!(context.goal.range().start.line, insertion as u32 + 1);
            let mut ordinary = replay_project.prover_for_node(first, false);
            ordinary.set_goal(&context);
            let mut shallow = ordinary.clone();
            assert!(matches!(
                ordinary.quick_search(),
                Outcome::Exhausted | Outcome::Timeout | Outcome::Constrained
            ));
            assert_eq!(shallow.quick_shallow_search(), Outcome::Exhausted);
        }
        let report = replay_project.sync_build_report();
        if valid {
            assert_eq!(report.status, BuildStatus::Good);
            assert_eq!(report.num_success, report.goals_total);
        } else {
            assert_eq!(report.status, BuildStatus::Warning);
            assert!(report.num_success < report.goals_total);
            assert_eq!(replay_project.cached_build().num_modules(), 0);
        }
    }
}
