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

#[test]
fn an_invalid_instance_must_fail_its_actual_law_obligation() {
    let text = r#"
            inductive Z2 {
                zero
                one
            }

            typeclass S: Singleton {
                value: S

                unique(x: S) {
                    x = S.value
                }
            }

            instance Z2: Singleton {
                let value: Z2 = Z2.zero
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
    let report = project.sync_build_report();
    assert_eq!(report.status, BuildStatus::Warning);
    assert_eq!(
        (report.goals_done, report.num_success, report.num_cached),
        (1, 0, 0)
    );
    assert_eq!(project.cached_build().num_modules(), 0);
}

#[test]
fn a_valid_instance_proves_a_real_law_obligation() {
    let text = r#"
            inductive Z1 {
                zero
            }

            typeclass S: Singleton {
                value: S

                unique(x: S) {
                    x = S.value
                }
            }

            instance Z1: Singleton {
                let value: Z1 = Z1.zero
            }
        "#;
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", text);
    let module = project.expect_ok("main");
    let env = project.get_env_by_id(module).unwrap();
    assert_eq!(env.iter_goals().count(), 1);
    for node in env.iter_goals() {
        let goal = node.goal_context().unwrap();
        for shallow in [false, true] {
            let mut prover = project.prover_for_node(&node, false);
            prover.set_goal(&goal);
            let result = if shallow {
                prover.quick_shallow_search()
            } else {
                prover.quick_search()
            };
            assert_eq!(result, Outcome::Success);
        }
    }
    let report = project.sync_build_report();
    assert_eq!(report.status, BuildStatus::Good);
    assert_eq!(
        (report.goals_done, report.num_success, report.num_cached),
        (1, 1, 0)
    );
}

#[test]
fn generic_instance_methods_use_checked_implementations() {
    let text = r#"
            inductive Z1 {
                zero
            }

            typeclass T: TwoColored {
                is_red: T -> Bool
            }

            instance Z1: TwoColored {
                define is_red(self) -> Bool {
                    true
                }
            }

            theorem goal {
                TwoColored.is_red(Z1.zero)
            }
        "#;
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", text);
    let module = project.expect_ok("main");
    let env = project.get_env_by_id(module).unwrap();
    assert_eq!(env.iter_goals().count(), 1);
    for node in env.iter_goals() {
        let goal = node.goal_context().unwrap();
        for shallow in [false, true] {
            let mut prover = project.prover_for_node(&node, false);
            prover.set_goal(&goal);
            let result = if shallow {
                prover.quick_shallow_search()
            } else {
                prover.quick_search()
            };
            assert_eq!(result, Outcome::Success);
        }
    }
    let report = project.sync_build_report();
    assert_eq!(report.status, BuildStatus::Good);
    assert_eq!(
        (report.goals_done, report.num_success, report.num_cached),
        (1, 1, 0)
    );
}

#[test]
fn function_valued_instance_members_use_checked_implementations() {
    let text = r#"
            inductive Z1 {
                zero
            }

            typeclass T: TwoColored {
                is_red: T -> Bool
            }

            instance Z1: TwoColored {
                let is_red: Z1 -> Bool = function(z: Z1) {
                    true
                }
            }

            theorem goal {
                TwoColored.is_red(Z1.zero)
            }
        "#;
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", text);
    let module = project.expect_ok("main");
    let env = project.get_env_by_id(module).unwrap();
    assert_eq!(env.iter_goals().count(), 1);
    for node in env.iter_goals() {
        let goal = node.goal_context().unwrap();
        for shallow in [false, true] {
            let mut prover = project.prover_for_node(&node, false);
            prover.set_goal(&goal);
            let result = if shallow {
                prover.quick_shallow_search()
            } else {
                prover.quick_search()
            };
            assert_eq!(result, Outcome::Success);
        }
    }
    let report = project.sync_build_report();
    assert_eq!(report.status, BuildStatus::Good);
    assert_eq!(
        (report.goals_done, report.num_success, report.num_cached),
        (1, 1, 0)
    );

    let false_text = text.replace("                    true", "                    false");
    assert_ne!(false_text, text);
    let mut false_project = Project::new_mock();
    false_project.mock("/mock/main.ac", &false_text);
    let false_module = false_project.expect_ok("main");
    let false_env = false_project.get_env_by_id(false_module).unwrap();
    assert_eq!(false_env.iter_goals().count(), 1);
    for node in false_env.iter_goals() {
        let goal = node.goal_context().unwrap();
        let mut shallow = false_project.prover_for_node(&node, false);
        shallow.set_goal(&goal);
        assert_eq!(shallow.quick_shallow_search(), Outcome::Exhausted);
        let mut ordinary = false_project.prover_for_node(&node, false);
        ordinary.set_goal(&goal);
        assert!(matches!(
            ordinary.quick_search(),
            Outcome::Exhausted | Outcome::Constrained | Outcome::Timeout
        ));
    }
    false_project.set_cache_policy(CachePolicy::Disabled);
    let report = false_project.sync_build_report();
    assert_eq!(report.status, BuildStatus::Warning);
    assert_eq!(
        (report.goals_done, report.num_success, report.num_cached),
        (1, 0, 0)
    );
    assert_eq!(false_project.cached_build().num_modules(), 0);
}

#[test]
fn explicit_instance_constants_prove_after_their_laws() {
    let text = r#"
            inductive Z1 {
                zero
            }

            typeclass S: Singleton {
                value: S

                unique(x: S) {
                    x = S.value
                }
            }

            instance Z1: Singleton {
                let value: Z1 = Z1.zero
            }

            theorem goal {
                Z1.zero = Singleton.value<Z1>
            }
        "#;
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", text);
    let module = project.expect_ok("main");
    let env = project.get_env_by_id(module).unwrap();
    assert_eq!(env.iter_goals().count(), 2);
    for node in env.iter_goals() {
        let goal = node.goal_context().unwrap();
        for shallow in [false, true] {
            let mut prover = project.prover_for_node(&node, false);
            prover.set_goal(&goal);
            let result = if shallow {
                prover.quick_shallow_search()
            } else {
                prover.quick_search()
            };
            assert_eq!(result, Outcome::Success);
        }
    }
    let report = project.sync_build_report();
    assert_eq!(report.status, BuildStatus::Good);
    assert_eq!(
        (report.goals_done, report.num_success, report.num_cached),
        (2, 2, 0)
    );

    let false_text = text.replace(
        "Z1.zero = Singleton.value<Z1>",
        "not (Z1.zero = Singleton.value<Z1>)",
    );
    assert_ne!(false_text, text);
    let mut false_project = Project::new_mock();
    false_project.mock("/mock/main.ac", &false_text);
    let false_module = false_project.expect_ok("main");
    let false_env = false_project.get_env_by_id(false_module).unwrap();
    assert_eq!(false_env.iter_goals().count(), 2);
    for (index, node) in false_env.iter_goals().enumerate() {
        let goal = node.goal_context().unwrap();
        let mut shallow = false_project.prover_for_node(&node, false);
        shallow.set_goal(&goal);
        let mut ordinary = false_project.prover_for_node(&node, false);
        ordinary.set_goal(&goal);
        if index == 0 {
            assert_eq!(shallow.quick_shallow_search(), Outcome::Success);
            assert_eq!(ordinary.quick_search(), Outcome::Success);
        } else {
            assert_eq!(shallow.quick_shallow_search(), Outcome::Exhausted);
            assert!(matches!(
                ordinary.quick_search(),
                Outcome::Exhausted | Outcome::Constrained | Outcome::Timeout
            ));
        }
    }
    false_project.set_cache_policy(CachePolicy::Disabled);
    let report = false_project.sync_build_report();
    assert_eq!(report.status, BuildStatus::Warning);
    assert_eq!(
        (report.goals_done, report.num_success, report.num_cached),
        (2, 1, 0)
    );
    assert_eq!(false_project.cached_build().num_modules(), 0);
}

#[test]
fn class_laws_do_not_apply_to_noninstances() {
    let text = r#"
            inductive Z2 {
                zero
                one
            }

            define is_equal<T>(x: T, y: T) -> Bool {
                x = y
            }

            typeclass S: Singleton {
                element: S

                unique(x: S, y: S) {
                    is_equal(x, y)
                }
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
    assert_eq!(project.cached_build().num_modules(), 0);
}

#[test]
fn typeclass_theorems_combine_through_a_checked_instance() {
    let text = r#"
            typeclass F: Foo {
                foo: F -> Bool
            }

            axiom always_foo<F: Foo>(x: F) {
                x.foo
            }

            inductive Bar {
                bar
            }

            let qux: Bool = axiom

            instance Bar: Foo {
                define foo(self) -> Bool {
                    qux
                }
            }

            theorem goal {
                qux
            }
        "#;
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", text);
    let module = project.expect_ok("main");
    let env = project.get_env_by_id(module).unwrap();
    assert_eq!(env.iter_goals().count(), 1);
    for node in env.iter_goals() {
        let goal = node.goal_context().unwrap();
        let class = env.bindings.get_typeclass_for_name("Foo").unwrap();
        assert!(goal.proof_scope.has_membership(module, "Bar", class));
        let mut ordinary = project.prover_for_node(&node, false);
        ordinary.set_goal(&goal);
        let mut shallow = ordinary.clone();
        assert_eq!(shallow.quick_shallow_search(), Outcome::Success);
        assert_eq!(ordinary.quick_search(), Outcome::Success);
        let code = ordinary
            .get_proof()
            .unwrap()
            .to_code(&node.bindings_for_codegen())
            .unwrap();
        // This automatic proof can emit an empty body. Replay its actual output;
        // the separate generic-method witness test requires nonempty output.
        let lines = text.lines().collect::<Vec<_>>();
        let insertion = goal.proof_insertion_line as usize;
        assert!(goal.insert_block);
        assert_eq!(lines[insertion].trim(), "}");
        let suffix = lines[insertion + 1..].join("\n");
        for (body, count, expected_first) in [
            (code.join("\n"), 1, Outcome::Success),
            ("false".into(), 2, Outcome::Exhausted),
        ] {
            let replay = format!(
                "{} by {{\n{body}\n}}\n{suffix}",
                lines[..=insertion].join("\n")
            );
            let mut replay_project = Project::new_mock();
            replay_project.mock("/mock/main.ac", &replay);
            let replay_module = replay_project.expect_ok("main");
            let replay_env = replay_project.get_env_by_id(replay_module).unwrap();
            let goals = replay_env.iter_goals().collect::<Vec<_>>();
            assert_eq!(goals.len(), count);
            let first = &goals[0];
            let mut ordinary = replay_project.prover_for_node(first, false);
            ordinary.set_goal(&first.goal_context().unwrap());
            let mut shallow = ordinary.clone();
            assert_eq!(ordinary.quick_search(), expected_first);
            assert_eq!(shallow.quick_shallow_search(), expected_first);
            let report = replay_project.sync_build_report();
            assert_eq!(report.goals_done, count as i32);
            if expected_first == Outcome::Success {
                assert_eq!(report.status, BuildStatus::Good);
                assert_eq!(report.num_success, count as i32);
            } else {
                assert_eq!(report.status, BuildStatus::Warning);
                assert!(report.num_success < report.goals_total);
                assert_eq!(replay_project.cached_build().num_modules(), 0);
            }
        }
    }
    project.set_cache_policy(CachePolicy::Disabled);
    let report = project.sync_build_report();
    assert_eq!(report.status, BuildStatus::Good);
    assert_eq!(
        (report.goals_done, report.num_success, report.num_cached),
        (1, 1, 0)
    );
}
