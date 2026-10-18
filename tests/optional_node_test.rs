use venticorn::builder::BuildStatus;
use venticorn::environment::Environment;
use venticorn::goal::Goal;
use venticorn::project::Project;
use venticorn::prover::Outcome;
use venticorn::statement::Statement;

#[test]
fn unsolved_outer_fact_is_absent_but_body_and_solve_goals_remain() {
    let mut project = Project::new_mock();
    project.mock(
        "/mock/main.ac",
        "let b: Bool = true\nsolve b by {\n true\n}\n",
    );
    let module = project.expect_ok("main");
    let env = project.get_env_by_id(module).unwrap();
    let node = env.nodes.last().unwrap();
    assert!(node.proposition().is_none());
    assert!(node.get_fact().is_none());
    assert!(node.has_goal());
    assert!(matches!(node.block().unwrap().goal, Some(Goal::Solve(..))));
    let goals = env.iter_goals().collect::<Vec<_>>();
    assert_eq!(goals.len(), 2);
    assert!(matches!(
        goals[0].goal_context().unwrap().goal,
        Goal::Prove(_)
    ));
    assert!(matches!(
        goals[1].goal_context().unwrap().goal,
        Goal::Solve(..)
    ));
    let mut slow = vec![];
    project.for_each_prover_slow(env, &mut |mut prover, goal| {
        slow.push((
            (goal.first_line, goal.last_line),
            prover.verification_search(),
        ));
        true
    });
    let mut fast = vec![];
    project.for_each_prover_fast(env, &mut |mut prover, goal| {
        fast.push((
            (goal.first_line, goal.last_line),
            prover.verification_search(),
        ));
        true
    });
    assert_eq!(slow.len(), 2);
    assert_eq!(slow, fast);
    assert_eq!(
        slow.iter()
            .map(|(_, outcome)| outcome.clone())
            .collect::<Vec<_>>(),
        vec![Outcome::Success, Outcome::Exhausted]
    );
    let report = project.sync_build_report();
    assert_eq!(report.status, BuildStatus::Warning);
    assert_eq!(
        (report.goals_done, report.num_success, report.num_cached),
        (2, 1, 0)
    );
    assert_eq!(project.cached_build().num_modules(), 0);
}

#[test]
fn a_solved_equality_body_keeps_its_outer_fact_and_one_real_proof_goal() {
    let mut project = Project::new_mock();
    project.mock(
        "/mock/main.ac",
        "let b: Bool = true\nsolve b by {\n b = true\n}\n",
    );
    let module = project.expect_ok("main");
    let env = project.get_env_by_id(module).unwrap();
    let node = env.nodes.last().unwrap();
    assert!(node.proposition().is_some());
    assert!(node.get_fact().is_some());
    assert!(!node.has_goal());
    assert!(node.block().unwrap().goal.is_none());
    let goals = env.iter_goals().collect::<Vec<_>>();
    assert_eq!(goals.len(), 1);
    assert!(matches!(
        goals[0].goal_context().unwrap().goal,
        Goal::Prove(_)
    ));
    for shallow in [false, true] {
        let mut outcomes = vec![];
        project.for_each_prover_slow(env, &mut |mut prover, _| {
            let outcome = if shallow {
                prover.quick_verification_search()
            } else {
                prover.verification_search()
            };
            assert_eq!(outcome, Outcome::Success);
            assert!(prover.get_proof().is_some());
            outcomes.push(outcome);
            true
        });
        assert_eq!(outcomes, vec![Outcome::Success]);
    }
    let report = project.sync_build_report();
    assert_eq!(report.status, BuildStatus::Good);
    assert_eq!(
        (report.goals_done, report.num_success, report.num_cached),
        (1, 1, 0)
    );
    assert_eq!(project.cached_build().num_modules(), 1);
}

#[test]
fn claimless_problem_retains_its_false_child_and_cannot_complete_a_module_cache() {
    let mut project = Project::new_mock();
    project.mock(
        "/mock/main.ac",
        "problem {\n true\n true != true\n}\ntheorem tail { true }\n",
    );
    let module = project.expect_ok("main");
    let env = project.get_env_by_id(module).unwrap();
    let problem = &env.nodes[0];
    assert!(problem.proposition().is_none());
    assert!(problem.get_fact().is_none());
    assert!(!problem.has_goal());
    assert_eq!(
        problem
            .block()
            .unwrap()
            .env
            .nodes
            .iter()
            .filter(|node| node.has_goal())
            .count(),
        2
    );
    assert_eq!(env.iter_goals().count(), 3);
    for shallow in [false, true] {
        let mut outcomes = vec![];
        project.for_each_prover_slow(env, &mut |mut prover, _| {
            outcomes.push(if shallow {
                prover.quick_verification_search()
            } else {
                prover.verification_search()
            });
            true
        });
        assert_eq!(outcomes.len(), 3);
        assert_eq!(outcomes[0], Outcome::Success);
        assert_eq!(outcomes[1], Outcome::Exhausted);
        assert_eq!(outcomes[2], Outcome::Success);
    }
    let report = project.sync_build_report();
    assert_eq!(report.status, BuildStatus::Warning);
    assert_eq!(
        (report.goals_done, report.num_success, report.num_cached),
        (3, 2, 0)
    );
    assert_eq!(project.cached_build().num_modules(), 0);
}

#[test]
fn a_trailing_claimless_block_cannot_export_an_earlier_claim() {
    let mut env = Environment::new(2);
    let statement = Statement::parse_str("forall(x: Bool) {\n true\n problem { true }\n}").unwrap();
    let error = env
        .add_statement(&mut Project::new_mock(), &statement)
        .unwrap_err();
    assert_eq!(error.message(), "expected a claim in this block");
}
