use venticorn::builder::BuildStatus;
use venticorn::project::Project;
use venticorn::prover::{Outcome, Prover};

const DOUBLE_SWAP: &str = r#"structure Pair<T, U> {
    first: T
    second: U
}
class Pair<T, U> {
    define swap(self) -> Pair<U, T> {
        Pair.new(self.second, self.first)
    }
}
theorem swap_swap<T, U>(p: Pair<T, U>) {
    p.swap.swap = p
}
"#;

fn project(source: &str) -> Project {
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", source);
    project.expect_ok("main");
    project
}

fn prover(project: &Project) -> Prover {
    let env = project
        .get_env_by_ref(&venticorn::module::ModuleRef::Name("main".into()))
        .unwrap();
    let node = env.iter_goals().last().unwrap();
    let mut prover = Prover::new(project, false);
    for fact in node.usable_facts(project) {
        prover.add_fact(fact);
    }
    prover.set_goal(&node.goal_context().unwrap());
    prover
}

#[test]
fn production_verification_can_use_deeper_steps_and_replay_its_output() {
    let project = project(DOUBLE_SWAP);
    assert_eq!(prover(&project).quick_shallow_search(), Outcome::Exhausted);
    assert_eq!(
        prover(&project).quick_verification_search(),
        Outcome::Exhausted
    );
    let mut full = prover(&project);
    assert_eq!(full.verification_search(), Outcome::Success);
    let proof = full.get_proof().unwrap();
    assert!(!proof.needs_simplification());
    let env = project
        .get_env_by_ref(&venticorn::module::ModuleRef::Name("main".into()))
        .unwrap();
    let code = proof.to_code(&env.bindings).unwrap();
    let replay = format!("{DOUBLE_SWAP} by {{\n{}\n}}", code.join("\n"));
    assert_eq!(
        self::project(&replay).sync_build_report().status,
        BuildStatus::Good
    );
    assert_eq!(project.sync_build_report().status, BuildStatus::Good);
}

#[test]
fn false_claims_remain_unverified_in_both_search_modes() {
    let source = DOUBLE_SWAP.replace("p.swap.swap = p", "p.swap.swap != p");
    let project = project(&source);
    assert_eq!(prover(&project).quick_shallow_search(), Outcome::Exhausted);
    let actual = prover(&project).verification_search();
    assert!(
        matches!(
            actual,
            Outcome::Exhausted | Outcome::Constrained | Outcome::Timeout
        ),
        "false claim returned {actual:?}"
    );
    let false_body = format!("{DOUBLE_SWAP} by {{ false }}");
    assert_eq!(
        self::project(&false_body).sync_build_report().status,
        BuildStatus::Warning
    );
}

#[test]
fn factual_clauses_do_not_spend_the_nonfactual_activation_budget() {
    let mut source = String::new();
    for i in 0..12 {
        source.push_str(&format!(
            "let p{i}: Bool = axiom\naxiom fact{i} {{ p{i} }}\n"
        ));
    }
    let project = project(&source);
    let env = project
        .get_env_by_ref(&venticorn::module::ModuleRef::Name("main".into()))
        .unwrap();
    let mut prover = Prover::new(&project, false);
    for fact in env.exported_facts() {
        prover.add_fact(fact);
    }
    // No goal is set: every queued clause is factual, so the budget stays unused.
    assert_eq!(
        prover.search_for_contradiction(1, 1.0, false),
        Outcome::Exhausted
    );
    assert!(prover.num_activated() > 1);
}
