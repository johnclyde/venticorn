// Modified for Venticorn: generic function heads retain canonical identity across qualification.
use venticorn::project::Project;
use venticorn::prover::{Outcome, Prover};

fn prove_goal(expression: &str, expected: Outcome) {
    let mut project = Project::new_mock();
    project.mock("/mock/generic.ac", "define identity<T>(value: T) -> T { value }\ntype Thing: axiom\nlet thing: Thing = axiom\nclass Thing {\n define keep<T>(self, value: T) -> T { value }\n}");
    project.mock(
        "/mock/main.ac",
        &format!("import generic\ntheorem goal {{ {expression} }}"),
    );
    let id = project.expect_ok("main");
    let env = project.get_env_by_id(id).unwrap();
    let nodes: Vec<_> = env.iter_goals().collect();
    assert_eq!(nodes.len(), 1);
    let node = &nodes[0];
    let context = node.goal_context().unwrap();
    context.goal.value().validate().unwrap();
    let mut prover = Prover::new(&project, false);
    for fact in node.usable_facts(&project) {
        fact.value.validate().unwrap();
        prover.add_fact(fact);
    }
    prover.set_goal(&context);
    assert_eq!(
        prover.quick_verification_search(),
        expected,
        "{expression}: {:?}",
        prover.error
    );
}

#[test]
fn qualified_and_grouped_generic_function_heads_still_infer() {
    for (head, args) in [
        ("generic.identity", "true"),
        ("(generic.identity)", "true"),
        ("generic.Thing.keep", "generic.thing, true"),
        ("(generic.Thing.keep)", "generic.thing, true"),
    ] {
        prove_goal(&format!("{head}({args}) = true"), Outcome::Success);
        prove_goal(&format!("{head}({args}) = false"), Outcome::Exhausted);
    }
}
