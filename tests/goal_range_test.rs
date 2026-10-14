// Modified for Venticorn: whole-goal coverage includes explicit and implicit proof blocks.
use venticorn::module::ModuleRef;
use venticorn::project::Project;

fn ranges(source: &str) -> Vec<(u32, u32, u32)> {
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", source);
    project.expect_ok("main");
    project
        .get_env_by_ref(&ModuleRef::Name("main".to_string()))
        .unwrap()
        .iter_goals()
        .map(|node| {
            let context = node.goal_context().unwrap();
            (
                context.first_line,
                context.last_line,
                context.proof_insertion_line,
            )
        })
        .collect()
}

#[test]
fn full_goal_bounds_include_the_header_and_proof_block() {
    assert_eq!(
        ranges("theorem simple { true }\ntheorem outer {\n true\n} by {\n true\n}\n"),
        vec![(0, 0, 0), (4, 4, 4), (1, 5, 5)]
    );
}

#[test]
fn implicit_and_anonymous_multiline_goals_keep_their_full_bounds() {
    assert_eq!(ranges("theorem {\n true\n}\n"), vec![(0, 2, 2)]);
}
