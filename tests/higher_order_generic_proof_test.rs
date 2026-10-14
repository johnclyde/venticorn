// Modified for Venticorn: higher-order generic definitions preserve theorem scopes.
use venticorn::project::Project;
use venticorn::prover::{Outcome, Prover};

const DEFINITIONS: &str = r#"
define is_surjective<T, U>(f: T -> U) -> Bool {
    forall(y: U) {
        exists(x: T) { f(x) = y }
    }
}

define identity<T>(x: T) -> T { x }
"#;

#[test]
fn identity_is_surjective_with_same_or_distinct_formal_names() {
    // Both generic definitions must instantiate at the theorem's opaque type.
    // Renaming that type must neither change the proof nor capture a definition's formals.
    for name in ["T", "V"] {
        for (negation, expected) in [("", Outcome::Success), ("not ", Outcome::Exhausted)] {
            let source = format!(
                "{DEFINITIONS}\ntheorem identity_is_surjective<{name}> {{ {negation}is_surjective(identity<{name}>) }}"
            );
            let mut project = Project::new_mock();
            project.mock("/mock/main.ac", &source);
            let id = project.expect_ok("main");
            let env = project.get_env_by_id(id).unwrap();
            let nodes = env.iter_goals().collect::<Vec<_>>();
            assert_eq!(nodes.len(), 1);
            for node in nodes {
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
                    "{source}\n{:?}",
                    prover.error
                );
            }
        }
    }
}
