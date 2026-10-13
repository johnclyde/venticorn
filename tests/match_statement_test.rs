// Modified for Venticorn.

use venticorn::environment::Environment;
use venticorn::project::Project;
use venticorn::statement::Statement;

fn fixture() -> Environment {
    let mut env = Environment::new_test();
    env.add("inductive Foo {\n    bar(Bool)\n    baz\n}");
    env.add("let f: Foo = axiom");
    env
}

#[test]
fn match_statements_report_unsupported_semantics_without_adding_nodes() {
    let mut env = fixture();
    let node_count = env.nodes.len();
    let statement =
        Statement::parse_str("match f {\n    Foo.bar(b) { b or not b }\n    Foo.baz { true }\n}")
            .unwrap();
    let error = env
        .add_statement(&mut Project::new_mock(), &statement)
        .unwrap_err();
    assert!(error
        .message
        .contains("match statements are not supported yet"));
    assert_eq!(env.nodes.len(), node_count);
    assert!(!env.bindings.has_identifier("b"));
}
