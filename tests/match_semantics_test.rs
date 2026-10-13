// Modified for Venticorn: validate match expressions before proof normalization.
use venticorn::environment::Environment;
use venticorn::project::Project;
use venticorn::token::Token;

fn add(env: &mut Environment, text: &str) -> Result<(), String> {
    env.add_tokens(&mut Project::new_mock(), Token::scan(text))
        .map_err(|error| error.to_string())
}

#[test]
fn structure_constructor_match_reaches_the_evaluation_boundary() {
    let mut env = Environment::new_test();
    env.add("structure Foo {\n bar: Bool\n }\n");
    let text = "define foo(f: Foo) -> Bool { match f { Foo.new(b) { b } } }";
    let error = add(&mut env, text).expect_err("match evaluation is not enabled yet");
    assert!(
        error.contains("match expression evaluation is not supported yet"),
        "{error}"
    );
}

#[test]
fn duplicate_names_in_one_match_pattern_are_rejected() {
    let mut env = Environment::new_test();
    env.add("inductive Foo {\n bar(Bool, Bool)\n }\n");
    let error = add(
        &mut env,
        "define foo(f: Foo) -> Bool { match f { Foo.bar(b, b) { b } } }",
    )
    .unwrap_err();
    assert!(
        error.contains("cannot use a name twice in one pattern"),
        "{error}"
    );
    assert!(!env.bindings.has_identifier("b"));
}
