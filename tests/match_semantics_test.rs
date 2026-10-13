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
