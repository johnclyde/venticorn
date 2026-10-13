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

#[test]
fn distinct_match_cases_can_reuse_local_binding_names() {
    let mut env = Environment::new_test();
    env.add("inductive Foo {\n first(Bool)\n second(Bool)\n }\n");
    let text = "define foo(f: Foo) -> Bool { match f { Foo.first(b) { b } Foo.second(b) { b } } }";
    let error = add(&mut env, text).expect_err("match evaluation is not enabled yet");
    assert!(
        error.contains("match expression evaluation is not supported yet"),
        "{error}"
    );
    assert!(!env.bindings.has_identifier("b"));
    env.add("let b: Bool = true");
}

#[test]
fn match_case_names_cannot_shadow_enclosing_arguments() {
    let mut env = Environment::new_test();
    env.add("inductive Foo {\n bar(Bool)\n }\n");
    let error = add(
        &mut env,
        "define foo(f: Foo, b: Bool) -> Bool { match f { Foo.bar(b) { b } } }",
    )
    .unwrap_err();
    assert!(error.contains("name b already bound"), "{error}");
}

#[test]
fn a_constructor_case_cannot_be_repeated_after_coverage_is_complete() {
    let mut env = Environment::new_test();
    env.add("inductive Foo {\n bar(Bool)\n baz\n }\n");
    let error = add(&mut env, "define foo(f: Foo) -> Bool { match f { Foo.bar(b) { b } Foo.baz { false } Foo.bar(b) { b } } }").unwrap_err();
    assert!(
        error.contains("cannot have multiple cases for the same constructor"),
        "{error}"
    );
    assert!(!env.bindings.has_identifier("b"));
}
