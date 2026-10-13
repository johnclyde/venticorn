// Modified for Venticorn: check match diagnostics before enabling proof lowering.
use venticorn::environment::Environment;
use venticorn::project::Project;
use venticorn::token::Token;

fn environment() -> Environment {
    let mut env = Environment::new_test();
    env.add("inductive Foo {\n bar(Bool)\n baz(Bool)\n }\n");
    env
}

fn error_for(env: &mut Environment, code: &str) -> String {
    env.add_tokens(&mut Project::new_mock(), Token::scan(code))
        .expect_err("this match must be rejected")
        .to_string()
}

#[test]
fn match_pattern_return_type_must_match_scrutinee() {
    let mut env = environment();
    env.add("define wrong(b: Bool) -> Bool { b }");
    let error = error_for(
        &mut env,
        "define f(v: Foo) -> Bool { match v { wrong(b) { b } } }",
    );
    assert!(
        error.contains("pattern type does not match scrutinee"),
        "{error}"
    );
}

#[test]
fn match_requires_function_patterns_until_nullary_binding_is_available() {
    let mut env = environment();
    let error = error_for(
        &mut env,
        "define f(v: Foo) -> Bool { match v { true { false } } }",
    );
    assert!(error.contains("invalid match pattern"), "{error}");
}

#[test]
fn match_constructor_arity_is_checked_before_names_are_bound() {
    let mut env = environment();
    let error = error_for(
        &mut env,
        "define f(v: Foo) -> Bool { match v { Foo.bar(x, y) { x } } }",
    );
    assert!(error.contains("expected 1 arguments but got 2"), "{error}");
}

#[test]
fn match_case_body_errors_do_not_make_binding_names_leak() {
    let mut env = environment();
    let error = error_for(
        &mut env,
        "define f(v: Foo) -> Bool { match v { Foo.bar(local) { missing } } }",
    );
    assert!(error.contains("missing"), "{error}");
    assert!(!env.bindings.has_identifier("local"));
    env.add("let local: Bool = true");
}
