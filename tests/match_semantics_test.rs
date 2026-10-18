use venticorn::acorn_type::Class;
// Modified for Venticorn: validate match expressions before proof normalization.
use venticorn::environment::Environment;
use venticorn::project::Project;
use venticorn::token::Token;

fn add(env: &mut Environment, text: &str) -> Result<(), String> {
    env.add_tokens(&mut Project::new_mock(), Token::scan(text))
        .map_err(|error| error.to_string())
}

#[test]
fn structure_constructor_match_has_the_declared_type() {
    let mut env = Environment::new_test();
    env.add("structure Foo {\n bar: Bool\n }\n");
    let text = "define foo(f: Foo) -> Bool { match f { Foo.new(b) { b } } }";
    add(&mut env, text).unwrap();
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
    add(&mut env, text).unwrap();
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

#[test]
fn a_match_result_must_not_violate_the_declared_return_type() {
    let mut env = Environment::new_test();
    env.add("inductive Foo {\n bar\n }\n");
    add(
        &mut env,
        "define foo(f: Foo) -> Bool { match f { Foo.bar { Foo.bar } } }",
    )
    .expect_err("Foo result must not define a Boolean function");
    assert!(!env.bindings.has_identifier("foo"));
    env.add("let foo: Bool = true");
}

#[test]
fn inferred_match_result_types_must_agree_across_cases() {
    let mut env = Environment::new_test();
    env.add("inductive Foo {\n bar\n baz\n }\n");
    let error = add(
        &mut env,
        "theorem claim(f: Foo) { (match f { Foo.bar { true } Foo.baz { Foo.bar } }) = true }",
    )
    .unwrap_err();
    assert!(error.contains("expected type Bool"), "{error}");
    add(
        &mut env,
        "theorem claim(f: Foo) { (match f { Foo.bar { Foo.bar } Foo.baz { Foo.baz } }) = f }",
    )
    .unwrap();
}

#[test]
fn match_type_errors_restore_case_and_function_bindings() {
    let mut env = Environment::new_test();
    env.add("inductive Foo {\n bar(Bool)\n baz\n }\n");
    let error = add(
        &mut env,
        "define foo(f: Foo) -> Bool { match f { Foo.bar(b) { Foo.baz } Foo.baz { true } } }",
    )
    .unwrap_err();
    assert!(error.contains("expected type Bool"), "{error}");
    assert!(!env.bindings.has_identifier("b"));
    assert!(!env.bindings.has_identifier("f"));
    env.add("let b: Bool = true");
    env.add("let f: Foo = Foo.baz");
}

#[test]
fn malformed_match_values_report_validation_errors() {
    use venticorn::acorn_type::AcornType;
    use venticorn::acorn_value::AcornValue;
    let item_type = AcornType::Data(Class::new(0, "Item".to_string()), vec![]);
    let item = AcornValue::new_constant(0, "Item.empty".to_string(), vec![], item_type);
    let empty = AcornValue::Match(Box::new(item.clone()), vec![]);
    assert!(empty.validate().unwrap_err().contains("at least one case"));
    let inconsistent = AcornValue::Match(
        Box::new(item.clone()),
        vec![
            (vec![], item.clone(), AcornValue::Bool(true)),
            (vec![], item.clone(), item.clone()),
        ],
    );
    assert!(inconsistent
        .validate()
        .unwrap_err()
        .contains("same result type"));
    let wrong_pattern = AcornValue::Match(
        Box::new(item),
        vec![(vec![], AcornValue::Bool(true), AcornValue::Bool(false))],
    );
    assert!(wrong_pattern
        .validate()
        .unwrap_err()
        .contains("pattern has a different type"));
}
