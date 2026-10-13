// Modified for Venticorn: recursive definitions require a structural termination proof.
use venticorn::environment::Environment;
use venticorn::project::Project;
use venticorn::statement::Statement;

fn naturals() -> Environment {
    let mut env = Environment::new_test();
    env.add("inductive Nat {\n zero\n suc(Nat)\n}");
    env
}

fn reject_termination(env: &mut Environment, text: &str) {
    let statement = Statement::parse_str(text).expect("recursion fixture must parse");
    let error = env
        .add_statement(&mut Project::new_mock(), &statement)
        .unwrap_err();
    assert!(error.to_string().contains("termination checker"), "{error}");
}

#[test]
fn left_recursive_definition_terminates() {
    let mut env = naturals();
    env.add(
        r#"
        define add(a: Nat, b: Nat) -> Nat {
            match a {
                Nat.zero { b }
                Nat.suc(pred) { add(pred, b).suc }
            }
        }
    "#,
    );
    assert!(env.bindings.has_identifier("add"));
}

#[test]
fn right_recursive_definition_terminates() {
    let mut env = naturals();
    env.add(
        r#"
        define add(a: Nat, b: Nat) -> Nat {
            match b {
                Nat.zero { a }
                Nat.suc(pred) { add(a, pred).suc }
            }
        }
    "#,
    );
    assert!(env.bindings.has_identifier("add"));
}

#[test]
fn unchanged_recursive_arguments_are_rejected() {
    let mut env = naturals();
    reject_termination(
        &mut env,
        r#"
        define loop(a: Nat, b: Nat) -> Nat {
            match a {
                Nat.zero { b }
                Nat.suc(pred) { loop(a, b) }
            }
        }
    "#,
    );
    assert!(!env.bindings.has_identifier("loop"));
}

#[test]
fn alternating_argument_decreases_do_not_prove_termination() {
    let mut env = naturals();
    reject_termination(
        &mut env,
        r#"
        define loop(a: Nat, b: Nat, c: Bool) -> Bool {
            if c {
                match a {
                    Nat.zero { false }
                    Nat.suc(pred) { not loop(pred, b.suc, false) }
                }
            } else {
                match b {
                    Nat.zero { false }
                    Nat.suc(pred) { loop(a.suc, pred, true) }
                }
            }
        }
    "#,
    );
}

#[test]
fn contradictory_self_recursion_is_rejected() {
    let mut env = Environment::new_test();
    reject_termination(&mut env, "define loop(a: Bool) -> Bool { not loop(a) }");
    assert!(!env.bindings.has_identifier("loop"));
}

#[test]
fn recursive_function_name_cannot_collide_with_a_type_parameter() {
    let mut env = Environment::new_test();
    let statement = Statement::parse_str("define f<f>(x: f) -> f { x }").unwrap();
    let error = env
        .add_statement(&mut Project::new_mock(), &statement)
        .unwrap_err();
    assert!(error
        .to_string()
        .contains("function name conflicts with a type parameter"));
    assert!(!env.bindings.has_identifier("f"));
    assert!(!env.bindings.has_type_name("f"));
    env.add("define f(x: Bool) -> Bool { x }");
}

#[test]
fn failed_generic_declarations_do_not_leak_temporary_bindings() {
    let mut env = Environment::new_test();
    let statement =
        Statement::parse_str("define bad<T>(value: T) -> Bool { missing(value) }").unwrap();
    assert!(env
        .add_statement(&mut Project::new_mock(), &statement)
        .is_err());
    assert!(!env.bindings.has_identifier("bad"));
    assert!(!env.bindings.has_type_name("T"));
    env.add("define good<T>(value: T) -> T { value }");
    assert!(!env.bindings.has_type_name("T"));
}

#[test]
fn recursive_constructor_types_must_be_direct_fields() {
    for text in [
        "inductive Bad {\n node(Bad -> Bool)\n}",
        "inductive Bad {\n zero\n node(Bool -> Bad)\n}",
        "inductive Bad {\n zero\n node((Bad -> Bool) -> Bool)\n}",
    ] {
        let mut env = Environment::new_test();
        let statement = Statement::parse_str(text).unwrap();
        let error = env
            .add_statement(&mut Project::new_mock(), &statement)
            .unwrap_err();
        assert!(error
            .to_string()
            .contains("recursive constructor fields must use the inductive type directly"));
        assert!(!env.bindings.has_type_name("Bad"));
    }
    let mut env = naturals();
    env.add("inductive Safe {\n terminal(Bool -> Bool)\n next(Safe)\n}");
}

#[test]
fn recursive_function_cannot_escape_as_a_value() {
    let mut env = naturals();
    env.add("define apply(f: Nat -> Bool, n: Nat) -> Bool { f(n) }");
    reject_termination(
        &mut env,
        "define cheat(n: Nat) -> Bool { not apply(cheat, n) }",
    );
    assert!(!env.bindings.has_identifier("cheat"));
}

#[test]
fn generic_recursive_definitions_preserve_type_metadata() {
    let mut env = naturals();
    let statement = Statement::parse_str(
        r#"
        define repeat<T>(n: Nat, f: T -> T, a: T) -> T {
            match n {
                Nat.zero { a }
                Nat.suc(pred) { repeat(pred, f, f(a)) }
            }
        }
    "#,
    )
    .unwrap();
    env.add_statement(&mut Project::new_mock(), &statement)
        .unwrap();
    assert!(env.bindings.has_identifier("repeat"));
    env.get_definition("repeat").unwrap().validate().unwrap();
    assert!(!env.bindings.has_type_name("T"));
}

#[test]
fn higher_order_wrappers_do_not_hide_recursive_calls() {
    let mut env = naturals();
    env.add("define apply(f: Nat -> Bool, n: Nat) -> Bool { f(n) }");
    reject_termination(
        &mut env,
        "define cheat(n: Nat) -> Bool { not apply(function(k: Nat) { cheat(k) }, n) }",
    );
    assert!(!env.bindings.has_identifier("cheat"));
    reject_termination(&mut env, "define generic<T>(n: Nat, value: T) -> Bool { not apply(function(k: Nat) { generic(k, value) }, n) }");
    assert!(!env.bindings.has_identifier("generic"));
    assert!(!env.bindings.has_type_name("T"));
}

#[test]
fn reserved_todo_syntax_never_discharges_proof_obligations() {
    for (i, source) in [
        "todo\ntheorem goal { false }",
        "theorem goal { false } by { todo }",
        "define unfinished(b: Bool) -> Bool { todo }\ntheorem goal { false }",
    ]
    .iter()
    .enumerate()
    {
        let mut project = Project::new_mock();
        let name = format!("todo_case_{}", i);
        project.mock(&format!("/mock/{}.ac", name), source);
        let id = project.load_module_by_name(&name).unwrap();
        assert!(matches!(
            project.get_module_by_id(id),
            venticorn::module::Module::Error(_)
        ));
    }
}

#[test]
fn member_recursion_can_decrease_the_receiver() {
    let mut env = naturals();
    env.add(
        r#"
        class Nat {
            define add(self, other: Nat) -> Nat {
                match self {
                    Nat.zero { other }
                    Nat.suc(pred) { pred.add(other).suc }
                }
            }
        }
    "#,
    );
    assert!(env.bindings.has_identifier("Nat.add"));
}
