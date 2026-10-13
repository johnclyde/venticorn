// Modified for Venticorn: recursion must be rejected until its safety checks are available.
use venticorn::environment::Environment;
use venticorn::project::Project;
use venticorn::statement::Statement;

fn naturals() -> Environment {
    let mut env = Environment::new_test();
    env.add("inductive Nat {\n zero\n suc(Nat)\n}");
    env
}

fn reject(env: &mut Environment, text: &str) {
    let statement = Statement::parse_str(text).expect("recursion fixture must parse");
    assert!(env.add_statement(&mut Project::new_mock(), &statement).is_err());
}

#[test]
fn left_recursive_definition_is_guarded() {
    let mut env = naturals();
    reject(&mut env, r#"
        define add(a: Nat, b: Nat) -> Nat {
            match a {
                Nat.zero { b }
                Nat.suc(pred) { add(pred, b).suc }
            }
        }
    "#);
    assert!(!env.bindings.has_identifier("add"));
}

#[test]
fn right_recursive_definition_is_guarded() {
    let mut env = naturals();
    reject(&mut env, r#"
        define add(a: Nat, b: Nat) -> Nat {
            match b {
                Nat.zero { a }
                Nat.suc(pred) { add(a, pred).suc }
            }
        }
    "#);
    assert!(!env.bindings.has_identifier("add"));
}

#[test]
fn unchanged_recursive_arguments_are_rejected() {
    let mut env = naturals();
    reject(&mut env, r#"
        define loop(a: Nat, b: Nat) -> Nat {
            match a {
                Nat.zero { b }
                Nat.suc(pred) { loop(a, b) }
            }
        }
    "#);
    assert!(!env.bindings.has_identifier("loop"));
}

#[test]
fn alternating_argument_decreases_do_not_prove_termination() {
    let mut env = naturals();
    reject(&mut env, r#"
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
    "#);
}

#[test]
fn contradictory_self_recursion_is_rejected() {
    let mut env = Environment::new_test();
    reject(&mut env, "define loop(a: Bool) -> Bool { not loop(a) }");
    assert!(!env.bindings.has_identifier("loop"));
}
