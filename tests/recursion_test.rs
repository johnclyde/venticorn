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
