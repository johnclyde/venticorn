// Modified for Venticorn: aliases retain canonical identity, including constructor metadata.
use venticorn::environment::Environment;
use venticorn::project::Project;
use venticorn::statement::Statement;

#[test]
fn local_aliases_preserve_constructor_identity_only() {
    let mut env = Environment::new_test();
    env.add("inductive Nat {\n zero\n suc(Nat)\n}");
    env.add("let z: Nat = Nat.zero\n let s: Nat -> Nat = Nat.suc");
    env.add("define previous(n: Nat) -> Nat { match n { z { z } s(pred) { pred } } }");
    env.add("define id(n: Nat) -> Nat { n }\n let ordinary: Nat -> Nat = id");
    let statement = Statement::parse_str("define bad(n: Nat) -> Nat { match n { z { z } ordinary(pred) { pred } } }").unwrap();
    let error = env.add_statement(&mut Project::new_mock(), &statement).unwrap_err();
    assert!(error.to_string().contains("expected a constructor"));
}
