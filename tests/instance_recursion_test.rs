use venticorn::acorn_type::Typeclass;
use venticorn::environment::Environment;
use venticorn::project::Project;
use venticorn::statement::Statement;

#[test]
fn unpublished_instance_members_cannot_recurse_or_escape() {
    let setup = "typeclass T: Walk {\n walk: T -> T\n}\ninductive Nat {\n zero\n suc(Nat)\n}\ndefine apply(f: Nat -> Nat, n: Nat) -> Nat { f(n) }";
    for (body, expected) in [
        (
            "match self { Nat.zero { Nat.zero } Nat.suc(pred) { Nat.Walk.walk(pred) } }",
            "Nat has no member named 'Walk'",
        ),
        ("Nat.Walk.walk(self)", "Nat has no member named 'Walk'"),
        (
            "apply(Nat.Walk.walk, self)",
            "Nat has no member named 'Walk'",
        ),
        ("Walk.walk<Nat>(self)", "does not satisfy"),
    ] {
        let mut env = Environment::new_test();
        env.add(setup);
        let class = Typeclass {
            module_id: env.module_id,
            name: "Walk".into(),
        };
        let nodes = env.nodes.len();
        let line = env.last_line();
        let scope = env.bindings.proof_scope().clone();
        let statement = Statement::parse_str(&format!(
            "instance Nat: Walk {{\n define walk(self) -> Nat {{ {body} }}\n}}"
        ))
        .unwrap();
        let error = env
            .add_statement(&mut Project::new_mock(), &statement)
            .unwrap_err();
        assert!(error.message().contains(expected), "{body}: {error}");
        assert_eq!(env.nodes.len(), nodes);
        assert_eq!(env.last_line(), line);
        assert_eq!(env.bindings.proof_scope(), &scope);
        assert!(!env.bindings.name_in_use("Nat.Walk.walk"));
        assert!(!env
            .bindings
            .proof_scope()
            .has_membership(env.module_id, "Nat", &class));
        env.add("instance Nat: Walk {\n define walk(self) -> Nat { self }\n}");
        assert!(env
            .bindings
            .proof_scope()
            .has_membership(env.module_id, "Nat", &class));
        assert!(env.bindings.get_constant_value("Nat.Walk.walk").is_some());
    }
}
