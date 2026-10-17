// Modified for Venticorn: exercise explicit generic arguments through real proof search.
use venticorn::environment::Environment;
use venticorn::project::Project;
use venticorn::prover::{Outcome, Prover};

fn prove(source: &str) -> Outcome {
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", source);
    let id = project.expect_ok("main");
    let env = project.get_env_by_id(id).unwrap();
    let node = env.get_node_by_name("goal");
    let context = node.goal_context().unwrap();
    context.goal.value().validate().unwrap();
    let mut prover = Prover::new(&project, false);
    for fact in node.usable_facts(&project) {
        fact.value.validate().unwrap();
        prover.add_fact(fact);
    }
    prover.set_goal(&context);
    let outcome = prover.quick_verification_search();
    assert_ne!(outcome, Outcome::Error, "{:?}\n{source}", prover.error);
    outcome
}

const DEFINITIONS: &str = r#"
    inductive Item {
        one
        two
    }
    define identity<T>(value: T) -> T { value }
    define first<T, U>(left: T, right: U) -> T { left }
    define phantom<T>(flag: Bool) -> Bool { flag }
    define truth<T> -> Bool { true }
    define lie<T> -> Bool { false }
    define witness<T> -> T { axiom }
"#;

#[test]
fn explicit_arguments_preserve_order_partial_application_and_unused_parameters() {
    for goal in [
        "first<Item, Bool>(Item.one, true) = Item.one",
        "(identity)<Bool>(true)",
        "first<Bool, Item>(true, Item.one) = true",
        "first<Item, Item>(Item.one, Item.two) = Item.one",
        "first<Item, Bool>(Item.one)(true) = Item.one",
        "identity<(Bool -> Bool)>(identity<Bool>)(true) = true",
        "phantom<Item>(true)",
        "truth<Item>",
        "witness<Item> = witness<Item>",
    ] {
        assert_eq!(
            prove(&format!("{DEFINITIONS}\ntheorem goal {{ {goal} }}")),
            Outcome::Success,
            "{goal}"
        );
    }
    for goal in ["first<Item, Bool>(Item.one, true) = Item.two", "lie<Item>"] {
        assert_eq!(
            prove(&format!("{DEFINITIONS}\ntheorem goal {{ {goal} }}")),
            Outcome::Exhausted,
            "{goal}"
        );
    }
}

#[test]
fn explicit_arguments_reject_wrong_counts_types_and_pending_values() {
    let mut env = Environment::new_test();
    env.add(DEFINITIONS);
    for statement in [
        "let bad: Bool = identity<Bool, Bool>(true)",
        "let bad: Bool = identity<Bool><Bool>(true)",
        "let bad: Bool = phantom(true)",
        "let bad: Item = witness",
        "let bad: Item = first<Item, Bool>(true, true)",
        "let bad: Bool = first<Item, Bool>(Item.one)",
        "let bad: Bool = identity<Bool>",
        "let bad: Bool = truth<Bool, Bool>",
        "let bad: Bool = true<Bool>",
    ] {
        env.bad(statement);
    }
}

#[test]
fn qualified_explicit_calls_resolve_in_the_defining_module() {
    let mut project = Project::new_mock();
    project.mock(
        "/mock/dependency.ac",
        "define identity<T>(value: T) -> T { value }",
    );
    project.mock(
        "/mock/main.ac",
        "import dependency\ntheorem goal { dependency.identity<Bool>(true) }",
    );
    let id = project.expect_ok("main");
    let node = project.get_env_by_id(id).unwrap().get_node_by_name("goal");
    let mut prover = Prover::new(&project, false);
    for fact in node.usable_facts(&project) {
        prover.add_fact(fact);
    }
    prover.set_goal(&node.goal_context().unwrap());
    assert_eq!(
        prover.quick_verification_search(),
        Outcome::Success,
        "{:?}",
        prover.error
    );
}

#[test]
fn no_argument_member_definitions_are_rejected_before_class_type_indexing() {
    for definition in [
        "define missing -> Bool { true }",
        "define missing<T> -> T { axiom }",
    ] {
        let mut project = Project::new_mock();
        project.mock(
            "/mock/main.ac",
            &format!("type Item: axiom\nclass Item {{ {definition} }}"),
        );
        let errors = project.errors();
        assert_eq!(errors.len(), 1);
        assert!(errors[0]
            .1
            .message()
            .contains("must have a 'self' argument"));
        assert_eq!(errors[0].1.range().start.line, 1);
        assert_eq!(
            errors[0].1.range().end.character - errors[0].1.range().start.character,
            7
        );
    }
}

#[test]
fn qualified_generic_heads_do_not_resolve_to_same_named_local_arguments() {
    for body in [
        "dependency.identity<Bool>(true)",
        "dependency.identity(true)",
    ] {
        for (goal, expected) in [
            ("call(true)", Outcome::Success),
            ("not call(true)", Outcome::Exhausted),
        ] {
            let mut project = Project::new_mock();
            project.mock(
                "/mock/dependency.ac",
                "define identity<T>(value: T) -> T { value }",
            );
            project.mock("/mock/main.ac", &format!("import dependency\ndefine call(identity: Bool) -> Bool {{ {body} }}\ntheorem goal {{ {goal} }}"));
            let id = project.expect_ok("main");
            let node = project.get_env_by_id(id).unwrap().get_node_by_name("goal");
            let mut prover = Prover::new(&project, false);
            for fact in node.usable_facts(&project) {
                prover.add_fact(fact);
            }
            prover.set_goal(&node.goal_context().unwrap());
            assert_eq!(
                prover.quick_verification_search(),
                expected,
                "{:?}",
                prover.error
            );
        }
    }
}

#[test]
fn class_qualified_generics_support_explicit_arguments_and_keep_instance_limits() {
    let definitions = r#"
        type Thing: axiom
        let thing: Thing = axiom
        class Thing {
            define keep<T>(self, value: T) -> T { value }
        }
    "#;
    for call in [
        "Thing.keep<Bool>(thing, true)",
        "Thing.keep(thing, true)",
        "Thing.keep<Bool>(thing)(true)",
    ] {
        assert_eq!(
            prove(&format!("{definitions}\ntheorem goal {{ {call} }}")),
            Outcome::Success
        );
        assert_eq!(
            prove(&format!("{definitions}\ntheorem goal {{ not {call} }}")),
            Outcome::Exhausted
        );
    }
    let mut env = Environment::new_test();
    env.add(definitions);
    env.bad("let bad: Bool = thing.keep(true)");
    env.bad("let bad: Bool = thing.keep<Bool>(true)");
}

fn verify_all(source: &str) -> Outcome {
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", source);
    let id = project.expect_ok("main");
    for node in project.get_env_by_id(id).unwrap().iter_goals() {
        let mut prover = Prover::new(&project, false);
        for fact in node.usable_facts(&project) {
            prover.add_fact(fact);
        }
        prover.set_goal(&node.goal_context().unwrap());
        let outcome = prover.quick_verification_search();
        assert_ne!(outcome, Outcome::Error, "{:?}", prover.error);
        if outcome != Outcome::Success {
            return outcome;
        }
    }
    Outcome::Success
}

#[test]
fn generated_phantom_witness_keeps_explicit_arguments_and_replays() {
    let source = r#"
        type Item: axiom
        let three: Item = axiom
        let mul: (Item, Item) -> Item = axiom
        define marker<T> -> Item { axiom }
        define threeven(n: Item) -> Bool {
            exists(d: Item) { mul(three, d) = n }
        }
        axiom mul_marker_right(a: Item, b: Item) {
            b = marker<Bool> -> mul(a, b) = marker<Bool>
        }
        theorem goal { threeven(marker<Bool>) }
    "#;
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", source);
    let id = project.expect_ok("main");
    let env = project.get_env_by_id(id).unwrap();
    let node = env.get_node_by_name("goal");
    let mut prover = Prover::new(&project, false);
    for fact in node.usable_facts(&project) {
        prover.add_fact(fact);
    }
    prover.set_goal(&node.goal_context().unwrap());
    assert_eq!(prover.quick_search(), Outcome::Success);
    let code = prover
        .get_and_print_proof()
        .unwrap()
        .to_code(&env.bindings)
        .unwrap();
    assert!(
        !code.is_empty(),
        "a nonempty witness proof must be generated"
    );
    assert!(code.join("\n").contains("marker<Bool>"), "{code:?}");
    let replay = format!("{} by {{\n{}\n}}", source.trim_end(), code.join("\n"));
    assert_eq!(verify_all(&replay), Outcome::Success);
    let false_body = format!(
        "{} by {{ exists(x: Item) {{ x != x }} }}",
        source.trim_end()
    );
    assert_eq!(verify_all(&false_body), Outcome::Exhausted);
}

#[test]
fn explicit_instance_codegen_roundtrips_functions_members_and_phantom_types() {
    use venticorn::expression::Expression;
    let mut env = Environment::new_test();
    env.add(
        r#"
        type Item: axiom
        let item: Item = axiom
        define identity<T>(x: T) -> T { x }
        define first<T,U>(x: T,y: U) -> T { x }
        define marker<T> -> Item { axiom }
        class Item { define keep<T>(self, x: T) -> T { x } }
    "#,
    );
    let project = Project::new_mock();
    for input in [
        "marker<Bool>",
        "marker<(Bool -> Bool) -> Bool>",
        "identity<Bool>",
        "first<Item,Bool>(item)",
        "Item.keep<Bool>(item,true)",
        "Item.keep<Bool>(item)",
        "identity<(Bool -> Bool)>(identity<Bool>)",
        "identity<(Bool -> Bool)>(identity<Bool>, true)",
    ] {
        let value = env
            .bindings
            .evaluate_value(&project, &Expression::expect_value(input), None)
            .unwrap();
        let code = env.bindings.value_to_code(&value).unwrap();
        let replay = env
            .bindings
            .evaluate_value(&project, &Expression::expect_value(&code), None)
            .unwrap_or_else(|e| panic!("{input} rendered as {code}: {e}"));
        assert_eq!(value, replay, "{input} rendered as {code}");
    }
}

#[test]
fn phantom_arguments_distinguish_instances_with_the_same_value_type() {
    let declarations = "type Item: axiom\ndefine marker<T> -> Item { axiom }";
    assert_eq!(
        prove(&format!(
            "{declarations}\ntheorem goal {{ marker<Bool> = marker<Bool> }}"
        )),
        Outcome::Success
    );
    assert_eq!(
        prove(&format!(
            "{declarations}\ntheorem goal {{ marker<Bool> = marker<Item> }}"
        )),
        Outcome::Exhausted
    );
}

#[test]
fn explicit_generic_constructor_arguments_follow_the_constructor_name() {
    let mut env = Environment::new_test();
    env.add(
        r#"
            type Foo: axiom
            type Bar: axiom
            structure Pair<T, U> {
                first: T
                second: U
            }
            let f: Foo = axiom
            let b: Bar = axiom
            let p1: Pair<Foo, Bar> = Pair.new(f, b)
            let p2: Pair<Foo, Bar> = Pair<Foo, Bar>.new(f, b)
            "#,
    );
    env.add(
        r#"
            let p3: Pair<Foo, Bar> = Pair.new<Foo, Bar>(f, b)
            "#,
    );
    let expected = env.bindings.get_constant_value("p1").unwrap().get_type();
    for name in ["p2", "p3"] {
        assert_eq!(
            env.bindings.get_constant_value(name).unwrap().get_type(),
            expected
        );
    }
}
