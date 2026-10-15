use venticorn::environment::Environment;
use venticorn::expression::Expression;
use venticorn::project::Project;

const PAIR: &str = "structure Pair<T, U> {\n first: T\n second: U\n}\n";

#[test]
fn instantiated_type_heads_specialize_members_and_aliases() {
    let mut env = Environment::new_test();
    env.add(PAIR);
    env.add("type Item: axiom\nlet item: Item = axiom\ntype Concrete: Pair<Item, Bool>");
    env.add("let p1: Pair<Item, Bool> = Pair.new(item, true)");
    env.add("let p2: Pair<Item, Bool> = Pair<Item, Bool>.new(item, true)");
    env.add("let p3: Pair<Item, Bool> = Pair.new<Item, Bool>(item, true)");
    env.add("let p4: Concrete = Concrete.new(item, true)");
    env.add("let make: (Item, Bool) -> Concrete = Concrete.new");
    env.bad("let bad: Concrete = Pair<Bool, Item>.new(item, true)");
    env.bad("let bad: Concrete = Concrete.new<Bool, Item>(item, true)");
    env.bad("let bad: Concrete = Pair<Item>.new(item, true)");
    env.bad("let bad: Concrete = Pair<Item, Bool>.new(item)");
    env.bad("let bad: Concrete = Pair<Item, Bool>.0");
    let project = Project::new_mock();
    for input in [
        "Pair<Item, Bool>.new",
        "Pair<Item, Bool>.new(item, true)",
        "Concrete.first(p1)",
    ] {
        let value = env
            .bindings
            .evaluate_value(&project, &Expression::expect_value(input), None)
            .unwrap();
        value.validate().unwrap();
        let code = env.bindings.value_to_code(&value).unwrap();
        let replay = env
            .bindings
            .evaluate_value(&project, &Expression::expect_value(&code), None)
            .unwrap();
        assert_eq!(value, replay, "{input} rendered as {code}");
    }
}

#[test]
fn instantiated_member_heads_preserve_phantom_parameters_and_module_identity() {
    let mut project = Project::new_mock();
    project.mock(
        "/mock/dependency.ac",
        "structure Marker<T, U> {\n value: Bool\n}",
    );
    project.mock(
        "/mock/main.ac",
        "import dependency\nstructure Marker<T, U> {\n value: Bool\n}",
    );
    let id = project.expect_ok("main");
    let env = project.get_env_by_id(id).unwrap();
    let mut values = vec![];
    for input in [
        "dependency.Marker<Bool, Bool>.new(true)",
        "dependency.Marker<Bool, Bool -> Bool>.new(true)",
        "Marker<Bool, Bool>.new(true)",
    ] {
        let value = env
            .bindings
            .evaluate_value(&project, &Expression::expect_value(input), None)
            .unwrap();
        let code = env.bindings.value_to_code(&value).unwrap();
        let replay = env
            .bindings
            .evaluate_value(&project, &Expression::expect_value(&code), None)
            .unwrap();
        assert_eq!(value, replay, "{input} rendered as {code}");
        values.push(value);
    }
    assert_ne!(values[0], values[1]);
    assert_ne!(values[0], values[2]);
}
