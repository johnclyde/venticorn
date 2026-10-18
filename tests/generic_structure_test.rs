use venticorn::environment::Environment;
use venticorn::expression::Expression;
use venticorn::project::Project;
use venticorn::prover::{Outcome, Prover};

const PAIR: &str = "structure Pair<T, U> {\n first: T\n second: U\n}\n";
const TAGGED: &str = "structure Tagged<T, U> {\n value: T\n}\n";

fn prove(source: &str) -> (Outcome, Vec<String>) {
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", source);
    let id = project.expect_ok("main");
    let env = project.get_env_by_id(id).unwrap();
    let node = env.get_node_by_name("goal");
    let mut prover = Prover::new(&project, false);
    for fact in node.usable_facts(&project) {
        fact.value.validate().unwrap();
        prover.add_fact(fact);
    }
    let context = node.goal_context().unwrap();
    context.goal.value().validate().unwrap();
    prover.set_goal(&context);
    let outcome = prover.quick_search();
    let code = if outcome == Outcome::Success {
        prover
            .get_and_print_proof()
            .unwrap()
            .to_code(&env.bindings)
            .unwrap()
    } else {
        vec![]
    };
    (outcome, code)
}

#[test]
fn generic_structure_declarations_reuse_names_without_leaking_scope() {
    let mut env = Environment::new_test();
    env.add(PAIR);
    env.add(&PAIR.replace("Pair", "Other"));
    env.add(TAGGED);
    env.bad("structure T<Pair, U> {\n first: Pair\n second: U\n}");
    assert!(!env.bindings.has_type_name("T"));
    assert!(!env.bindings.has_type_name("U"));
    env.add("type Item: axiom\nlet item: Item = axiom");
    env.add("let pair: Pair<Item, Bool> = Pair.new(item, true)");
    env.add("let tag: Tagged<Item, Bool> = Tagged.new<Item, Bool>(item)");
    env.add("let first: Item = Pair.first(pair)");
    env.bad("let bad: Pair<Bool, Item> = pair");
    env.add("type BoolPair: Pair<Bool, Bool>");
    env.bad("let bad: Pair<Item, Bool> = BoolPair.new(item, true)");
    env.bad("let bad: Tagged<Item, Bool> = Tagged.new(item)");
    env.bad("numerals Pair<Bool, Bool>");
}

#[test]
fn failed_generic_declarations_restore_bindings_and_facts() {
    for source in [
        "structure Broken<T, T> {\n value: T\n}",
        "structure Broken<T> {\n value: Missing\n}",
        "structure Broken<T> {\n new: T\n}",
        "structure Broken<T> {\n value: T\n value: T\n}",
        "structure Broken<T> {\n value: T\n} constraint { missing }",
    ] {
        let mut env = Environment::new_test();
        env.add("let keep: Bool = true");
        let nodes = env.nodes.len();
        env.bad(source);
        assert_eq!(env.nodes.len(), nodes, "{source}");
        assert!(!env.bindings.has_type_name("T"));
        assert!(!env.bindings.has_type_name("Broken"));
        assert!(!env.bindings.has_identifier("Broken.new"));
        assert!(env.bindings.has_identifier("keep"));
        env.add("structure Broken<T> {\n value: T\n}");
    }
}

#[test]
fn generic_structure_values_round_trip_order_aliases_and_functional_actuals() {
    let mut env = Environment::new_test();
    env.add(PAIR);
    env.add(TAGGED);
    env.add(
        "type Item: axiom\nlet item: Item = axiom\ndefine identity<T>(value: T) -> T { value }",
    );
    env.add("type Left: Pair<Item, Bool>\ntype Right: Pair<Bool, Item>");
    let project = Project::new_mock();
    for input in [
        "Pair.new<Item, Bool>(item, true)",
        "Pair.new<Bool, Item>(true, item)",
        "Tagged.new<Item, (Bool -> Bool) -> Bool>(item)",
        "Pair.new<Pair<Item, Bool>, Bool>(Pair.new(item, true), true)",
        "function(x: Left) { x }",
        "function(x: Right) { x }",
        "function(x: Tagged<Item, (Bool -> Bool) -> Bool>) { x }",
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
fn qualified_generic_datatype_code_round_trips_without_local_capture() {
    let mut project = Project::new_mock();
    project.mock("/mock/dependency.ac", PAIR);
    project.mock(
        "/mock/main.ac",
        "import dependency\ntype Item: axiom\nlet item: Item = axiom",
    );
    let id = project.expect_ok("main");
    let env = project.get_env_by_id(id).unwrap();
    for input in [
        "dependency.Pair.new<Item, Bool>(item, true)",
        "function(x: dependency.Pair<Item, Bool>) { x }",
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
    }
}

#[test]
fn generic_structure_equations_prove_and_reject_distinct_constructors() {
    let prefix = format!("{PAIR}{TAGGED}inductive Item {{\n one\n two\n}}\n");
    for claim in [
        "Pair.first(Pair.new(Item.one, true)) = Item.one",
        "Pair.second(Pair.new(Item.one, true)) = true",
        "Tagged.value(Tagged.new<Item, Bool>(Item.one)) = Item.one",
    ] {
        assert_eq!(
            prove(&format!("{prefix}theorem goal {{ {claim} }}")).0,
            Outcome::Success,
            "{claim}"
        );
    }
    assert_eq!(
        verify_all(&format!(
            "{prefix}theorem goal {{ Pair.first(Pair.new(Item.one, true)) = Item.two }}"
        )),
        Outcome::Exhausted
    );
}

fn verify_all(source: &str) -> Outcome {
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", source);
    let id = project.expect_ok("main");
    for node in project.get_env_by_id(id).unwrap().iter_goals() {
        let mut prover = Prover::new(&project, false);
        for fact in node.usable_facts(&project) {
            fact.value.validate().unwrap();
            prover.add_fact(fact);
        }
        prover.set_goal(&node.goal_context().unwrap());
        let outcome = prover.quick_verification_search();
        assert!(
            !matches!(outcome, Outcome::Error(_)),
            "{:?}",
            prover.error()
        );
        if outcome != Outcome::Success {
            return outcome;
        }
    }
    Outcome::Success
}

#[test]
fn generated_generic_structure_witness_proof_replays_with_a_false_control() {
    for actual in ["Bool", "(Bool -> Bool) -> Bool"] {
        for constraint in ["", " constraint { value }"] {
            let source = format!(
                "structure Marker<T> {{\n value: Bool\n}}{constraint}\n\
                 let three: Marker<{actual}> = axiom\n\
                 let mul: (Marker<{actual}>, Marker<{actual}>) -> Marker<{actual}> = axiom\n\
                 define threeven(n: Marker<{actual}>) -> Bool {{\n\
                   exists(d: Marker<{actual}>) {{ mul(three, d) = n }}\n\
                 }}\n\
                 axiom marker_right(a: Marker<{actual}>, b: Marker<{actual}>) {{\n\
                   b = Marker.new<{actual}>(true) -> mul(a, b) = Marker.new<{actual}>(true)\n\
                 }}\n\
                 theorem goal {{ threeven(Marker.new<{actual}>(true)) }}"
            );
            let (outcome, code) = prove(&source);
            assert_eq!(outcome, Outcome::Success);
            assert!(!code.is_empty(), "witness proof must be nonempty");
            assert!(
                code.join("\n").contains("Marker.new<"),
                "phantom witness must preserve actuals: {code:?}"
            );
            let replay = format!("{source} by {{\n{}\n}}", code.join("\n"));
            assert_eq!(verify_all(&replay), Outcome::Success);
            let false_body = format!("{source} by {{ exists(p: Marker<{actual}>) {{ p != p }} }}");
            assert_eq!(verify_all(&false_body), Outcome::Exhausted);
        }
    }
}

#[test]
fn constrained_generic_facts_keep_the_constraint_and_fixed_outer_types() {
    let prefix = "structure Flagged<T> {\n flag: Bool\n} constraint { flag }\n";
    assert_eq!(
        verify_all(&format!(
            "{prefix}theorem goal(p: Flagged<Bool>) {{ Flagged.flag(p) }}"
        )),
        Outcome::Success
    );
    let source = format!("{prefix}theorem goal {{ Flagged.flag(Flagged.new<Bool>(true)) }}");
    assert_eq!(verify_all(&source), Outcome::Success);
    let negative = format!("{prefix}let off: Bool = axiom\naxiom off_is_false {{ not off }}\ntheorem goal {{ Flagged.flag(Flagged.new<Bool>(off)) = off }}");
    assert_eq!(verify_all(&negative), Outcome::Exhausted);

    let scoped = "theorem goal<A>(outer: A) { outer = outer } by {\n structure Local<U> {\n flag: Bool\n } constraint { outer = outer }\n outer = outer\n}";
    assert_eq!(verify_all(scoped), Outcome::Success);
    let false_constraint = scoped.replace(
        "constraint { outer = outer }",
        "constraint { outer != outer }",
    );
    assert_eq!(verify_all(&false_constraint), Outcome::Exhausted);
}

#[test]
fn unsupported_outer_type_signatures_restore_generic_structure_admission() {
    let mut env = Environment::new_test();
    env.bindings.add_arbitrary_type("Outer");
    let nodes = env.nodes.len();
    env.bad("structure Captured<T> {\n outer: Outer\n inner: T\n}");
    assert_eq!(env.nodes.len(), nodes);
    assert!(env.bindings.has_type_name("Outer"));
    assert!(!env.bindings.has_type_name("T"));
    assert!(!env.bindings.has_type_name("Captured"));
    assert!(!env.bindings.has_identifier("Captured.new"));
    env.add("structure Captured<T> {\n inner: T\n}");
}

#[test]
fn generic_instance_fields_infer_actuals_and_round_trip() {
    let mut env = Environment::new_test();
    env.add(PAIR);
    env.add(TAGGED);
    env.add("type Item: axiom\nlet item: Item = axiom");
    env.add("let pair: Pair<Item, Bool> = Pair.new(item, true)");
    env.add("let tagged: Tagged<Item, Bool> = Tagged.new<Item, Bool>(item)");
    env.add("type ItemPair: Pair<Item, Bool>\nlet alias: ItemPair = pair");
    let project = Project::new_mock();
    for input in ["pair.first", "pair.second", "tagged.value", "alias.first"] {
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
    env.bad("let wrong: Bool = pair.first");
    env.bad("let wrong: Item = pair.second");
    env.bad("let wrong: Item = pair.missing");
    let source = format!("{PAIR}inductive Item {{\n one\n two\n}}\nlet pair: Pair<Item, Bool> = Pair.new(Item.one, true)\ntheorem goal {{ pair.first = Item.one }}");
    assert_eq!(verify_all(&source), Outcome::Success);
    assert_eq!(
        verify_all(&source.replace("pair.first = Item.one", "pair.first = Item.two")),
        Outcome::Exhausted
    );
}

#[test]
fn standalone_generic_functions_keep_datatype_parameters_scoped() {
    let prefix = format!("{PAIR}inductive Item {{\n one\n two\n}}\ndefine flip<T, U>(p: Pair<T, U>) -> Pair<U, T> {{ Pair.new(p.second, p.first) }}\n");
    let mut env = Environment::new_test();
    env.add(&prefix);
    env.get_definition("flip").unwrap().validate().unwrap();
    assert!(!env.bindings.has_type_name("T"));
    assert!(!env.bindings.has_type_name("U"));
    assert_eq!(
        verify_all(&format!(
            "{prefix}theorem goal {{ flip(Pair.new(Item.one, true)).second = Item.one }}"
        )),
        Outcome::Success
    );
    assert_eq!(
        verify_all(&format!(
            "{prefix}theorem goal {{ flip(Pair.new(Item.one, true)).second = Item.two }}"
        )),
        Outcome::Exhausted
    );
}
