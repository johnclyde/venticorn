use venticorn::environment::Environment;
use venticorn::expression::Expression;
use venticorn::project::Project;
use venticorn::prover::{Outcome, Prover};

const PAIR: &str = "structure Pair<T, U> {\n first: T\n second: U\n}\n";
const SWAP: &str = "class Pair<T, U> {\n define swap(self) -> Pair<U, T> { Pair.new(self.second, self.first) }\n}\n";

#[test]
fn generic_class_methods_keep_ordered_class_parameters_and_return_types() {
    let mut env = Environment::new_test();
    env.add(PAIR);
    env.add(SWAP);
    env.add("type Foo: axiom\ntype Bar: axiom\nlet f: Foo = axiom\nlet b: Bar = axiom");
    env.add("let s: Pair<Foo, Bar> -> Pair<Bar, Foo> = Pair<Foo, Bar>.swap");
    env.add("let p1: Pair<Foo, Bar> = Pair.new(f, b)");
    env.add("let p2: Pair<Bar, Foo> = p1.swap");
    env.add("let p3: Pair<Foo, Bar> = p2.swap");
    env.add("let p4: Pair<Foo, Bar> = p1.swap.swap");
    assert!(!env.bindings.has_type_name("T"));
    assert!(!env.bindings.has_type_name("U"));
    env.add("class Pair<X, Y> {\n define same(self) -> Pair<X, Y> { self }\n define chosen(self) -> Y { axiom }\n}");
    env.add("let result: Bar = p1.chosen");
    assert!(!env.bindings.has_type_name("X"));
    assert!(!env.bindings.has_type_name("Y"));
    let project = Project::new_mock();
    for input in [
        "p1.swap",
        "p1.swap.swap",
        "Pair<Foo, Bar>.swap",
        "Pair.chosen<Foo, Bar>",
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
fn failed_generic_class_bodies_restore_members_facts_and_parameter_scope() {
    for body in [
        "define same(self) -> Pair<T, U> { self }\n define broken(self) -> Missing { axiom }",
        "define same(self) -> Pair<T, U> { self }\n define own<V>(self, value: V) -> V { value }",
        "define same(self) -> Pair<T, U> { self }\n let leaked: Missing = axiom",
        "define same(self) -> Pair<T, U> { self }\n define same(self) -> Pair<T, U> { self }",
    ] {
        let mut env = Environment::new_test();
        env.add(PAIR);
        let nodes = env.nodes.len();
        env.bad(&format!("class Pair<T, U> {{\n {body}\n}}"));
        assert_eq!(env.nodes.len(), nodes);
        assert!(!env.bindings.has_identifier("Pair.same"));
        assert!(!env.bindings.has_identifier("Pair.leaked"));
        assert!(!env.bindings.has_type_name("T"));
        assert!(!env.bindings.has_type_name("U"));
        env.add("class Pair<T, U> {\n define same(self) -> Pair<T, U> { self }\n}");
    }
    let mut env = Environment::new_test();
    env.add(PAIR);
    for text in [
        "class Pair<T> {}",
        "class Pair<T, U, V> {}",
        "class Pair<T, T> {}",
    ] {
        env.bad(text);
        assert!(!env.bindings.has_type_name("T"));
        assert!(!env.bindings.has_type_name("U"));
        assert!(!env.bindings.has_type_name("V"));
    }
    env.add("type Concrete: Pair<Bool, Bool>");
    env.bad("class Concrete {\n define same(self) -> Concrete { self }\n}");
}

#[test]
fn generic_class_axiom_methods_keep_phantom_actuals() {
    let mut env = Environment::new_test();
    env.add("structure Marker<T, U> {\n value: Bool\n}\nclass Marker<T, U> {\n define flag(self) -> Bool { axiom }\n}");
    let project = Project::new_mock();
    let first = env
        .bindings
        .evaluate_value(
            &project,
            &Expression::expect_value("Marker<Bool, Bool>.flag"),
            None,
        )
        .unwrap();
    let second = env
        .bindings
        .evaluate_value(
            &project,
            &Expression::expect_value("Marker<Bool, Bool -> Bool>.flag"),
            None,
        )
        .unwrap();
    assert_ne!(first, second);
    assert!(!first.has_generic());
    assert!(!second.has_generic());
    for value in [first, second] {
        let code = env.bindings.value_to_code(&value).unwrap();
        let replay = env
            .bindings
            .evaluate_value(&project, &Expression::expect_value(&code), None)
            .unwrap();
        assert_eq!(value, replay);
    }
}

fn verify(source: &str) -> Outcome {
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", source);
    let id = project.expect_ok("main");
    for node in project.get_env_by_id(id).unwrap().iter_goals() {
        let mut prover = Prover::new(&project, false);
        for fact in node.usable_facts(&project) {
            fact.as_proposition().unwrap().value.validate().unwrap();
            prover.add_fact(fact);
        }
        let context = node.goal_context().unwrap();
        assert!(!context.goal.value().has_generic());
        context.goal.value().validate().unwrap();
        prover.set_goal(&context);
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
fn generic_class_defining_equation_proves_with_a_fixed_second_type() {
    assert_eq!(verify(&format!("{PAIR}{SWAP}theorem swap_def<T>(p: Pair<T, Bool>) {{ p.swap = Pair.new(p.second, p.first) }}")), Outcome::Success);
    assert_eq!(
        verify(&format!(
            "{PAIR}{SWAP}theorem goal(p: Pair<Bool, Bool>) {{ p.first = p.second }}"
        )),
        Outcome::Exhausted
    );
}

#[test]
fn generic_class_declarations_reject_captured_outer_types_without_panicking() {
    for declaration in [
        "define bad(self) -> A { outer }",
        "define bad(self) -> A { axiom }",
        "define bad(self) -> Bool { outer = outer }",
        "let bad: Bool = outer = outer",
        "let bad: A = axiom",
    ] {
        let mut env = Environment::new_test();
        env.add(PAIR);
        let nodes = env.nodes.len();
        env.bad(&format!("theorem outer<A>(outer: A) {{ outer = outer }} by {{\n class Pair<T, U> {{\n {declaration}\n }}\n outer = outer\n}}"));
        assert_eq!(env.nodes.len(), nodes);
        assert!(!env.bindings.has_identifier("Pair.bad"));
        assert!(!env.bindings.has_type_name("T"));
        assert!(!env.bindings.has_type_name("U"));
    }
}

#[test]
fn generic_member_constants_generalize_their_types_values_and_phantom_parameters() {
    let mut env = Environment::new_test();
    env.add(PAIR);
    env.add("class Pair<T, U> {\n let t: T = axiom\n let u: U = axiom\n let flag: Bool = true\n let pair: Pair<T, U> = Pair.new(Pair<T, U>.t, Pair<T, U>.u)\n}");
    assert!(!env.bindings.has_type_name("T"));
    assert!(!env.bindings.has_type_name("U"));
    env.add("structure Other<T, U> {\n first: T\n second: U\n}");
    env.add("let t: Bool = Pair<Bool, Bool -> Bool>.t");
    env.add("let u: Bool -> Bool = Pair<Bool, Bool -> Bool>.u");
    env.add("let p: Pair<Bool, Bool -> Bool> = Pair<Bool, Bool -> Bool>.pair");
    env.bad("let bad: Bool = Pair.t");
    let project = Project::new_mock();
    let first = env
        .bindings
        .evaluate_value(
            &project,
            &Expression::expect_value("Pair<Bool, Bool>.flag"),
            None,
        )
        .unwrap();
    let second = env
        .bindings
        .evaluate_value(
            &project,
            &Expression::expect_value("Pair<Bool, Bool -> Bool>.flag"),
            None,
        )
        .unwrap();
    assert_ne!(first, second);
    for value in [first, second] {
        value.validate().unwrap();
        let code = env.bindings.value_to_code(&value).unwrap();
        let replay = env
            .bindings
            .evaluate_value(&project, &Expression::expect_value(&code), None)
            .unwrap();
        assert_eq!(value, replay);
    }
    assert_eq!(verify(&format!("{PAIR}class Pair<T, U> {{\n let flag: Bool = true\n}}\ntheorem goal {{ Pair<Bool, Bool>.flag }}")), Outcome::Success);
}

#[test]
fn class_headers_report_exact_declared_arity() {
    use venticorn::statement::Statement;
    let mut env = Environment::new_test();
    env.add(PAIR);
    for (text, expected) in [
        (
            "class Pair<T> {}",
            "type Pair expects 2 parameters, but got 1",
        ),
        (
            "class Pair<T, U, V> {}",
            "type Pair expects 2 parameters, but got 3",
        ),
    ] {
        let statement = Statement::parse_str(text).unwrap();
        let error = env
            .add_statement(&mut Project::new_mock(), &statement)
            .unwrap_err();
        assert_eq!(error.message(), expected);
        assert!(!env.bindings.has_type_name("T"));
        assert!(!env.bindings.has_type_name("U"));
        assert!(!env.bindings.has_type_name("V"));
    }
}

#[test]
fn recursive_generic_methods_preserve_phantom_actuals_in_declaration_order() {
    use venticorn::acorn_type::AcornType;
    let mut env = Environment::new_test();
    env.add("inductive Nat {\n zero\n suc(Nat)\n}\nstructure Box<T, U> {\n value: T\n}\nclass Box<T, U> {\n define repeat(self, n: Nat) -> T { match n {\n Nat.zero { self.value }\n Nat.suc(previous) { self.repeat(previous) }\n} }\n}");
    let (definition, params) = env
        .bindings
        .get_definition_and_params("Box.repeat")
        .unwrap();
    assert_eq!(
        params,
        &[
            venticorn::acorn_type::TypeParam::unconstrained("T"),
            venticorn::acorn_type::TypeParam::unconstrained("U")
        ]
    );
    definition.validate().unwrap();
    assert!(!definition.has_arbitrary());
    let mut recursive = vec![];
    definition.find_constants(
        &|constant| {
            constant.name.module_id == env.module_id
                && constant.name.local_name.to_string() == "Box.repeat"
        },
        &mut recursive,
    );
    assert!(!recursive.is_empty());
    for constant in recursive {
        assert_eq!(
            constant.params,
            vec![
                AcornType::Variable(venticorn::acorn_type::TypeParam {
                    name: "T".into(),
                    typeclass: None
                }),
                AcornType::Variable(venticorn::acorn_type::TypeParam {
                    name: "U".into(),
                    typeclass: None
                })
            ]
        );
        assert!(constant.instance_type.has_type_variable("T"));
        assert!(constant.instance_type.has_type_variable("U"));
    }
}
