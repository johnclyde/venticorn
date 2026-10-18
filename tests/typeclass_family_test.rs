use venticorn::acorn_type::PotentialType;
use venticorn::environment::Environment;
use venticorn::expression::Expression;
use venticorn::project::Project;
use venticorn::prover::{Outcome, Prover};
use venticorn::statement::{Statement, StatementInfo};

const CLASSES: &str =
    "typeclass M: Magma {\n mul: (M, M) -> M\n}\ntypeclass O: Other {\n item: O\n}\n";
const PAIR: &str = "structure MagmaPair<T: Magma> {\n first: T\n second: T\n}\nclass MagmaPair<Renamed> {\n define prod(self) -> Renamed { self.first.mul(self.second) }\n}\n";

#[test]
fn bounded_families_retain_formals_and_reopening_inherits_bounds_positionally() {
    let mut env = Environment::new_test();
    env.add(&format!("{CLASSES}{PAIR}structure Phantom<T: Magma, U: Other> {{\n flag: Bool\n}}\nclass Phantom<A, B> {{\n let value: Bool = axiom\n define preserve(self) -> Phantom<A, B> {{ self }}\n}}\ndefine create<T: Magma, U: Other> -> Phantom<T, U> {{ Phantom.new<T, U>(true) }}"));
    let magma = env.bindings.get_typeclass_for_name("Magma").unwrap();
    let other = env.bindings.get_typeclass_for_name("Other").unwrap();
    let PotentialType::Unresolved(family) =
        env.bindings.get_potential_type_for_name("Phantom").unwrap()
    else {
        panic!("expected family")
    };
    assert_eq!(
        family
            .params
            .iter()
            .map(|p| (p.name.as_str(), p.typeclass.as_ref()))
            .collect::<Vec<_>>(),
        [("T", Some(magma)), ("U", Some(other))]
    );
    for name in [
        "Phantom.new",
        "Phantom.flag",
        "Phantom.value",
        "Phantom.preserve",
    ] {
        let formals = env.bindings.get_params(name);
        assert_eq!(formals.len(), 2, "{name}");
        assert_eq!(formals[0].typeclass.as_ref(), Some(magma));
        assert_eq!(formals[1].typeclass.as_ref(), Some(other));
    }
    let prod = env.bindings.get_params("MagmaPair.prod");
    assert_eq!(prod[0].name, "Renamed");
    assert_eq!(prod[0].typeclass.as_ref(), Some(magma));
    for name in ["T", "U", "A", "B", "Renamed"] {
        assert!(!env.bindings.name_in_use(name));
    }
    for node in &env.nodes {
        node.claim.value.validate().unwrap();
    }
}

#[test]
fn invalid_family_actuals_and_conflicting_reopenings_roll_back() {
    let mut env = Environment::new_test();
    env.add(&format!(
        "{CLASSES}{PAIR}structure Phantom<T: Magma, U: Other> {{\n flag: Bool\n}}"
    ));
    for source in [
        "let bad: MagmaPair<Bool> = axiom",
        "let bad: Bool = MagmaPair.new<Bool>(true, false).first",
        "let bad: Bool = MagmaPair<Bool>.new(true, false).first",
        "let bad: (MagmaPair<Bool> -> Bool) = MagmaPair.first<Bool>",
        "let bad: Bool = MagmaPair.new(true, false).first",
        "define bad<T>(x: T) -> MagmaPair<T> { MagmaPair.new(x, x) }",
        "define bad<T: Other>(x: T) -> MagmaPair<T> { MagmaPair.new(x, x) }",
        "define bad<T: Magma, U: Other> -> Phantom<U, T> { axiom }",
        "define bad<T: Magma> -> Bool { Phantom.new<T, Bool>(true).flag }",
        "class MagmaPair<A: Other> { define bad(self) -> Bool { true } }",
        "class MagmaPair<A, B> { define bad(self) -> Bool { true } }",
        "structure Bad<T: Magma, T: Magma> {\n value: T\n}",
    ] {
        let nodes = env.nodes.len();
        let line = env.last_line();
        let error = env
            .add_statement(
                &mut Project::new_mock(),
                &Statement::parse_str(source).unwrap(),
            )
            .unwrap_err();
        assert!(
            error.message().contains("bound")
                || error.message().contains("parameters")
                || error.message().contains("defined")
                || error.message().contains("duplicate type parameter")
                || error.message().contains("expected type"),
            "{error}"
        );
        assert_eq!(env.nodes.len(), nodes, "{source}");
        assert_eq!(env.last_line(), line, "{source}");
        for name in ["bad", "Bad", "T", "U", "A", "B", "MagmaPair.bad"] {
            assert!(!env.bindings.name_in_use(name), "{source}: {name}");
        }
    }
    env.add("class MagmaPair<Again: Magma> { define keep(self) -> MagmaPair<Again> { self } }");
}

#[test]
fn imported_family_aliases_and_reexports_keep_canonical_bounds_and_spelling() {
    let mut project = Project::new_mock();
    project.mock("/mock/left.ac", &format!("{CLASSES}{PAIR}"));
    project.mock("/mock/right.ac", CLASSES);
    project.mock(
        "/mock/bridge.ac",
        "from left import MagmaPair\ntype Reexport: MagmaPair",
    );
    project.mock("/mock/main.ac", "import left\nimport right\nfrom bridge import Reexport\ntype Alias: Reexport\ndefine make<T: left.Magma>(a: T) -> Alias<T> { Alias.new(a, a) }\ntheorem goal<T: left.Magma>(a: T) { Alias.new(a, a).first = a }");
    let id = project.expect_ok("main");
    let env = project.get_env_by_id(id).unwrap();
    let node = env.get_node_by_name("goal");
    let scope = &node.current().block().unwrap().env.bindings;
    let value = scope
        .evaluate_value(
            &project,
            &Expression::expect_value("forall(x: Alias<T>) { x.first = x.first }"),
            None,
        )
        .unwrap();
    let code = scope.value_to_code(&value).unwrap();
    assert!(code.contains("Reexport<T>"), "{code}");
    assert_eq!(
        scope
            .evaluate_value(&project, &Expression::expect_value(&code), None)
            .unwrap(),
        value
    );
    let mut prover = Prover::new(&project, false);
    for fact in node.usable_facts(&project) {
        prover.add_fact(fact);
    }
    prover.set_goal(&node.goal_context().unwrap());
    assert_eq!(prover.quick_search(), Outcome::Success);
    let mut scope = env.child(0, false);
    for source in [
        "let bad: Alias<Bool> = axiom",
        "define bad<T: right.Magma>(a: T) -> Reexport<T> { axiom }",
        "define bad<T: right.Magma>(a: T) -> T { Alias.new(a, a).first }",
    ] {
        let error = scope
            .add_statement(&mut project, &Statement::parse_str(source).unwrap())
            .unwrap_err();
        assert!(
            error.message().contains("class bound") || error.message().contains("expected type"),
            "{error}"
        );
        assert!(!scope.bindings.name_in_use("bad"));
    }
}

#[test]
fn bounded_family_witness_emits_nonempty_proof_and_replays() {
    let source = format!("{CLASSES}structure Marker<T: Magma> {{\n value: Bool\n}}\nclass Marker<T> {{\n define chosen(self) -> Marker<T> {{ axiom }}\n}}\ndefine seed<T: Magma> -> Marker<T> {{ axiom }}\ndefine mul<T: Magma>(a: Marker<T>, b: Marker<T>) -> Marker<T> {{ axiom }}\ndefine marked<T: Magma>(n: Marker<T>) -> Bool {{ exists(d: Marker<T>) {{ mul(seed<T>, d) = n }} }}\naxiom right<T: Magma>(a: Marker<T>, b: Marker<T>) {{ b = seed<T>.chosen -> mul(a, b) = seed<T>.chosen }}\ntheorem goal<T: Magma> {{ marked(seed<T>.chosen) }}");
    fn search(source: &str, shallow: bool) -> Outcome {
        let mut project = Project::new_mock();
        project.mock("/mock/main.ac", source);
        let id = project.expect_ok("main");
        for node in project.get_env_by_id(id).unwrap().iter_goals() {
            let mut prover = Prover::new(&project, false);
            for fact in node.usable_facts(&project) {
                fact.as_proposition().unwrap().value.validate().unwrap();
                prover.add_fact(fact);
            }
            prover.set_goal(&node.goal_context().unwrap());
            let result = if shallow {
                prover.quick_verification_search()
            } else {
                prover.quick_search()
            };
            if result != Outcome::Success {
                return result;
            }
        }
        Outcome::Success
    }
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", &source);
    let id = project.expect_ok("main");
    let node = project.get_env_by_id(id).unwrap().get_node_by_name("goal");
    let mut prover = Prover::new(&project, false);
    for fact in node.usable_facts(&project) {
        prover.add_fact(fact);
    }
    prover.set_goal(&node.goal_context().unwrap());
    assert_eq!(prover.quick_search(), Outcome::Success);
    let code = prover
        .get_and_print_proof()
        .unwrap()
        .to_code(&node.current().block().unwrap().env.bindings)
        .unwrap();
    assert!(!code.is_empty());
    assert_eq!(
        search(&format!("{source} by {{\n{}\n}}", code.join("\n")), false),
        Outcome::Success
    );
    let bad = format!("{source} by {{ exists(x: Marker<T>) {{ x != x }} }}");
    assert!(matches!(
        search(&bad, false),
        Outcome::Exhausted | Outcome::Timeout | Outcome::Constrained
    ));
    assert_eq!(search(&bad, true), Outcome::Exhausted);
}

#[test]
fn bounded_structure_and_inherited_member_scope_are_admitted() {
    let mut env = Environment::new_test();
    env.add(
        r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }
            
            structure MagmaPair<T: Magma> {
                first: T
                second: T
            }

            class MagmaPair<T> {
                define prod(self) -> T {
                    self.first.mul(self.second)
                }
            }
            "#,
    );
}

#[test]
fn bounded_family_projection_and_method_equations_prove_without_extra_laws() {
    for (operator, expected) in [("=", Outcome::Success), ("!=", Outcome::Exhausted)] {
        let source = format!("{CLASSES}{PAIR}theorem goal<T: Magma>(a: T, b: T) {{ MagmaPair.new(a, b).prod {operator} a.mul(b) }}");
        let mut project = Project::new_mock();
        project.mock("/mock/main.ac", &source);
        let id = project.expect_ok("main");
        let node = project.get_env_by_id(id).unwrap().get_node_by_name("goal");
        let mut prover = Prover::new(&project, false);
        for fact in node.usable_facts(&project) {
            fact.as_proposition().unwrap().value.validate().unwrap();
            prover.add_fact(fact);
        }
        prover.set_goal(&node.goal_context().unwrap());
        let mut ordinary = prover.clone();
        let outcome = ordinary.quick_search();
        if expected == Outcome::Success {
            assert_eq!(outcome, expected);
        } else {
            assert!(matches!(
                outcome,
                Outcome::Exhausted | Outcome::Timeout | Outcome::Constrained
            ));
        }
        assert_eq!(prover.quick_verification_search(), expected);
    }
}

#[test]
fn bounded_family_constraints_keep_scope_and_require_existence() {
    for (constraint, expected) in [("flag", Outcome::Success), ("false", Outcome::Exhausted)] {
        let source = format!("{CLASSES}structure Flagged<T: Magma> {{\n flag: Bool\n}} constraint {{ {constraint} }}");
        let mut project = Project::new_mock();
        project.mock("/mock/main.ac", &source);
        let id = project.expect_ok("main");
        let env = project.get_env_by_id(id).unwrap();
        let nodes = env.iter_goals().collect::<Vec<_>>();
        assert_eq!(nodes.len(), 1);
        let node = &nodes[0];
        let bindings = &node.current().block().unwrap().env.bindings;
        let venticorn::acorn_type::AcornType::Arbitrary(param) =
            bindings.get_type_for_name("T").unwrap()
        else {
            panic!("constraint must retain fixed bound parameter")
        };
        assert_eq!(
            param.typeclass.as_ref(),
            env.bindings.get_typeclass_for_name("Magma")
        );
        assert!(!bindings.name_in_use("Flagged"));
        assert!(!bindings.name_in_use("Flagged.new"));
        let mut prover = Prover::new(&project, false);
        for fact in node.usable_facts(&project) {
            prover.add_fact(fact);
        }
        prover.set_goal(&node.goal_context().unwrap());
        let mut ordinary = prover.clone();
        assert_eq!(ordinary.quick_search(), expected);
        assert_eq!(prover.quick_verification_search(), expected);
        assert!(!env.bindings.name_in_use("T"));
    }
}

#[test]
fn bounded_structure_and_explicit_member_scope_are_admitted() {
    let mut env = Environment::new_test();
    env.add(
        r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }
            
            structure MagmaPair<T: Magma> {
                first: T
                second: T
            }

            class MagmaPair<T: Magma> {
                define prod(self) -> T {
                    self.first.mul(self.second)
                }
            }
            "#,
    );
}

#[test]
fn unbounded_structure_reopening_cannot_add_a_class_bound() {
    let mut env = Environment::new_test();
    env.add(
        r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }
            
            structure MagmaPair<T> {
                first: T
                second: T
            }
            "#,
    );
    let nodes = env.nodes.len();
    let last_line = env.last_line();
    env.bad(
        r#"
            class MagmaPair<T: Magma> {
                define prod(self) -> T {
                    self.first.mul(self.second)
                }
            }
            "#,
    );
    assert_eq!(env.nodes.len(), nodes);
    assert_eq!(env.last_line(), last_line);
    assert!(!env.bindings.name_in_use("T"));
    assert!(!env.bindings.name_in_use("MagmaPair.prod"));

    let statement = Statement::parse_str(
        "class MagmaPair<Again: Magma> { define prod(self) -> Again { self.first.mul(self.second) } }",
    ).unwrap();
    let StatementInfo::Class(class) = &statement.statement else {
        panic!()
    };
    let bound_range = class.type_params[0].typeclass.as_ref().unwrap().range();
    let error = env
        .add_statement(&mut Project::new_mock(), &statement)
        .unwrap_err();
    assert!(error.message().contains("bound conflicts"), "{error}");
    assert_eq!(error.range(), bound_range);
    assert_eq!(env.nodes.len(), nodes);
    assert_eq!(env.last_line(), last_line);
    assert!(!env.bindings.name_in_use("Again"));
    assert!(!env.bindings.name_in_use("MagmaPair.prod"));
    env.add("class MagmaPair<Again> { define keep(self) -> Again { self.first } }");
    assert!(env.bindings.name_in_use("MagmaPair.keep"));
    assert!(!env.bindings.name_in_use("Again"));
}
