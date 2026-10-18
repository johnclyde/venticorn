use std::collections::HashMap;
use venticorn::acorn_type::Class;
use venticorn::acorn_type::{AcornType, TypeParam, Typeclass};
use venticorn::builder::BuildStatus;
use venticorn::environment::Environment;
use venticorn::expression::Expression;
use venticorn::persistent_cache::CachePolicy;
use venticorn::project::Project;
use venticorn::prover::{Outcome, Prover};

const DECL: &str = "typeclass T: Marked {\n flag: Bool\n}\ntype Item: axiom\nlet first: Item = axiom\nlet second: Item = axiom\ndefine same<T>(a: T, b: T) -> Bool { a = b }\naxiom collapse<T: Marked>(a: T, b: T) { same(a, b) }\n";
const INSTANCE: &str = "instance Item: Marked {\n let flag: Bool = true\n}\n";
fn project(source: &str) -> Project {
    let mut p = Project::new_mock();
    p.mock("/mock/main.ac", source);
    p.expect_ok("main");
    p
}
fn outcomes(p: &Project, slow: bool) -> Vec<Outcome> {
    let env = p
        .get_env_by_ref(&venticorn::module::ModuleRef::Name("main".into()))
        .unwrap();
    let mut result = vec![];
    let mut callback = |mut prover: Prover, _| {
        result.push(prover.quick_search());
        true
    };
    if slow {
        p.for_each_prover_slow(env, &mut callback);
    } else {
        p.for_each_prover_fast(env, &mut callback);
    }
    result
}
fn miss(outcome: Outcome) {
    assert!(
        matches!(
            outcome,
            Outcome::Exhausted | Outcome::Constrained | Outcome::Timeout
        ),
        "{outcome:?}"
    );
}

#[test]
fn later_membership_cannot_retroactively_specialize_an_earlier_fact_demand() {
    let source = format!("{DECL}theorem before {{ same(first, second) }}\n{INSTANCE}theorem after {{ same(first, second) }}");
    let mut p = project(&source);
    for slow in [false, true] {
        let found = outcomes(&p, slow);
        assert_eq!(found.len(), 2);
        miss(found[0].clone());
        assert_eq!(found[1], Outcome::Success);
    }
    for policy in [CachePolicy::ReadWrite, CachePolicy::Disabled] {
        p.set_cache_policy(policy);
        for dataset in [false, true] {
            let mut builder = p.builder(|_| {});
            if dataset {
                builder.create_dataset();
            }
            p.build(&mut builder);
            assert_eq!(builder.status, BuildStatus::Warning);
            assert_eq!(
                (builder.goals_done, builder.num_success, builder.num_cached),
                (2, 1, 0)
            );
            assert!(builder
                .cache()
                .unwrap()
                .get(&venticorn::module::ModuleRef::Name("main".into()))
                .is_none());
        }
    }
}

#[test]
fn import_frontier_changes_rebuild_facts_even_when_memberships_do_not_change() {
    let mut p = Project::new_mock();
    p.mock("/mock/base.ac", "let flag: Bool = axiom");
    p.mock("/mock/laws.ac", "import base\naxiom known { base.flag }");
    p.mock("/mock/main.ac", "import base\ntheorem outer { true } by {\n base.flag\n import laws\n base.flag\n}\ntheorem tail { base.flag }");
    p.expect_ok("main");
    for slow in [false, true] {
        let found = outcomes(&p, slow);
        assert_eq!(found.len(), 4);
        miss(found[0].clone());
        assert_eq!(found[1], Outcome::Success);
        assert_eq!(found[2], Outcome::Success);
        miss(found[3].clone());
    }
    let report = p.sync_build_report();
    assert_eq!(report.status, BuildStatus::Warning);
    assert_eq!((report.goals_done, report.num_success), (4, 2));
}

#[test]
fn complete_actuals_preserve_canonical_bounds_for_explicit_inferred_and_phantom_calls() {
    let mut env = Environment::new_test();
    env.add(&format!("{DECL}{INSTANCE}define identity<T: Marked>(x: T) -> T {{ x }}\ndefine phantom<T: Marked> -> Bool {{ true }}\nstructure Box<T: Marked> {{\n value: T\n}}\ntype Alias: Item\nlet chosen: Alias = identity<Item>(first)\nlet inferred: Item = identity(first)\nlet flag: Bool = phantom<Alias>\nlet boxed: Box<Item> = Box.new(first)"));
    let class = env
        .bindings
        .get_typeclass_for_name("Marked")
        .unwrap()
        .clone();
    let formal = TypeParam {
        name: "T".into(),
        typeclass: Some(class.clone()),
    };
    let ty = env
        .bindings
        .evaluate_type(
            &Project::new_mock(),
            &Expression::generate_identifier("Item"),
        )
        .unwrap();
    let scope = env.bindings.proof_scope();
    assert!(formal.accepts_in_scope(&ty, scope));
    assert!(!formal.accepts(&ty));
    for bad in [
        AcornType::Bool,
        AcornType::Data(
            Class::new(class.module_id, "Item".into()),
            vec![AcornType::Bool],
        ),
        AcornType::Data(Class::new(class.module_id + 1, "Item".into()), vec![]),
        AcornType::new_functional(vec![ty.clone()], ty.clone()),
        AcornType::Arbitrary(TypeParam::unconstrained("U")),
    ] {
        assert!(!formal.accepts_in_scope(&bad, scope));
        let mut reused = HashMap::from([("T".into(), bad.clone())]);
        assert!(
            !AcornType::Variable(formal.clone()).match_instance_in_scope(&bad, &mut reused, scope)
        );
    }
    let foreign = TypeParam {
        name: "T".into(),
        typeclass: Some(Typeclass {
            module_id: class.module_id + 1,
            name: class.name,
        }),
    };
    assert!(!foreign.accepts_in_scope(&ty, scope));
    for input in [
        "let bad: Bool = phantom<Bool>",
        "let bad: Bool = Marked.flag<Bool>",
        "let bad: Bool = identity(true)",
        "let bad: Box<Bool> = axiom",
    ] {
        env.bad(input);
        assert!(!env.bindings.name_in_use("bad"));
    }
}

#[test]
fn explicit_scope_mismatch_is_an_error_and_legacy_constructor_never_widens() {
    let p = project(&format!(
        "{DECL}{INSTANCE}theorem goal {{ same(first, second) }}"
    ));
    let env = p
        .get_env_by_ref(&venticorn::module::ModuleRef::Name("main".into()))
        .unwrap();
    let node = env.get_node_by_name("goal");
    let goal = node.goal_context().unwrap();
    let mut legacy = Prover::new(&p, false);
    let mut wrong = Prover::with_scope(&p, false, Default::default());
    for fact in node.usable_facts(&p) {
        legacy.add_fact(fact.clone());
        wrong.add_fact(fact);
    }
    legacy.set_goal(&goal);
    wrong.set_goal(&goal);
    miss(legacy.quick_search());
    assert_eq!(
        wrong.quick_search(),
        Outcome::Error("proof scope changed after fact ingestion".into())
    );
    let mut scoped = p.prover_for_node(&node, false);
    scoped.set_goal(&goal);
    assert_eq!(scoped.quick_search(), Outcome::Success);
}

#[test]
fn generated_nonempty_proof_replays_at_its_original_position_with_future_names_intact() {
    let facts = "typeclass T: Marked {\n chosen: T\n mul: (T, T) -> T\n}\ninductive State {\n clean\n dirty\n}\ninstance State: Marked {\n let chosen: State = axiom\n define mul(self, other: State) -> State { axiom }\n}\ndefine marked(n: State) -> Bool { exists(d: State) { State.Marked.mul(State.clean, d) = n } }\naxiom chosen_right(a: State, b: State) { b = State.Marked.chosen -> State.Marked.mul(a, b) = State.Marked.chosen }";
    let prefix = "import facts\ntheorem goal { facts.marked(facts.State.Marked.chosen) } by {\n";
    let claim = " facts.marked(facts.State.Marked.chosen)\n";
    let suffix = " type Alias: facts.State\n import later\n}\ntype Local: axiom\ninstance Local: facts.Marked {\n let chosen: Local = axiom\n define mul(self, other: Local) -> Local { axiom }\n}\n";
    let make = |source: &str| {
        let mut p = Project::new_mock();
        p.mock("/mock/facts.ac", facts);
        p.mock("/mock/later.ac", "theorem harmless { true }");
        p.mock("/mock/main.ac", source);
        p.expect_ok("main");
        p
    };
    let original = format!("{prefix}{claim}{suffix}");
    let p = make(&original);
    let env = p
        .get_env_by_ref(&venticorn::module::ModuleRef::Name("main".into()))
        .unwrap();
    let node = env
        .iter_goals()
        .find(|node| node.goal_context().unwrap().proof_insertion_line == 2)
        .unwrap();
    let goal = node.goal_context().unwrap();
    assert!(!goal.insert_block);
    assert_eq!(goal.proof_insertion_line, 2);
    let mut prover = p.prover_for_node(&node, false);
    prover.set_goal(&goal);
    assert_eq!(prover.quick_search(), Outcome::Success);
    let code = prover
        .get_and_print_proof()
        .unwrap()
        .to_code(&node.bindings_for_codegen())
        .unwrap();
    assert!(!code.is_empty());
    assert!(!code.join("\n").contains("Alias"));
    let replay = format!("{prefix}{}\n{claim}{suffix}", code.join("\n"));
    assert!(replay.ends_with(suffix));
    let report = make(&replay).sync_build_report();
    assert_eq!(report.status, BuildStatus::Good);
    assert!(report.goals_done >= 3);
    let false_replay = format!("{prefix}exists(x: facts.State) {{ x != x }}\n{claim}{suffix}");
    assert_eq!(
        make(&false_replay).sync_build_report().status,
        BuildStatus::Warning
    );
}

#[test]
fn saved_guidance_cannot_import_a_premise_before_its_new_lexical_position() {
    let mut p = Project::new_mock();
    p.mock(
        "/mock/base.ac",
        "let seed: Bool = axiom\nlet first: Bool = axiom\nlet second: Bool = axiom",
    );
    p.mock("/mock/laws.ac", "import base\naxiom start { base.seed }\naxiom left { base.seed implies base.first }\naxiom right { base.seed implies base.second }");
    p.mock(
        "/mock/main.ac",
        "import base\nimport laws\ntheorem outer { true } by {\n base.first\n base.second\n}",
    );
    let cold = p.sync_build_report();
    assert_eq!(cold.status, BuildStatus::Good);
    assert_eq!(cold.goals_done, 3);
    assert!(!cold
        .cache
        .unwrap()
        .get(&venticorn::module::ModuleRef::Name("main".into()))
        .unwrap()
        .theorem_premises()["outer"]
        .is_empty());
    p.update_file(
        std::path::PathBuf::from("/mock/main.ac"),
        "import base\ntheorem outer { true } by {\n base.first\n import laws\n base.second\n}",
        10,
    )
    .unwrap();
    p.expect_ok("main");
    let mut builder = p.builder(|_| {});
    p.build(&mut builder);
    assert_eq!(builder.status, BuildStatus::Warning);
    assert_eq!(
        (builder.goals_done, builder.num_success, builder.num_cached),
        (3, 2, 0)
    );
    assert!(builder.hinted_searches > 0);
    assert!(builder.hinted_successes > 0);
    assert!(builder
        .cache()
        .unwrap()
        .get(&venticorn::module::ModuleRef::Name("main".into()))
        .is_none());
}

#[test]
fn selected_codegen_scope_preserves_reexport_only_instance_spelling() {
    let mut p = Project::new_mock();
    p.mock("/mock/owner.ac", "typeclass T: Marked {\n flag: Bool\n}\ntype State: axiom\ninstance State: Marked {\n let flag: Bool = true\n}");
    p.mock("/mock/bridge.ac", "from owner import State");
    p.mock(
        "/mock/main.ac",
        "from bridge import State\ntheorem goal { true }",
    );
    let id = p.expect_ok("main");
    let env = p.get_env_by_id(id).unwrap();
    let node = env.get_node_by_name("goal");
    let bindings = node.bindings_for_codegen();
    let value = bindings
        .evaluate_value(&p, &Expression::expect_value("State.Marked.flag"), None)
        .unwrap();
    let code = bindings.value_to_code(&value).unwrap();
    assert_eq!(code, "State.Marked.flag");
    assert_eq!(
        bindings
            .evaluate_value(&p, &Expression::expect_value(&code), None)
            .unwrap(),
        value
    );
}
