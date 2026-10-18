use venticorn::acorn_type::AcornType;
use venticorn::builder::BuildStatus;
use venticorn::persistent_cache::CachePolicy;
use venticorn::project::Project;
use venticorn::proposition::SourceType;
use venticorn::prover::Outcome;

fn outcomes(source: &str, shallow: bool) -> Vec<Outcome> {
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", source);
    let module = project.expect_ok("main");
    let env = project.get_env_by_id(module).unwrap();
    let expected = env.iter_goals().count();
    assert!(expected > 0);
    let mut results = vec![];
    project.for_each_prover_slow(env, &mut |mut prover, _| {
        let result = if shallow {
            prover.quick_verification_search()
        } else {
            prover.quick_search()
        };
        assert!(!matches!(result, Outcome::Error(_)), "{:?}", prover.error);
        results.push(result);
        true
    });
    assert_eq!(results.len(), expected);
    results
}

fn assert_success(source: &str) {
    for shallow in [false, true] {
        assert!(outcomes(source, shallow)
            .iter()
            .all(|o| *o == Outcome::Success));
    }
}

fn assert_rejected(source: &str) {
    let ordinary = outcomes(source, false);
    assert!(ordinary.iter().any(|o| matches!(
        o,
        Outcome::Exhausted | Outcome::Timeout | Outcome::Constrained
    )));
    assert!(ordinary.iter().all(|o| matches!(
        o,
        Outcome::Success | Outcome::Exhausted | Outcome::Timeout | Outcome::Constrained
    )));
    assert!(outcomes(source, true).contains(&Outcome::Exhausted));
}

#[test]
fn canonical_method_bridges_keep_the_owner_actual_and_signature() {
    let mut project = Project::new_mock();
    let class = "typeclass T: Painted {\n is_red: T -> Bool\n}";
    project.mock("/mock/left.ac", class);
    project.mock("/mock/right.ac", class);
    let source = "import left\nimport right\ninductive State {\n only\n}\ninductive Other {\n only\n}\ninstance State: left.Painted {\n define is_red(self) -> Bool { true }\n}\ninstance Other: right.Painted {\n define is_red(self) -> Bool { false }\n}\ntheorem positive { left.Painted.is_red(State.only) }\ntheorem negative { not right.Painted.is_red(Other.only) }";
    project.mock("/mock/main.ac", source);
    let module = project.expect_ok("main");
    let left = project.expect_ok("left");
    let right = project.expect_ok("right");
    let env = project.get_env_by_id(module).unwrap();
    let mut bridges = vec![];
    for (target_name, class_module) in [("State", left), ("Other", right)] {
        let target = env.bindings.get_type_for_name(target_name).unwrap();
        let bridge = env.nodes.iter().find(|node| matches!(&node.claim.source.source_type, SourceType::TypeDefinition(name, member) if name == target_name && member == "instance.Painted.is_red")).unwrap();
        assert!(bridge.structural);
        assert!(bridge.block.is_none());
        let mut references = vec![];
        bridge.claim.value.find_constants(
            &|constant| constant.name.local_name.to_string() == "Painted.is_red",
            &mut references,
        );
        assert_eq!(references.len(), 1);
        let generic = &references[0];
        assert_eq!(generic.name.module_id, class_module);
        assert_eq!(generic.params, [target.clone()]);
        let AcornType::Function(signature) = &generic.instance_type else {
            panic!("member must keep its functional signature")
        };
        assert_eq!(signature.arg_types, [target.clone()]);
        assert_eq!(*signature.return_type, AcornType::Bool);
        let implementation = env
            .bindings
            .get_constant_value(&format!("{target_name}.Painted.is_red"))
            .unwrap()
            .resolved()
            .unwrap();
        assert_eq!(generic.instance_type, implementation.get_type());
        bridge.claim.value.validate().unwrap();
        bridges.push(bridge.claim.value.clone());
    }
    assert_ne!(bridges[0], bridges[1]);
    let mut results = vec![];
    project.for_each_prover_slow(env, &mut |mut prover, _| {
        results.push(prover.quick_search());
        true
    });
    assert_eq!(results, [Outcome::Success, Outcome::Success]);
    let standalone = "typeclass T: Painted {\n is_red: T -> Bool\n}\ninductive State {\n only\n}\ninstance State: Painted {\n define is_red(self) -> Bool { true }\n}\ntheorem goal { Painted.is_red(State.only) }";
    assert_success(standalone);
    assert_rejected(&standalone.replace(
        "theorem goal { Painted.is_red",
        "theorem goal { not Painted.is_red",
    ));
}

#[test]
fn bridge_facts_are_after_the_obligation_and_absent_from_its_own_proof() {
    let source = "inductive State {\n only\n}\ntypeclass T: Painted {\n is_red: T -> Bool\n red(x: T) { T.is_red(x) }\n}\ninstance State: Painted {\n define is_red(self) -> Bool { true }\n}\ntheorem after { Painted.is_red(State.only) }";
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", source);
    let module = project.expect_ok("main");
    let env = project.get_env_by_id(module).unwrap();
    let class = env.bindings.get_typeclass_for_name("Painted").unwrap();
    let obligation_index = env.nodes.iter().position(|node| matches!(&node.claim.source.source_type, SourceType::Instance(name, class) if name == "State" && class == "Painted")).unwrap();
    let bridge_index = env.nodes.iter().position(|node| matches!(&node.claim.source.source_type, SourceType::TypeDefinition(name, member) if name == "State" && member == "instance.Painted.is_red")).unwrap();
    assert!(obligation_index < bridge_index);
    let obligation = env.iter_goals().next().unwrap();
    assert!(!obligation
        .goal_context()
        .unwrap()
        .proof_scope
        .has_membership(module, "State", class));
    assert!(!obligation.usable_facts(&project).iter().any(|fact| matches!(&fact.source.source_type, SourceType::TypeDefinition(name, member) if name == "State" && member == "instance.Painted.is_red")));
    let after = env.get_node_by_name("after");
    assert!(after
        .goal_context()
        .unwrap()
        .proof_scope
        .has_membership(module, "State", class));
    assert!(after.usable_facts(&project).iter().any(|fact| matches!(&fact.source.source_type, SourceType::TypeDefinition(name, member) if name == "State" && member == "instance.Painted.is_red")));
    assert_eq!(env.iter_goals().count(), 2);
    assert_success(source);

    let false_instance = source.replace("{ true }", "{ false }");
    assert!(matches!(
        outcomes(&false_instance, false)[0],
        Outcome::Exhausted | Outcome::Timeout | Outcome::Constrained
    ));
    assert_eq!(outcomes(&false_instance, true)[0], Outcome::Exhausted);
    let mut invalid = Project::new_mock();
    invalid.mock("/mock/main.ac", &false_instance);
    invalid.expect_ok("main");
    invalid.set_cache_policy(CachePolicy::MemoryOnly);
    assert_eq!(invalid.sync_build_report().status, BuildStatus::Warning);
    assert_eq!(invalid.cached_build().num_modules(), 0);
}

#[test]
fn earlier_goals_cannot_borrow_later_membership_or_bridges() {
    let source = "typeclass T: Painted {\n is_red: T -> Bool\n}\ndefine observed<T>(x: T) -> Bool { axiom }\naxiom via_member<T: Painted>(x: T) { observed(x) = Painted.is_red(x) }\ninductive State {\n only\n}\ntheorem before { observed(State.only) }\ninstance State: Painted {\n define is_red(self) -> Bool { true }\n}\ntheorem after { observed(State.only) }";
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", source);
    let module = project.expect_ok("main");
    let env = project.get_env_by_id(module).unwrap();
    let before = env.get_node_by_name("before");
    assert!(!before.usable_facts(&project).iter().any(|fact| matches!(&fact.source.source_type, SourceType::TypeDefinition(name, member) if name == "State" && member == "instance.Painted.is_red")));
    for shallow in [false, true] {
        let results = outcomes(source, shallow);
        assert_eq!(results.len(), 2);
        if shallow {
            assert_eq!(results[0], Outcome::Exhausted);
        } else {
            assert!(matches!(
                results[0],
                Outcome::Exhausted | Outcome::Timeout | Outcome::Constrained
            ));
        }
        assert_eq!(results[1], Outcome::Success);
    }
    project.set_cache_policy(CachePolicy::MemoryOnly);
    assert_eq!(project.sync_build_report().status, BuildStatus::Warning);
    assert_eq!(project.cached_build().num_modules(), 0);
}

#[test]
fn two_instances_cannot_certify_each_other_through_a_future_membership() {
    let source = "inductive Left {\n only\n}\ninductive Right {\n only\n}\ntypeclass T: Marked {\n marked: T -> Bool\n every(x: T) { T.marked(x) }\n}\ndefine observed<T>(x: T) -> Bool { axiom }\naxiom consequence<T: Marked>(x: T) { observed(x) }\ninstance Left: Marked {\n define marked(self) -> Bool { observed(Right.only) }\n}\ninstance Right: Marked {\n define marked(self) -> Bool { observed(Left.only) }\n}";
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", source);
    let module = project.expect_ok("main");
    let env = project.get_env_by_id(module).unwrap();
    let class = env.bindings.get_typeclass_for_name("Marked").unwrap();
    let contexts = env
        .iter_goals()
        .map(|node| node.goal_context().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(contexts.len(), 2);
    assert!(!contexts[0]
        .proof_scope
        .has_membership(module, "Left", class));
    assert!(!contexts[0]
        .proof_scope
        .has_membership(module, "Right", class));
    assert!(contexts[1]
        .proof_scope
        .has_membership(module, "Left", class));
    assert!(!contexts[1]
        .proof_scope
        .has_membership(module, "Right", class));
    for shallow in [false, true] {
        let results = outcomes(source, shallow);
        assert_eq!(results.len(), 2);
        if shallow {
            assert_eq!(results[0], Outcome::Exhausted);
        } else {
            assert!(matches!(
                results[0],
                Outcome::Exhausted | Outcome::Timeout | Outcome::Constrained
            ));
        }
        assert_eq!(results[1], Outcome::Success);
    }
    project.set_cache_policy(CachePolicy::MemoryOnly);
    assert_eq!(project.sync_build_report().status, BuildStatus::Warning);
    assert_eq!(project.cached_build().num_modules(), 0);
}

#[test]
fn generic_method_witness_emits_nonempty_code_at_the_original_goal_position() {
    // Reuse the established concrete witness shape, but demand the generic method.
    // The chosen value is an ordinary constant.
    let source = "typeclass T: Marked {\n combine: (T, T) -> T\n}\ninductive State {\n clean\n dirty\n}\nlet chosen: State = axiom\ninstance State: Marked {\n define combine(self, other: State) -> State { axiom }\n}\ndefine marked(n: State) -> Bool { exists(d: State) { Marked.combine(State.clean, d) = n } }\naxiom chosen_right(a: State, b: State) { b = chosen -> State.Marked.combine(a, b) = chosen }\ntheorem goal { marked(chosen) }\nlet future_chosen: State = chosen\ntheorem after { true }";
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", source);
    let module = project.expect_ok("main");
    let env = project.get_env_by_id(module).unwrap();
    let node = env.get_node_by_name("goal");
    let goal = node.goal_context().unwrap();
    let mut prover = project.prover_for_node(&node, false);
    prover.set_goal(&goal);
    assert_eq!(prover.quick_search(), Outcome::Success);
    let code = prover
        .get_and_print_proof()
        .unwrap()
        .to_code(&node.bindings_for_codegen())
        .unwrap();
    assert!(
        !code.is_empty(),
        "the generic method must emit a real witness proof"
    );
    assert!(!code.join("\n").contains("future_chosen"));
    let lines = source.lines().collect::<Vec<_>>();
    let insertion = goal.proof_insertion_line as usize;
    assert!(goal.insert_block);
    assert_eq!(lines[insertion], "theorem goal { marked(chosen) }");
    let suffix = lines[insertion + 1..].join("\n");
    assert!(suffix.starts_with("let future_chosen"));
    let insert = |body: &str| {
        format!(
            "{} by {{\n{body}\n}}\n{suffix}",
            lines[..=insertion].join("\n")
        )
    };
    let replay = insert(&code.join("\n"));
    assert!(replay.ends_with("theorem after { true }"));
    assert_success(&replay);
    let false_replay = insert("exists(x: State) { x != x }");
    assert!(matches!(
        outcomes(&false_replay, false)[0],
        Outcome::Exhausted | Outcome::Constrained | Outcome::Timeout
    ));
    assert_eq!(outcomes(&false_replay, true)[0], Outcome::Exhausted);
    let mut invalid = Project::new_mock();
    invalid.mock("/mock/main.ac", &false_replay);
    let module = invalid.expect_ok("main");
    let first = invalid
        .get_env_by_id(module)
        .unwrap()
        .iter_goals()
        .next()
        .unwrap()
        .goal_context()
        .unwrap();
    assert_eq!(first.goal.range().start.line, insertion as u32 + 1);
    let report = invalid.sync_build_report();
    assert_eq!(report.status, BuildStatus::Warning);
    assert!(report.goals_done >= 3);
    assert!(report.num_success < report.goals_total);
    assert_eq!(invalid.cached_build().num_modules(), 0);
}
