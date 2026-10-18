use venticorn::builder::BuildStatus;
use venticorn::environment::Environment;
use venticorn::persistent_cache::CachePolicy;
use venticorn::project::Project;
use venticorn::proposition::SourceType;
use venticorn::prover::Outcome;
use venticorn::statement::Statement;

const SINGLETON: &str = "typeclass S: Singleton {\n value: S\n unique(x: S) { x = S.value }\n}";
const UNIT: &str = "inductive Unit {\n only\n}";
const BIT: &str = "inductive Bit {\n zero\n one\n}";

fn outcomes(source: &str, shallow: bool) -> Vec<Outcome> {
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", source);
    let module = project.expect_ok("main");
    let env = project.get_env_by_id(module).unwrap();
    let count = env.iter_goals().count();
    assert!(count > 0, "the test must actually create proof obligations");
    let mut answers = vec![];
    project.for_each_prover_slow(env, &mut |mut prover, _| {
        let outcome = if shallow {
            prover.quick_verification_search()
        } else {
            prover.quick_search()
        };
        assert!(
            !matches!(outcome, Outcome::Error(_)),
            "{:?}",
            prover.error()
        );
        answers.push(outcome);
        true
    });
    assert_eq!(answers.len(), count);
    answers
}

fn assert_success(source: &str) {
    for shallow in [false, true] {
        assert!(outcomes(source, shallow)
            .iter()
            .all(|o| *o == Outcome::Success));
    }
}

fn assert_rejected_goal(source: &str) {
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
fn implicit_laws_and_explicit_proofs_create_real_scoped_obligations() {
    for proof in [
        "",
        " by {\n forall(x: Unit) { x = Unit.Singleton.value }\n}",
    ] {
        let source = format!("{UNIT}\n{SINGLETON}\ninstance Unit: Singleton {{\n let value: Unit = Unit.only\n}}{proof}");
        let mut project = Project::new_mock();
        project.mock("/mock/main.ac", &source);
        let id = project.expect_ok("main");
        let env = project.get_env_by_id(id).unwrap();
        let class = env.bindings.get_typeclass_for_name("Singleton").unwrap();
        assert_eq!(
            env.iter_goals().count(),
            if proof.is_empty() { 1 } else { 2 }
        );
        let container = env.nodes.iter().find(|node| matches!(&node.source().unwrap().source_type, SourceType::Instance(name, class) if name == "Unit" && class == "Singleton")).unwrap();
        let block = container.block().unwrap();
        assert!(container.proposition().is_none());
        assert!(!container.is_structural());
        assert!(!block.entry_scope().has_membership(id, "Unit", class));
        assert!(!block
            .env
            .bindings
            .proof_scope()
            .has_membership(id, "Unit", class));
        assert!(env.bindings.proof_scope().has_membership(id, "Unit", class));
        for goal in env.iter_goals() {
            assert!(!goal
                .goal_context()
                .unwrap()
                .proof_scope
                .has_membership(id, "Unit", class));
        }
        let goal = block.goal.as_ref().unwrap().value();
        assert!(!goal.is_generic());
        assert!(!goal.has_arbitrary());
        let mut generic_members = vec![];
        goal.find_constants(
            &|constant| {
                constant.name.module_id == id
                    && constant.name.local_name.to_string() == "Singleton.value"
            },
            &mut generic_members,
        );
        assert!(generic_members.is_empty());
        let last = source.lines().count() as u32 - 1;
        let selected = env.path_for_line(last).unwrap();
        assert!(!selected.is_empty());
        assert_success(&source);
    }
    let invalid =
        format!("{BIT}\n{SINGLETON}\ninstance Bit: Singleton {{\n let value: Bit = Bit.zero\n}}");
    assert_eq!(outcomes(&invalid, true), [Outcome::Exhausted]);
    assert_rejected_goal(&invalid);
}

#[test]
fn optional_law_free_proofs_are_checked_and_multiple_laws_share_one_goal() {
    let prefix = format!("{UNIT}\ntypeclass T: Marked {{\n flag: Bool\n}}\ninstance Unit: Marked {{\n let flag: Bool = true\n}}");
    let mut env = Environment::new_test();
    env.add(&prefix);
    assert_eq!(env.iter_goals().count(), 0);
    let explicit = format!("{prefix} by {{\n true\n}}");
    assert_eq!(
        outcomes(&explicit, true),
        [Outcome::Success, Outcome::Success]
    );
    let false_body = format!("{prefix} by {{\n false\n}}");
    assert_rejected_goal(&false_body);
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", &false_body);
    project.expect_ok("main");
    project.set_cache_policy(CachePolicy::MemoryOnly);
    let report = project.sync_build_report();
    assert_eq!(report.status, BuildStatus::Warning);
    assert_eq!(project.cached_build().num_modules(), 0);

    let source = format!("{UNIT}\ntypeclass T: Marked {{\n flag: Bool\n enabled {{ T.flag }}\n reflexive(x: T) {{ x = x }}\n}}\ninstance Unit: Marked {{\n let flag: Bool = true\n}}");
    let mut env = Environment::new_test();
    env.add(&source);
    assert_eq!(env.iter_goals().count(), 1);
    assert_success(&source);
    assert_rejected_goal(&source.replace("let flag: Bool = true", "let flag: Bool = false"));
    // No required member does not mean no law obligation.
    let only_law = format!("{UNIT}\ntypeclass T: Reflexive {{\n reflexive(x: T) {{ x = x }}\n}}\ninstance Unit: Reflexive {{}}");
    assert_eq!(outcomes(&only_law, true), [Outcome::Success]);
}

#[test]
fn bad_proof_bodies_roll_back_members_membership_nodes_and_ranges() {
    let mut env = Environment::new_test();
    env.add(&format!("{UNIT}\n{SINGLETON}"));
    let nodes = env.nodes.len();
    let last_line = env.last_line();
    for body in [
        "unknown",
        "Singleton.unique<Unit>(Unit.only)",
        "forall(x: Unit) { Singleton.unique(x) }",
    ] {
        let source = format!(
            "instance Unit: Singleton {{\n let value: Unit = Unit.only\n}} by {{\n {body}\n}}"
        );
        let error = env
            .add_statement(
                &mut Project::new_mock(),
                &Statement::parse_str(&source).unwrap(),
            )
            .unwrap_err();
        assert!(
            error.message().contains("unknown identifier")
                || error.message().contains("class bound")
                || error.message().contains("expected type"),
            "{error}"
        );
        assert_eq!(env.nodes.len(), nodes);
        assert_eq!(env.last_line(), last_line);
        assert!(!env.bindings.name_in_use("Unit.Singleton.value"));
        let class = env.bindings.get_typeclass_for_name("Singleton").unwrap();
        assert!(!env
            .bindings
            .proof_scope()
            .has_membership(env.module_id, "Unit", class));
    }
    env.add("instance Unit: Singleton {\n let value: Unit = Unit.only\n} by {\n forall(x: Unit) { x = Unit.only }\n}");
    assert_eq!(env.iter_goals().count(), 2);
}

#[test]
fn own_zero_argument_law_cannot_erase_the_denied_membership() {
    let mut env = Environment::new_test();
    env.add(&format!("{UNIT}\ntypeclass F: Flagged {{\n flag: Bool\n enabled {{ F.flag }}\n}}\naxiom inherited<F: Flagged> {{ F.enabled }}"));
    let before = env.nodes.len();
    for body in ["Flagged.enabled<Unit>", "inherited<Unit>"] {
        let source =
            format!("instance Unit: Flagged {{\n let flag: Bool = true\n}} by {{\n {body}\n}}");
        let error = env
            .add_statement(
                &mut Project::new_mock(),
                &Statement::parse_str(&source).unwrap(),
            )
            .unwrap_err();
        assert!(error.message().contains("class bound"), "{error}");
        assert_eq!(env.nodes.len(), before);
        assert!(!env.bindings.name_in_use("Unit.Flagged.flag"));
        let class = env.bindings.get_typeclass_for_name("Flagged").unwrap();
        assert!(!env
            .bindings
            .proof_scope()
            .has_membership(env.module_id, "Unit", class));
    }
    env.add("instance Unit: Flagged {\n let flag: Bool = true\n}");
    assert_eq!(env.iter_goals().count(), 1);
}

#[test]
fn denied_membership_survives_imports_and_cannot_be_hidden_in_a_generic_helper() {
    let mut project = Project::new_mock();
    project.mock("/mock/laws.ac", SINGLETON);
    project.mock(
        "/mock/helper.ac",
        "import laws\naxiom inherited<T: laws.Singleton>(x: T) { x = T.value }",
    );
    project.mock("/mock/main.ac", &format!("import laws\n{UNIT}\ninstance Unit: laws.Singleton {{\n let value: Unit = Unit.only\n}} by {{\n import helper\n helper.inherited(Unit.only)\n}}"));
    assert!(project
        .errors()
        .iter()
        .any(|(_, error)| error.message().contains("class bound")
            || error.message().contains("expected type")));
    project.set_cache_policy(CachePolicy::MemoryOnly);
    assert_eq!(project.sync_build_report().status, BuildStatus::Error);
    assert_eq!(project.cached_build().num_modules(), 0);

    let source = format!("{BIT}\n{SINGLETON}\ndefine equal<T>(left: T, right: T) -> Bool {{ left = right }}\naxiom inherited<T: Singleton>(left: T, right: T) {{ equal(left, right) }}\ninstance Bit: Singleton {{\n let value: Bit = Bit.zero\n}} by {{\n forall(x: Bit) {{ equal(x, Bit.zero) }}\n}}");
    assert_rejected_goal(&source);
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", &source);
    project.expect_ok("main");
    project.set_cache_policy(CachePolicy::MemoryOnly);
    assert_eq!(project.sync_build_report().status, BuildStatus::Warning);
    assert_eq!(project.cached_build().num_modules(), 0);
}

#[test]
fn lowering_preserves_legitimate_prior_membership_actuals() {
    let source = "inductive First {\n only\n}\ninductive Second {\n only\n}\ntypeclass T: Marked {\n flag: Bool\n enabled { T.flag }\n}\ninstance First: Marked {\n let flag: Bool = true\n}\ninstance Second: Marked {\n let flag: Bool = Marked.flag<First>\n}";
    let mut env = Environment::new_test();
    env.add(source);
    assert_eq!(env.iter_goals().count(), 2);
    let goal = env.iter_goals().last().unwrap().goal_context().unwrap();
    let mut lowered = vec![];
    goal.goal.value().find_constants(
        &|c| c.name.local_name.to_string() == "Second.Marked.flag",
        &mut lowered,
    );
    assert_eq!(lowered.len(), 1);
    let mut members = vec![];
    env.bindings
        .get_definition("Second.Marked.flag")
        .unwrap()
        .find_constants(
            &|c| c.name.local_name.to_string() == "Marked.flag",
            &mut members,
        );
    assert_eq!(members.len(), 1);
    assert_eq!(
        members[0].params,
        [env.bindings.get_type_for_name("First").unwrap().clone()]
    );
    assert_success(source);
}

#[test]
fn generated_existential_obligation_proof_replays_at_its_original_position() {
    let source = "type State: axiom\nlet seed: State = axiom\nlet chosen: State = axiom\ndefine combine(a: State, b: State) -> State { axiom }\naxiom chosen_right(a: State, b: State) { b = chosen -> combine(a, b) = chosen }\ndefine reachable<T>(start: T, finish: T, operation: (T, T) -> T) -> Bool { exists(d: T) { operation(start, d) = finish } }\ntypeclass T: Witness {\n seed: T\n chosen: T\n combine: (T, T) -> T\n witnessed { reachable(T.seed, T.chosen, T.combine) }\n}\ninstance State: Witness {\n let seed: State = seed\n let chosen: State = chosen\n let combine: (State, State) -> State = combine\n}\nlet future_chosen: State = chosen\ntheorem after { true }";
    // The direct existential is valid too; its completed proof condenses to no
    // emitted lines. A defined predicate gives the nonempty replay path below.
    assert_success(&source.replace(
        "witnessed { reachable(T.seed, T.chosen, T.combine) }",
        "witnessed { exists(d: T) { T.combine(T.seed, d) = T.chosen } }",
    ));
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", source);
    let module = project.expect_ok("main");
    let env = project.get_env_by_id(module).unwrap();
    let node = env.iter_goals().find(|node| matches!(&node.current().source().unwrap().source_type, SourceType::Instance(name, class) if name == "State" && class == "Witness")).unwrap();
    let goal = node.goal_context().unwrap();
    assert!(goal.insert_block);
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
        "an actual nonempty generated proof is required"
    );
    assert!(!code.join("\n").contains("future_chosen"));
    let lines = source.lines().collect::<Vec<_>>();
    let insertion = goal.proof_insertion_line as usize;
    assert_eq!(lines[insertion], "}");
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
    // The false child must fail. Later goals may also report the inconsistency
    // introduced by that failed child, so inspect the child independently.
    assert!(matches!(
        outcomes(&false_replay, false)[0],
        Outcome::Exhausted | Outcome::Constrained | Outcome::Timeout
    ));
    assert_eq!(outcomes(&false_replay, true)[0], Outcome::Exhausted);
    let mut rejected = Project::new_mock();
    rejected.mock("/mock/main.ac", &false_replay);
    rejected.expect_ok("main");
    let report = rejected.sync_build_report();
    assert_eq!(report.status, BuildStatus::Warning);
    assert!(report.goals_done >= 3);
    assert!(report.num_success < report.goals_total);
    assert_eq!(rejected.cached_build().num_modules(), 0);
}

#[test]
fn earlier_lemma_cannot_borrow_future_membership_to_prove_its_instance() {
    let source = format!("{BIT}\n{SINGLETON}\ndefine equal<T>(left: T, right: T) -> Bool {{ left = right }}\naxiom inherited<T: Singleton>(left: T, right: T) {{ equal(left, right) }}\ntheorem earlier(x: Bit) {{ equal(x, Bit.zero) }}\ninstance Bit: Singleton {{\n let value: Bit = Bit.zero\n}} by {{\n forall(x: Bit) {{ earlier(x) }}\n}}");
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", &source);
    let module = project.expect_ok("main");
    let env = project.get_env_by_id(module).unwrap();
    assert_eq!(env.iter_goals().count(), 2);
    for slow in [false, true] {
        let mut found = vec![];
        let mut callback = |mut prover: venticorn::prover::Prover, _| {
            found.push(prover.quick_shallow_search());
            true
        };
        if slow {
            project.for_each_prover_slow(env, &mut callback);
        } else {
            project.for_each_prover_fast(env, &mut callback);
        }
        assert_eq!(found.len(), 2);
        assert_eq!(found[0], Outcome::Exhausted);
        assert!(found
            .iter()
            .all(|outcome| matches!(outcome, Outcome::Success | Outcome::Exhausted)));
    }
    for policy in [CachePolicy::MemoryOnly, CachePolicy::Disabled] {
        project.set_cache_policy(policy);
        for dataset in [false, true] {
            let mut builder = project.builder(|_| {});
            if dataset {
                builder.create_dataset();
            }
            project.build(&mut builder);
            assert_eq!(builder.status, BuildStatus::Warning);
            assert_eq!(builder.goals_done, 2);
            assert!(builder.num_success < 2);
            assert_eq!(builder.num_cached, 0);
            assert!(builder
                .cache()
                .unwrap()
                .get(&venticorn::module::ModuleRef::Name("main".into()))
                .is_none());
        }
    }
}
