use std::collections::HashSet;
use venticorn::environment::Environment;
use venticorn::module::ModuleRef;
use venticorn::project::{ImportFilter, Project};
use venticorn::prover::{Outcome, Prover};

fn names(values: &[&str]) -> HashSet<String> {
    values.iter().map(|value| value.to_string()).collect()
}

#[test]
fn export_filter_preserves_shared_datatype_principles_and_anonymous_facts() {
    let mut env = Environment::new_test();
    env.add("inductive Choice {\n one\n two\n three\n}\ntheorem { true }\ndefine identity<T>(x: T) -> T { x }");
    assert_eq!(
        env.exported_facts().len(),
        env.exported_facts_filtered(None).len()
    );
    assert!(env
        .exported_facts_filtered(Some(&HashSet::new()))
        .is_empty());
    let selected = env.exported_facts_filtered(Some(&names(&["Choice.three", "6", "identity"])));
    assert_eq!(selected.len(), 4);
    assert_eq!(
        selected
            .iter()
            .filter(
                |fact| fact.as_proposition().unwrap().source.name().as_deref()
                    == Some("Choice.three")
            )
            .count(),
        2
    );
    assert!(selected
        .iter()
        .any(|fact| fact.as_proposition().unwrap().source.name().as_deref() == Some("6")));
    assert!(selected
        .iter()
        .any(|fact| fact.as_proposition().unwrap().source.name().as_deref() == Some("identity")));
}

fn project() -> (Project, u16) {
    let mut project = Project::new_mock();
    project.mock(
        "/mock/left.ac",
        "let flag: Bool = axiom\naxiom same { flag }",
    );
    project.mock(
        "/mock/right.ac",
        "let flag: Bool = axiom\naxiom same { flag }",
    );
    project.mock("/mock/main.ac", "import left\nimport right\naxiom local { right.flag }\ntheorem selected { left.flag }\ntheorem local_goal { right.flag }\ntheorem premise(a: Bool) { a implies a } by { if a { a } }");
    let id = project.expect_ok("main");
    (project, id)
}

#[test]
fn imported_names_are_qualified_by_defining_module() {
    let (project, id) = project();
    let left_id = project
        .get_env_by_ref(&ModuleRef::Name("left".into()))
        .unwrap()
        .module_id;
    let right_id = project
        .get_env_by_ref(&ModuleRef::Name("right".into()))
        .unwrap()
        .module_id;
    let mut filter = ImportFilter::new();
    filter.insert(ModuleRef::Name("left".into()), names(&["same"]));
    let selected = project.imported_facts_filtered(id, Some(&filter));
    assert_eq!(selected.len(), 1);
    assert_eq!(selected[0].as_proposition().unwrap().source.module, left_id);
    assert_ne!(
        selected[0].as_proposition().unwrap().source.module,
        right_id
    );
    assert_eq!(
        selected[0]
            .as_proposition()
            .unwrap()
            .source
            .name()
            .as_deref(),
        Some("same")
    );
    assert!(project
        .imported_facts_filtered(id, Some(&ImportFilter::new()))
        .is_empty());
    assert_eq!(
        project.imported_facts(id).len(),
        project.imported_facts_filtered(id, None).len()
    );
    filter.insert(ModuleRef::Name("right".into()), names(&["same"]));
    assert_eq!(project.imported_facts_filtered(id, Some(&filter)).len(), 2);
}

#[test]
fn cursor_and_fast_filters_keep_local_facts_and_premises() {
    let (project, id) = project();
    let env = project.get_env_by_id(id).unwrap();
    let mut filter = ImportFilter::new();
    filter.insert(ModuleRef::Name("left".into()), names(&["same"]));
    let mut cursor_results = vec![];
    for node in env.iter_goals() {
        let goal = node.goal_context().unwrap();
        let mut prover = Prover::new(&project, false);
        for fact in node.usable_facts_filtered(&project, Some(&filter)) {
            prover.add_fact(fact);
        }
        prover.set_goal(&goal);
        cursor_results.push((goal.description().to_string(), prover.verification_search()));
    }
    let mut fast_results = vec![];
    project.for_each_prover_fast_filtered(env, Some(&filter), &mut |mut prover, goal| {
        fast_results.push((goal.description().to_string(), prover.verification_search()));
        true
    });
    assert_eq!(cursor_results, fast_results);
    assert!(!fast_results.is_empty());
    assert!(fast_results
        .iter()
        .all(|(_, result)| *result == Outcome::Success));
    let selected = env.get_node_by_name("selected");
    let mut prover = Prover::new(&project, false);
    for fact in selected.usable_facts_filtered(&project, Some(&ImportFilter::new())) {
        prover.add_fact(fact);
    }
    prover.set_goal(&selected.goal_context().unwrap());
    assert_eq!(prover.verification_search(), Outcome::Exhausted);
    let mut legacy = vec![];
    project.for_each_prover_fast(env, &mut |mut prover, goal| {
        legacy.push((goal.description().to_string(), prover.verification_search()));
        true
    });
    let mut explicit_none = vec![];
    project.for_each_prover_fast_filtered(env, None, &mut |mut prover, goal| {
        explicit_none.push((goal.description().to_string(), prover.verification_search()));
        true
    });
    assert_eq!(legacy, explicit_none);
}

#[test]
fn reexports_select_defining_sources_instead_of_local_alias_spellings() {
    let mut project = Project::new_mock();
    project.mock("/mock/original.ac", "define identity<T>(x: T) -> T { x }");
    project.mock(
        "/mock/bridge.ac",
        "from original import identity\nlet alias: Bool -> Bool = identity<Bool>",
    );
    project.mock(
        "/mock/main.ac",
        "from bridge import identity, alias\ntheorem goal { identity(true) }\ntheorem alias_goal { alias(true) }",
    );
    let id = project.expect_ok("main");
    let original = project
        .get_env_by_ref(&ModuleRef::Name("original".into()))
        .unwrap()
        .module_id;
    let mut filter = ImportFilter::new();
    filter.insert(ModuleRef::Name("original".into()), names(&["identity"]));
    let selected = project.imported_facts_filtered(id, Some(&filter));
    assert_eq!(selected.len(), 1);
    assert_eq!(
        selected[0].as_proposition().unwrap().source.module,
        original
    );
    assert_eq!(
        selected[0]
            .as_proposition()
            .unwrap()
            .source
            .name()
            .as_deref(),
        Some("identity")
    );
    let node = project.get_env_by_id(id).unwrap().get_node_by_name("goal");
    let mut prover = Prover::new(&project, false);
    for fact in node.usable_facts_filtered(&project, Some(&filter)) {
        prover.add_fact(fact);
    }
    prover.set_goal(&node.goal_context().unwrap());
    assert_eq!(prover.verification_search(), Outcome::Success);
    // A newly declared alias has its own defining equation. Selecting the
    // original definition does not implicitly admit that separate bridge fact.
    let alias_goal = project
        .get_env_by_id(id)
        .unwrap()
        .get_node_by_name("alias_goal");
    for include_alias in [false, true] {
        if include_alias {
            filter.insert(ModuleRef::Name("bridge".into()), names(&["alias"]));
        }
        let mut prover = Prover::new(&project, false);
        let facts = alias_goal.usable_facts_filtered(&project, Some(&filter));
        assert_eq!(
            facts.iter().any(
                |fact| fact.as_proposition().unwrap().source.name().as_deref() == Some("alias")
            ),
            include_alias
        );
        for fact in facts {
            prover.add_fact(fact);
        }
        prover.set_goal(&alias_goal.goal_context().unwrap());
        let outcome = prover.verification_search();
        if include_alias {
            assert_eq!(outcome, Outcome::Success);
        } else {
            assert!(
                matches!(
                    outcome,
                    Outcome::Exhausted | Outcome::Constrained | Outcome::Timeout
                ),
                "{outcome:?}"
            );
        }
    }
    filter.clear();
    filter.insert(ModuleRef::Name("original".into()), names(&["alias"]));
    assert!(project
        .imported_facts_filtered(id, Some(&filter))
        .is_empty());
    filter.clear();
    filter.insert(ModuleRef::Name("bridge".into()), names(&["identity"]));
    assert!(project
        .imported_facts_filtered(id, Some(&filter))
        .is_empty());
}
