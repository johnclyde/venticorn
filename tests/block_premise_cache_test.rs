use std::collections::{BTreeMap, BTreeSet};
use venticorn::builder::BuildStatus;
use venticorn::module::ModuleRef;
use venticorn::project::Project;

fn main_module() -> ModuleRef {
    ModuleRef::Name("main".into())
}
const FACTS: &str =
    "type Foo: axiom\nlet p: Foo -> Bool = axiom\nlet a: Foo = axiom\naxiom known { p(a) }\n";

#[test]
fn function_definition_blocks_retain_and_use_complete_premise_advice() {
    let source = format!("{FACTS}let choose(x: Foo) -> y: Foo satisfy {{ p(y) }} by {{\n p(a)\n}}");
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", &source);
    let cold = project.sync_build_report();
    assert_eq!(cold.status, BuildStatus::Good);
    assert_eq!(cold.num_success, 2);
    // Scoped body facts remain available in order but are not reusable imported advice.
    let names: &[&str] = &["known"];
    let expected = BTreeMap::from([(
        main_module(),
        names
            .iter()
            .map(|name| name.to_string())
            .collect::<BTreeSet<_>>(),
    )]);
    let cache = cold.cache.unwrap();
    let module = cache.get(&main_module()).unwrap();
    assert_eq!(module.block_premises()["choose"], expected);
    assert_eq!(module.block_premises(), module.theorem_premises());
    let warm = project.sync_build_report();
    assert_eq!((warm.num_success, warm.num_cached), (0, 2));
    assert_eq!(
        warm.cache
            .unwrap()
            .get(&main_module())
            .unwrap()
            .block_premises()["choose"],
        expected
    );
    project.check_hashes = false;
    let mut guided = project.builder(|_| {});
    project.build(&mut guided);
    assert_eq!(guided.status, BuildStatus::Good);
    assert_eq!((guided.num_success, guided.num_cached), (2, 0));
    assert!(guided.hinted_searches > 0 && guided.hinted_successes > 0);
    let mut dataset = project.builder(|_| {});
    dataset.create_dataset();
    project.build(&mut dataset);
    assert_eq!(dataset.status, BuildStatus::Good);
    assert_eq!(
        (
            dataset.searches_total,
            dataset.hinted_searches,
            dataset.num_cached
        ),
        (2, 0, 0)
    );
    project.mock("/mock/main.ac", &source.replace("p(y)", "y != y"));
    let rejected = project.sync_build_report();
    assert_eq!(rejected.status, BuildStatus::Warning);
    assert!(rejected.cache.unwrap().get(&main_module()).is_none());
}

#[test]
fn constraint_blocks_keep_existence_obligations_and_use_named_advice() {
    use venticorn::acorn_value::AcornValue;
    let source = format!("{FACTS}structure Checked {{\n value: Foo\n}} constraint {{ p(value) }}");
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", &source);
    let env = project.get_env_by_ref(&main_module()).unwrap();
    let node = env
        .nodes
        .iter()
        .find(|node| node.block().is_some())
        .unwrap();
    assert_eq!(node.proposition().unwrap().value, AcornValue::Bool(true));
    assert_eq!(
        node.proposition().unwrap().source.fact_name().as_deref(),
        Some("Checked.constraint")
    );
    assert_eq!(node.proposition().unwrap().source.range.start.line, 4);
    assert_eq!(node.proposition().unwrap().source.range.end.line, 6);
    let block = node.block().unwrap();
    assert!(
        matches!(block.goal.as_ref().unwrap().value(), AcornValue::Exists(types, _) if types.len() == 1)
    );
    assert!(!block.env.bindings.has_type_name("Checked"));
    assert!(!block.env.bindings.has_identifier("Checked.new"));
    let cold = project.sync_build_report();
    assert_eq!(cold.status, BuildStatus::Good);
    assert_eq!(cold.num_success, 1);
    let expected = BTreeMap::from([(main_module(), BTreeSet::from(["known".into()]))]);
    assert_eq!(
        cold.cache
            .unwrap()
            .get(&main_module())
            .unwrap()
            .block_premises()["Checked.constraint"],
        expected
    );
    let warm = project.sync_build_report();
    assert_eq!((warm.num_success, warm.num_cached), (0, 1));
    project.check_hashes = false;
    let mut guided = project.builder(|_| {});
    project.build(&mut guided);
    assert_eq!(guided.status, BuildStatus::Good);
    assert_eq!(
        (
            guided.searches_total,
            guided.hinted_searches,
            guided.hinted_successes,
            guided.num_cached
        ),
        (1, 1, 1, 0)
    );
    project.mock(
        "/mock/main.ac",
        &source.replace("p(value)", "value != value"),
    );
    let rejected = project.sync_build_report();
    assert_eq!(rejected.status, BuildStatus::Warning);
    assert_eq!(rejected.num_success, 0);
    assert!(rejected.cache.unwrap().get(&main_module()).is_none());
}

#[test]
fn goal_free_declarations_do_not_create_premise_advice_or_search_work() {
    let mut project = Project::new_mock();
    project.mock(
        "/mock/main.ac",
        "structure Plain<T> {\n value: T\n}\ndefine identity<T>(value: T) -> T { value }",
    );
    project.check_hashes = false;
    let mut builder = project.builder(|_| {});
    project.build(&mut builder);
    assert_eq!(builder.status, BuildStatus::Good);
    assert_eq!(
        (
            builder.goals_total,
            builder.searches_total,
            builder.hinted_searches
        ),
        (0, 0, 0)
    );
    assert!(builder
        .cache()
        .unwrap()
        .get(&main_module())
        .unwrap()
        .block_premises()
        .is_empty());
}
