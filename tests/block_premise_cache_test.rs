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
    // The native route also uses the scoped body fact after simplification;
    // that source remains metadata until the body has been proved in order.
    let names: &[&str] = if cfg!(feature = "onnx") {
        &["6", "known"]
    } else {
        &["known"]
    };
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
