use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;
use venticorn::build_cache::PremiseSet;
use venticorn::builder::{BuildStatus, Builder};
use venticorn::module::ModuleRef;
use venticorn::persistent_cache::CachePolicy;
use venticorn::project::Project;

fn named(name: &str) -> ModuleRef {
    ModuleRef::Name(name.into())
}
fn source() -> &'static str {
    "let first: Bool = axiom\nlet second: Bool = axiom\nlet spare: Bool = axiom\naxiom left { first }\naxiom right { second }\naxiom unused { spare }\ntheorem both { first and second } by {\n first\n second\n}\n"
}
fn hints(project: &Project, module: &ModuleRef) -> BTreeMap<String, PremiseSet> {
    let report = project.sync_build_report();
    assert_eq!(report.status, BuildStatus::Good);
    report
        .cache
        .unwrap()
        .get(module)
        .unwrap()
        .theorem_premises()
        .clone()
}

#[test]
fn completed_theorem_unions_reachable_sources_and_retains_them_on_reuse() {
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", source());
    let original = hints(&project, &named("main"));
    let selected = &original["both"][&named("main")];
    assert!(
        selected.contains("left") && selected.contains("right"),
        "{selected:?}"
    );
    assert!(
        !selected.contains("unused") && !selected.contains("both"),
        "{selected:?}"
    );
    assert_eq!(hints(&project, &named("main")), original);
    project
        .update_file(
            PathBuf::from("/mock/main.ac"),
            &format!("{}theorem extra {{ true }}\n", source()),
            1,
        )
        .unwrap();
    assert_eq!(
        project
            .get_env_by_ref(&named("main"))
            .unwrap()
            .iter_goals()
            .count(),
        4
    );
    let report = project.sync_build_report();
    assert_eq!(report.status, BuildStatus::Good);
    assert_eq!((report.num_success, report.num_cached), (1, 3));
    let cache = report.cache.unwrap();
    let expanded = cache.get(&named("main")).unwrap().theorem_premises();
    assert_eq!(expanded["both"], original["both"]);
    assert_eq!(expanded["extra"], PremiseSet::new());
}

#[test]
fn canonical_hints_survive_reordered_load_ids_and_standalone_files() {
    let mut project = Project::new_mock();
    project.mock(
        "/outside/standalone.ac",
        "let flag: Bool = axiom\naxiom known { flag }\ntheorem goal { flag }",
    );
    let file = ModuleRef::File(PathBuf::from("/outside/standalone.ac"));
    let original = hints(&project, &file);
    assert_eq!(
        original["goal"],
        BTreeMap::from([(file.clone(), BTreeSet::from(["known".into()]))])
    );
    let original_id = project.get_env_by_ref(&file).unwrap().module_id;
    project.mock("/mock/earlier.ac", "theorem extra { true }");
    assert_ne!(
        project.get_env_by_ref(&file).unwrap().module_id,
        original_id
    );
    assert_eq!(hints(&project, &file), original);
}

#[test]
fn unverified_or_interrupted_theorems_publish_no_partial_hints() {
    let mut project = Project::new_mock();
    project.mock(
        "/mock/main.ac",
        "theorem bad { true } by {\n true\n false\n}\n",
    );
    let failed = project.sync_build_report();
    assert_eq!(failed.status, BuildStatus::Warning);
    assert!(failed.cache.unwrap().get(&named("main")).is_none());
    project
        .update_file(PathBuf::from("/mock/main.ac"), source(), 1)
        .unwrap();
    project
        .get_env_by_ref(&named("main"))
        .unwrap()
        .get_node_by_name("both");
    let mut builder = Builder::new(|event| {
        if event.verified.is_some() {
            project.stop_build();
        }
    });
    project.build(&mut builder);
    assert_eq!(builder.status, BuildStatus::Error);
    assert!(builder.cache().is_none());
}

#[test]
fn disabled_and_dataset_builds_do_not_extract_or_publish_hints() {
    for dataset in [false, true] {
        let mut project = Project::new_mock();
        project.mock("/mock/main.ac", source());
        if !dataset {
            project.set_cache_policy(CachePolicy::Disabled);
        }
        let mut builder = project.builder(|_| {});
        if dataset {
            builder.create_dataset();
        }
        project.build(&mut builder);
        assert_eq!(builder.status, BuildStatus::Good);
        assert!(builder
            .cache()
            .unwrap()
            .get(&named("main"))
            .unwrap()
            .theorem_premises()
            .is_empty());
    }
}

#[test]
fn disk_result_promotion_preserves_memory_and_persisted_hints() {
    let root = std::env::temp_dir().join(format!("venticorn_premises_{}", std::process::id()));
    std::fs::create_dir(&root).unwrap();
    std::fs::write(root.join("main.ac"), source()).unwrap();
    let make_project = || {
        let mut project = Project::from_library_root(root.clone()).unwrap();
        project.set_cache_policy(CachePolicy::ReadWrite);
        project.add_all_targets().unwrap();
        project
    };
    let project = make_project();
    let learned = hints(&project, &named("main"));
    assert!(!learned.is_empty());
    assert_eq!(hints(&project, &named("main")), learned);
    let reopened = make_project();
    let report = reopened.sync_build_report();
    assert_eq!(report.status, BuildStatus::Good);
    assert_eq!(report.num_success, 0);
    assert!(report.num_cached > 0);
    assert_eq!(
        report
            .cache
            .unwrap()
            .get(&named("main"))
            .unwrap()
            .theorem_premises(),
        &learned
    );
    std::fs::remove_dir_all(root).unwrap();
}
