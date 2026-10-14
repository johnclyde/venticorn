// Modified for Venticorn: only complete successful modules produce cache metadata.
use venticorn::builder::{BuildStatus, Builder};
use venticorn::module::ModuleRef;
use venticorn::project::Project;

fn named(name: &str) -> ModuleRef {
    ModuleRef::Name(name.into())
}

#[test]
fn completed_modules_record_identity_dependencies_and_full_goal_ranges() {
    let mut project = Project::new_mock();
    project.mock("/mock/dependency.ac", "theorem identity { true }");
    project.mock(
        "/mock/main.ac",
        "import dependency\ntheorem outer { true } by {\n true\n}\n",
    );
    let mut builder = Builder::new(|_| {});
    assert!(builder.cache().is_none());
    project.build(&mut builder);
    assert_eq!(builder.status, BuildStatus::Good);
    let cache = builder.cache().unwrap();
    assert_eq!(cache.num_modules(), 2);
    let main = cache.get(&named("main")).unwrap();
    assert_eq!(main.direct_dependencies(), &[named("dependency")]);
    assert_eq!(main.verified(), &[(2, 2), (1, 3)]);
    let id = project.load_module_by_name("main").unwrap();
    assert_eq!(main.fingerprint(), project.get_hash(id).unwrap());
}

#[test]
fn warnings_exclude_the_entire_affected_module() {
    let mut project = Project::new_mock();
    project.mock(
        "/mock/afailed.ac",
        "theorem identity { true }\ntheorem impossible { false }",
    );
    project.mock("/mock/zverified.ac", "theorem identity { true }");
    let mut builder = Builder::new(|_| {});
    project.build(&mut builder);
    assert_eq!(builder.status, BuildStatus::Warning);
    let cache = builder.cache().unwrap();
    assert_eq!(cache.num_modules(), 1);
    assert!(cache.get(&named("afailed")).is_none());
    assert!(cache.get(&named("zverified")).is_some());
}

#[test]
fn loading_failure_never_exposes_cache_metadata() {
    let mut project = Project::new_mock();
    project.mock("/mock/good.ac", "theorem identity { true }");
    project.mock("/mock/broken.ac", "theorem broken {");
    let mut builder = Builder::new(|_| {});
    project.build(&mut builder);
    assert_eq!(builder.status, BuildStatus::Error);
    assert!(builder.cache().is_none());
}

#[test]
fn canceled_builds_discard_even_previously_completed_modules() {
    let mut project = Project::new_mock();
    project.mock("/mock/first.ac", "theorem identity { true }");
    project.mock("/mock/second.ac", "theorem identity { true }");
    let mut builder = Builder::new(|event| {
        if event.verified.is_some() {
            project.stop_build();
        }
    });
    project.build(&mut builder);
    assert!(builder.cache().is_none());
}

#[test]
fn zero_goal_modules_are_complete_but_canceled_empty_builds_are_not_cacheable() {
    let mut project = Project::new_mock();
    project.mock("/mock/empty.ac", "");
    let mut builder = Builder::new(|_| {});
    project.build(&mut builder);
    let cache = builder.cache().unwrap();
    assert_eq!(cache.num_modules(), 1);
    assert!(cache.get(&named("empty")).unwrap().verified().is_empty());
    project.stop_build();
    let mut canceled = Builder::new(|_| {});
    project.build(&mut canceled);
    assert!(canceled.cache().is_none());
}
