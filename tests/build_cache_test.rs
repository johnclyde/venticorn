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

#[test]
fn synchronous_reports_preserve_events_and_actual_completion_counts() {
    let mut project = Project::new_mock();
    project.mock("/mock/one.ac", "theorem one { true }");
    project.mock("/mock/two.ac", "theorem two { true }");
    let report = project.sync_build_report();
    assert_eq!(report.status, BuildStatus::Good);
    assert_eq!(
        (report.num_success, report.goals_done, report.goals_total),
        (2, 2, 2)
    );
    assert_eq!(report.events.last().unwrap().progress, Some((2, 2)));
    assert_eq!(report.cache.unwrap().num_modules(), 2);
    // The established API still reports the same status and verified goal ranges.
    let (status, events) = project.sync_build();
    assert_eq!(status, BuildStatus::Good);
    assert_eq!(events.iter().filter(|e| e.verified.is_some()).count(), 2);
}

#[test]
fn synchronous_reports_distinguish_empty_failed_and_interrupted_builds() {
    let empty = Project::new_mock().sync_build_report();
    assert_eq!((empty.goals_done, empty.goals_total), (0, 0));
    assert_eq!(empty.events.last().unwrap().progress, Some((0, 0)));
    assert_eq!(empty.cache.unwrap().num_modules(), 0);

    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", "theorem impossible { false }");
    let failed = project.sync_build_report();
    assert_eq!(failed.status, BuildStatus::Warning);
    assert_eq!(
        (failed.num_success, failed.goals_done, failed.goals_total),
        (0, 1, 1)
    );
    assert_eq!(failed.events.last().unwrap().progress, Some((1, 1)));
    assert_eq!(failed.cache.unwrap().num_modules(), 0);

    project.stop_build();
    assert!(project.sync_build_report().cache.is_none());
    project.allow_build();
    assert!(project.sync_build_report().cache.is_some());

    project.mock("/mock/broken.ac", "theorem broken {");
    let invalid = project.sync_build_report();
    assert_eq!(invalid.status, BuildStatus::Error);
    assert_eq!(invalid.goals_done, 0);
    assert!(invalid.cache.is_none());
}

#[test]
fn completed_cache_can_be_taken_once_without_consuming_statistics() {
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", "theorem identity { true }");
    let mut builder = Builder::new(|_| {});
    assert!(builder.take_cache().is_none());
    project.build(&mut builder);
    let stats = (
        builder.status,
        builder.num_success,
        builder.goals_done,
        builder.goals_total,
    );
    let cache = builder.take_cache().unwrap();
    assert_eq!(cache.num_modules(), 1);
    assert!(builder.cache().is_none());
    assert!(builder.take_cache().is_none());
    assert_eq!(
        stats,
        (
            builder.status,
            builder.num_success,
            builder.goals_done,
            builder.goals_total
        )
    );
}
