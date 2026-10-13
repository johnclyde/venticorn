// Modified for Venticorn.

use std::path::PathBuf;
use std::time::Duration;

use venticorn::builder::Builder;
use venticorn::module::ModuleRef;
use venticorn::project::Project;
use venticorn::prover::{Outcome, Prover};

#[test]
fn diagnostics_preserve_file_identity_for_success_and_warning() {
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", "theorem impossible { false }");
    let environment = project
        .get_env_by_ref(&ModuleRef::from_name("main"))
        .unwrap();
    let goal = environment
        .iter_goals()
        .next()
        .unwrap()
        .goal_context()
        .unwrap();
    let prover = Prover::new(&project, false);
    let file = ModuleRef::File(PathBuf::from("/outside/proof.ac"));
    let mut events = Vec::new();
    {
        let mut builder = Builder::new(|event| events.push(event));
        builder.module_proving_started(&file);
        builder.module_proving_complete(&file);
        builder.module_proving_started(&file);
        builder.search_finished(&prover, &goal, Outcome::Exhausted, Duration::ZERO);
        builder.module_proving_complete(&file);
    }
    let diagnostics: Vec<_> = events
        .into_iter()
        .filter_map(|event| event.diagnostic)
        .collect();
    assert_eq!(diagnostics.len(), 2);
    assert_eq!(diagnostics[0].0, file);
    assert!(diagnostics[0].1.is_none());
    assert_eq!(diagnostics[1].0, file);
    assert!(diagnostics[1].1.is_some());
}

#[test]
fn external_file_diagnostics_follow_updates_and_close() {
    use venticorn::builder::BuildStatus;
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", "theorem identity { true }");
    let path = PathBuf::from("/outside/proof.ac");
    let reference = ModuleRef::File(path.clone());
    for (version, source, expected, diagnostic_present) in [
        (
            1,
            "theorem impossible { false }",
            BuildStatus::Warning,
            true,
        ),
        (2, "theorem identity { true }", BuildStatus::Good, false),
        (3, "theorem unfinished {", BuildStatus::Error, true),
    ] {
        project.update_file(path.clone(), source, version).unwrap();
        let (status, events) = project.sync_build();
        assert_eq!(status, expected);
        let diagnostic = events
            .iter()
            .filter_map(|event| event.diagnostic.as_ref())
            .find(|(module_ref, _)| module_ref == &reference)
            .expect("external-file diagnostic");
        assert_eq!(diagnostic.1.is_some(), diagnostic_present);
    }
    project.close_file(path.clone()).unwrap();
    assert!(!project.open_files.contains_key(&path));
    assert!(project.get_env_by_ref(&reference).is_none());
    let (status, events) = project.sync_build();
    assert_eq!(status, BuildStatus::Good);
    assert!(events
        .iter()
        .filter_map(|event| event.diagnostic.as_ref())
        .all(|(module_ref, _)| module_ref != &reference));
}

#[test]
fn invalid_file_updates_and_closes_preserve_existing_state() {
    use venticorn::builder::BuildStatus;
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", "theorem identity { true }");
    let invalid = PathBuf::from("/outside/not_source.txt");
    assert!(project
        .update_file(invalid.clone(), "theorem identity { true }", 1)
        .is_err());
    assert!(!project.open_files.contains_key(&invalid));
    project
        .open_files
        .insert(invalid.clone(), ("editor content".to_string(), 1));
    assert!(project.close_file(invalid.clone()).is_err());
    assert_eq!(project.open_files[&invalid].0, "editor content");
    assert_eq!(project.sync_build().0, BuildStatus::Good);
}

#[test]
fn first_editor_open_reloads_dependencies_cached_from_disk() {
    use std::fs;
    use venticorn::builder::BuildStatus;
    struct Directory(PathBuf);
    impl Drop for Directory {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }
    let directory = Directory(std::env::temp_dir().join(format!(
        "venticorn_cached_dependency_{}",
        std::process::id()
    )));
    fs::create_dir(&directory.0).unwrap();
    let dependency = directory.0.join("dependency.ac");
    fs::write(&dependency, "let value: Bool = true").unwrap();
    fs::write(
        directory.0.join("main.ac"),
        "import dependency\ntheorem dependency_holds { dependency.value }",
    )
    .unwrap();
    let mut project = Project::new(directory.0.to_str().unwrap());
    assert!(project.add_target_by_name("main"));
    assert_eq!(project.sync_build().0, BuildStatus::Good);
    assert!(!project.open_files.contains_key(&dependency));

    project
        .update_file(dependency.clone(), "let replacement: Bool = false", 1)
        .unwrap();
    // Both the dependency and its importer must use the editor content. The
    // importer can no longer resolve the removed value.
    assert_eq!(project.sync_build().0, BuildStatus::Error);

    project.close_file(dependency).unwrap();
    assert_eq!(project.sync_build().0, BuildStatus::Good);
}

#[test]
fn opening_missing_dependency_recovers_cached_import_errors() {
    use venticorn::builder::BuildStatus;
    let mut project = Project::new_mock();
    let external = PathBuf::from("/outside/proof.ac");
    project
        .update_file(
            external.clone(),
            "import missing\ntheorem identity { true }",
            1,
        )
        .unwrap();
    assert_eq!(project.sync_build().0, BuildStatus::Error);

    project
        .update_file(
            PathBuf::from("/mock/missing.ac"),
            "theorem identity { true }",
            1,
        )
        .unwrap();
    assert!(project.get_env_by_ref(&ModuleRef::File(external)).is_some());
    assert_eq!(project.sync_build().0, BuildStatus::Good);
}
