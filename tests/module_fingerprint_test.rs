// Modified for Venticorn: source snapshot identity is independent of load IDs and editor versions.
use std::path::PathBuf;
use venticorn::project::{ModuleFingerprint, Project};

fn fingerprint(project: &mut Project, module: &str) -> ModuleFingerprint {
    let id = project.load_module_by_name(module).unwrap();
    project.get_hash(id).unwrap()
}

#[test]
fn module_fingerprints_follow_source_bytes_not_editor_versions() {
    let mut project = Project::new_mock();
    let path = PathBuf::from("/mock/main.ac");
    let text = "theorem identity { true }";
    project.update_file(path.clone(), text, 1).unwrap();
    let first = fingerprint(&mut project, "main");
    project.update_file(path.clone(), text, 2).unwrap();
    assert_eq!(first, fingerprint(&mut project, "main"));
    project.update_file(path, &format!("{text}\n"), 3).unwrap();
    assert_ne!(first, fingerprint(&mut project, "main"));
}

#[test]
fn source_fingerprints_are_stable_when_module_ids_change() {
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", "theorem identity { true }");
    let first = fingerprint(&mut project, "main");
    let first_id = project.load_module_by_name("main").unwrap();
    let mut reordered = Project::new_mock();
    reordered.mock("/mock/main.ac", "theorem identity { true }");
    reordered.mock("/mock/other.ac", "theorem other { true }");
    assert_ne!(first_id, reordered.load_module_by_name("main").unwrap());
    assert_eq!(first, fingerprint(&mut reordered, "main"));
}

#[test]
fn errors_and_missing_modules_have_no_usable_fingerprint() {
    let mut project = Project::new_mock();
    project.mock("/mock/broken.ac", "theorem broken {");
    let broken = project.load_module_by_name("broken").unwrap();
    assert!(project.get_hash(broken).is_none());
    assert!(project.get_hash(0).is_none());
    assert!(project.get_hash(u16::MAX).is_none());
    project.mock("/mock/cycle.ac", "import cycle");
    let cycle = project.load_module_by_name("cycle").unwrap();
    assert!(project.get_hash(cycle).is_none());
}

#[test]
fn fingerprints_include_transitive_dependencies_but_ignore_unrelated_files() {
    let mut project = Project::new_mock();
    project.mock("/mock/leaf.ac", "let value: Bool = true");
    project.mock(
        "/mock/middle.ac",
        "import leaf\nlet value: Bool = leaf.value",
    );
    project.mock(
        "/mock/main.ac",
        "import middle\ntheorem identity { middle.value = middle.value }",
    );
    let first = fingerprint(&mut project, "main");
    let first_id = project.load_module_by_name("main").unwrap();
    project.mock("/mock/unrelated.ac", "theorem other { true }");
    assert_ne!(first_id, project.load_module_by_name("main").unwrap());
    assert_eq!(first, fingerprint(&mut project, "main"));
    project
        .update_file(PathBuf::from("/mock/leaf.ac"), "let value: Bool = false", 1)
        .unwrap();
    assert_ne!(first, fingerprint(&mut project, "main"));
    project
        .update_file(PathBuf::from("/mock/leaf.ac"), "let value: Bool = true", 2)
        .unwrap();
    assert_eq!(first, fingerprint(&mut project, "main"));
}

#[test]
fn failed_transitive_dependency_cannot_retain_an_old_fingerprint() {
    let mut project = Project::new_mock();
    project.mock("/mock/leaf.ac", "let value: Bool = true");
    project.mock("/mock/middle.ac", "import leaf");
    project.mock("/mock/main.ac", "import middle");
    let original = fingerprint(&mut project, "main");
    project
        .update_file(PathBuf::from("/mock/leaf.ac"), "theorem broken {", 1)
        .unwrap();
    for name in ["leaf", "middle", "main"] {
        let id = project.load_module_by_name(name).unwrap();
        assert!(project.get_hash(id).is_none(), "{name}");
    }
    project
        .update_file(PathBuf::from("/mock/leaf.ac"), "let value: Bool = true", 2)
        .unwrap();
    assert_eq!(original, fingerprint(&mut project, "main"));
}
