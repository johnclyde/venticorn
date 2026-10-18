use super::*;

#[test]
fn completed_policy_cannot_be_relabelled_when_publishing_to_disk() {
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "venticorn_scope_publish_{}_{}",
        std::process::id(),
        nonce
    ));
    std::fs::create_dir(&root).unwrap();
    struct Cleanup(PathBuf);
    impl Drop for Cleanup {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }
    let _cleanup = Cleanup(root.clone());
    std::fs::write(
        root.join("main.ac"),
        "type Item: axiom\ntypeclass T: Marked {\n flag: Bool\n}\ntheorem goal { true }\n",
    )
    .unwrap();
    let mut project = Project::from_library_root(root.clone()).unwrap();
    assert!(project.add_target_by_name("main"));
    let id = project.load_module_by_name("main").unwrap();
    let report = project.sync_build_report();
    assert_eq!(report.status, BuildStatus::Good);
    assert_eq!((report.num_success, report.goals_done), (1, 1));
    let completed = report.cache.unwrap();
    assert!(!root.join(".venticorn-cache").exists());
    project.set_cache_policy(CachePolicy::ReadWrite);
    project.persist_completed(&completed);
    let records = || {
        std::fs::read_dir(root.join(".venticorn-cache"))
            .unwrap()
            .map(|e| e.unwrap().path())
            .collect::<Vec<_>>()
    };
    let files = records();
    assert_eq!(files.len(), 1);
    let original = std::fs::read(&files[0]).unwrap();
    std::fs::remove_file(&files[0]).unwrap();
    let Module::Ok(env) = &mut project.modules[id as usize].state else {
        panic!()
    };
    let block = env
        .nodes
        .iter_mut()
        .find_map(|node| node.block_mut())
        .unwrap();
    let original_bindings = block.env.bindings.clone();
    // Deliberately alter only the current policy, keeping source, value and ranges
    // identical to real completed evidence. This must never be re-certified on disk.
    block.env.bindings.add_instance_scope(
        "Item",
        crate::acorn_type::Typeclass {
            module_id: id,
            name: "Marked".into(),
        },
        "Item.Marked".into(),
    );
    project.persist_completed(&completed);
    assert!(records().is_empty());
    let Module::Ok(env) = &mut project.modules[id as usize].state else {
        panic!()
    };
    env.nodes
        .iter_mut()
        .find_map(|node| node.block_mut())
        .unwrap()
        .env
        .bindings = original_bindings;
    project.persist_completed(&completed);
    assert_eq!(records().len(), 1);
    assert_eq!(std::fs::read(&files[0]).unwrap(), original);
}
