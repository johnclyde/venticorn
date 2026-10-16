use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};
use venticorn::builder::BuildStatus;
use venticorn::module::ModuleRef;
use venticorn::persistent_cache::CachePolicy;
use venticorn::project::Project;

const FACTS: &str = "let seed: Bool = axiom\nlet first: Bool = axiom\nlet second: Bool = axiom\naxiom start { seed }\naxiom left { seed implies first }\naxiom right { seed implies second }\n";
static NEXT: AtomicU64 = AtomicU64::new(0);
struct Library(PathBuf);
impl Library {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "venticorn_advice_{}_{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        Self(path.canonicalize().unwrap())
    }
    fn write(&self, name: &str, source: &str) {
        fs::write(self.0.join(name), source).unwrap();
    }
    fn main(&self, claim: &str) {
        self.write("main.ac", &format!("{FACTS}theorem goal {{ {claim} }}"));
    }
    fn project(&self, policy: CachePolicy) -> Project {
        let mut project = Project::from_library_root(self.0.clone()).unwrap();
        project.set_cache_policy(policy);
        project.add_all_targets().unwrap();
        project
    }
    fn records(&self) -> Vec<(PathBuf, Vec<u8>)> {
        let mut records = fs::read_dir(self.0.join(".venticorn-cache"))
            .into_iter()
            .flatten()
            .map(|f| {
                let p = f.unwrap().path();
                let b = fs::read(&p).unwrap();
                (p, b)
            })
            .collect::<Vec<_>>();
        records.sort();
        records
    }
    fn child(&self, policy: &str, dataset: bool, target: Option<&Path>) -> serde_json::Value {
        let mut cmd = Command::new(std::env::current_exe().unwrap());
        cmd.args(["--exact", "persistent_advice_child", "--nocapture"])
            .env("VENTICORN_ADVICE_TEST_ROOT", &self.0)
            .env("VENTICORN_ADVICE_TEST_POLICY", policy)
            .env(
                "VENTICORN_ADVICE_TEST_DATASET",
                if dataset { "1" } else { "0" },
            );
        if let Some(target) = target {
            cmd.env("VENTICORN_ADVICE_TEST_TARGET", target);
        }
        let output = cmd.output().unwrap();
        assert!(
            output.status.success(),
            "{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        #[cfg(feature = "onnx")]
        for stream in [&output.stdout, &output.stderr] {
            assert!(
                !String::from_utf8_lossy(stream).contains("Could not load the proof-scoring model"),
                "native child silently fell back to the heuristic scorer"
            );
        }
        let output = String::from_utf8(output.stdout).unwrap();
        println!("{output}");
        let line = output
            .lines()
            .find_map(|line| line.strip_prefix("ADVICE_RESULT:"))
            .unwrap();
        serde_json::from_str(line).unwrap()
    }
}
impl Drop for Library {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn persistent_advice_child() {
    let Some(root) = std::env::var_os("VENTICORN_ADVICE_TEST_ROOT") else {
        return;
    };
    let mut project = Project::from_library_root(PathBuf::from(root)).unwrap();
    project.set_cache_policy(
        match std::env::var("VENTICORN_ADVICE_TEST_POLICY")
            .unwrap()
            .as_str()
        {
            "disabled" => CachePolicy::Disabled,
            "read" => CachePolicy::ReadOnly,
            _ => CachePolicy::ReadWrite,
        },
    );
    if let Some(target) = std::env::var_os("VENTICORN_ADVICE_TEST_TARGET") {
        project.add_target_by_path(Path::new(&target)).unwrap();
    } else {
        project.add_all_targets().unwrap();
    }
    let mut builder = project.builder(|_| {});
    if std::env::var("VENTICORN_ADVICE_TEST_DATASET").unwrap() == "1" {
        builder.create_dataset();
    }
    project.build(&mut builder);
    println!(
        "ADVICE_RESULT:{}",
        serde_json::json!({"status":format!("{:?}",builder.status), "searches":builder.searches_total,"full":builder.full_searches(),"hinted":builder.hinted_searches,"accepted":builder.hinted_successes,"fallbacks":builder.hint_fallbacks,"fresh":builder.num_success,"cached":builder.num_cached,"goals":builder.goals_done})
    );
}
fn good(result: &serde_json::Value, searches: i32, hinted: i32, cached: i32) {
    assert_eq!(result["status"], "Good");
    assert_eq!(result["searches"], searches);
    assert_eq!(result["hinted"], hinted);
    assert_eq!(result["cached"], cached);
    assert_eq!(result["goals"], 1);
}

#[test]
fn fresh_process_advice_survives_reuse_and_rechecks_changed_claims() {
    let library = Library::new();
    library.main("first");
    good(&library.child("write", false, None), 1, 0, 0);
    let original = library.records();
    assert!(
        serde_json::from_slice::<serde_json::Value>(&original[0].1).unwrap()["hints"]["goal"]
            .is_array()
    );
    good(&library.child("write", false, None), 0, 0, 1);
    assert_eq!(library.records(), original);
    library.main("first and first");
    let hit = library.child("write", false, None);
    good(&hit, 1, 1, 0);
    assert_eq!(hit["accepted"], 1);
    library.main("second");
    let retry = library.child("write", false, None);
    good(&retry, 2, 1, 0);
    assert_eq!(retry["fallbacks"], 1);
    let before_false = library.records();
    library.main("not second");
    let rejected = library.child("write", false, None);
    assert_eq!(rejected["status"], "Warning");
    assert_eq!(rejected["fresh"], 0);
    assert_eq!(rejected["cached"], 0);
    assert_eq!(library.records(), before_false);
}

#[test]
fn stale_zero_goal_dependency_advice_never_becomes_verified_evidence() {
    let library = Library::new();
    library.write("leaf.ac", FACTS);
    library.write("main.ac", "import leaf\ntheorem goal { leaf.first }");
    good(&library.child("write", false, None), 1, 0, 0);
    library.write("leaf.ac", &format!("// changed dependency\n{FACTS}"));
    let project = library.project(CachePolicy::ReadOnly);
    assert!(project
        .cached_build()
        .get(&ModuleRef::Name("leaf".into()))
        .is_none());
    assert!(project
        .cached_build()
        .get(&ModuleRef::Name("main".into()))
        .is_none());
    let result = library.child("read", false, None);
    good(&result, 1, 1, 0);
    assert_eq!(result["accepted"], 1);
}

#[test]
fn malformed_or_unknown_advice_cannot_load_modules_or_skip_search() {
    let library = Library::new();
    library.main("first");
    good(&library.child("write", false, None), 1, 0, 0);
    let (path, original) = library.records().pop().unwrap();
    library.main("first and first");
    // This file must never be loaded merely because a stored hint names it.
    library.write("foreign.ac", "this is not a valid declaration");
    let main = library.0.join("main.ac");
    for change in 0..8 {
        let mut value: serde_json::Value = serde_json::from_slice(&original).unwrap();
        match change {
            0 => value["schema"] = 99.into(),
            1 => value["checker"] = "foreign checker".into(),
            2 => value["root"][0] = (value["root"][0].as_u64().unwrap() ^ 1).into(),
            3 => value["module"][0] = (value["module"][0].as_u64().unwrap() ^ 1).into(),
            4 => value["hints"]["goal"][0]["module"] = serde_json::json!({"Name":"foreign"}),
            5 => {
                value["hints"]["goal"][0]["module"] =
                    serde_json::json!({"File":library.0.join("foreign.ac")})
            }
            6 => value["hints"]["goal"][0]["names"] = serde_json::json!(["absent"]),
            _ => value["hints"] = serde_json::json!({"malformed": false}),
        }
        fs::write(&path, serde_json::to_vec(&value).unwrap()).unwrap();
        good(&library.child("read", false, Some(&main)), 1, 0, 0);
    }
    for bytes in [b"{broken".to_vec(), vec![b'x'; 16 * 1024 + 1]] {
        fs::write(&path, bytes).unwrap();
        good(&library.child("read", false, Some(&main)), 1, 0, 0);
    }
}

#[test]
fn dataset_disabled_and_unsaved_builds_bypass_persistent_advice() {
    let library = Library::new();
    library.main("first");
    good(&library.child("write", false, None), 1, 0, 0);
    let records = library.records();
    library.main("first and first");
    good(&library.child("write", true, None), 1, 0, 0);
    assert_eq!(library.records(), records);
    good(&library.child("disabled", false, None), 1, 0, 0);
    assert_eq!(library.records(), records);
    let mut project = library.project(CachePolicy::ReadWrite);
    project
        .update_file(
            library.0.join("main.ac"),
            &format!("{FACTS}theorem goal {{ first and first and first }}"),
            1,
        )
        .unwrap();
    let mut builder = project.builder(|_| {});
    project.build(&mut builder);
    assert_eq!(builder.status, BuildStatus::Good);
    assert_eq!(
        (
            builder.searches_total,
            builder.hinted_searches,
            builder.num_cached
        ),
        (1, 0, 0)
    );
    assert_eq!(library.records(), records);
}

#[cfg(unix)]
#[test]
fn canonical_file_hints_work_through_current_aliases_without_resolving_payload_paths() {
    let library = Library::new();
    let outside = Library::new();
    let file = outside.0.join("standalone.ac");
    let alias = outside.0.join("alias.ac");
    fs::write(&file, format!("{FACTS}theorem goal {{ first }}")).unwrap();
    std::os::unix::fs::symlink(&file, &alias).unwrap();
    good(&library.child("write", false, Some(&file)), 1, 0, 0);
    let (record, bytes) = library.records().pop().unwrap();
    let value: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    assert_eq!(
        value["hints"]["goal"][0]["module"]["File"],
        file.to_str().unwrap()
    );
    fs::write(&file, format!("{FACTS}theorem goal {{ first and first }}")).unwrap();
    good(&library.child("read", false, Some(&alias)), 1, 1, 0);
    let mut changed = value;
    changed["hints"]["goal"][0]["module"]["File"] = alias.to_str().unwrap().into();
    fs::write(&record, serde_json::to_vec(&changed).unwrap()).unwrap();
    // An arbitrary payload spelling is not canonicalized or opened by the reader.
    good(&library.child("read", false, Some(&file)), 1, 0, 0);
}

#[cfg(unix)]
#[test]
fn unsaved_alias_excludes_advice_for_transitive_importers() {
    let library = Library::new();
    let aliases = Library::new();
    library.write("leaf.ac", FACTS);
    library.write("main.ac", "import leaf\ntheorem goal { leaf.first }");
    good(&library.child("write", false, None), 1, 0, 0);
    let records = library.records();
    let alias = aliases.0.join("leaf.ac");
    std::os::unix::fs::symlink(library.0.join("leaf.ac"), &alias).unwrap();
    let mut project = library.project(CachePolicy::ReadWrite);
    project
        .update_file(alias, &format!("// unsaved alias\n{FACTS}"), 1)
        .unwrap();
    let mut builder = project.builder(|_| {});
    project.build(&mut builder);
    assert_eq!(builder.status, BuildStatus::Good);
    assert_eq!(
        (
            builder.searches_total,
            builder.hinted_searches,
            builder.num_cached
        ),
        (1, 0, 0)
    );
    assert_eq!(library.records(), records);
}
