// Modified for Venticorn: exercise complete case proofs through the verifier.
use std::fs;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

static NEXT_DIRECTORY: AtomicUsize = AtomicUsize::new(0);

fn verify(source: &str, succeeds: bool) {
    let id = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!(
        "venticorn_case_proof_{}_{}",
        std::process::id(),
        id
    ));
    fs::create_dir(&path).unwrap();
    fs::write(path.join("main.ac"), source).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_verify"))
        .env("VENTICORN_LIBRARY", &path)
        .args(["--module", "main"])
        .output()
        .expect("run case proof verifier");
    fs::remove_dir_all(path).unwrap();
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.success(), succeeds, "{stdout}\n{stderr}");
    assert!(
        !stdout.contains("normalization error"),
        "{stdout}\n{stderr}"
    );
    assert!(!stderr.contains("panicked"), "{stdout}\n{stderr}");
    if !succeeds {
        assert_eq!(output.status.code(), Some(1), "{stdout}\n{stderr}");
        assert!(
            stdout.contains("could not be verified"),
            "{stdout}\n{stderr}"
        );
    }
}

const CHOICE: &str = "inductive Choice {\n first\n second\n}\n";

#[test]
fn exhaustive_case_conclusions_prove_their_disjunction() {
    verify(
        &format!(
            "{CHOICE}
        theorem claim(c: Choice) {{ c = Choice.first or c = Choice.second }} by {{
            match c {{
                Choice.first {{ c = Choice.first }}
                Choice.second {{ c = Choice.second }}
            }}
        }}"
        ),
        true,
    );
}

#[test]
fn a_failed_case_cannot_be_skipped_when_the_outer_goal_is_true() {
    for (first, second) in [("false", "true"), ("true", "false")] {
        verify(
            &format!(
                "{CHOICE}
            theorem claim(c: Choice) {{ true }} by {{
                match c {{
                    Choice.first {{ {first} }}
                    Choice.second {{ {second} }}
                }}
            }}"
            ),
            false,
        );
    }
}

#[test]
fn a_case_premise_cannot_escape_its_branch() {
    verify(
        &format!(
            "{CHOICE}
        theorem claim(c: Choice) {{ c = Choice.first }} by {{
            match c {{
                Choice.first {{ c = Choice.first }}
                Choice.second {{ c = Choice.second }}
            }}
        }}"
        ),
        false,
    );
}

#[test]
fn case_constructor_arguments_export_as_existential_witnesses() {
    verify(
        "inductive Item {\n wrap(Bool)\n empty\n}\n
        theorem claim(item: Item) {
            (exists(bit: Bool) { item = Item.wrap(bit) }) or item = Item.empty
        } by {
            match item {
                Item.wrap(bit) { item = Item.wrap(bit) }
                Item.empty { item = Item.empty }
            }
        }",
        true,
    );
}
