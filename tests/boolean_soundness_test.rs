use std::fs;
use std::path::PathBuf;
use std::process::{Command, Output};
use std::sync::atomic::{AtomicUsize, Ordering};

static NEXT_DIRECTORY: AtomicUsize = AtomicUsize::new(0);

struct TestLibrary(PathBuf);

impl TestLibrary {
    fn new() -> Self {
        let id = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let path =
            std::env::temp_dir().join(format!("venticorn_boolean_{}_{}", std::process::id(), id,));
        fs::create_dir(&path).expect("create Boolean regression library");
        Self(path)
    }

    fn verify(&self, value: bool, imported: bool, negated: bool) -> Output {
        let definition = format!("let value: Bool = {}\n", value);
        let (prefix, reference) = if imported {
            fs::write(self.0.join("dependency.ac"), definition).unwrap();
            ("import dependency\n".to_string(), "dependency.value")
        } else {
            (definition, "value")
        };
        let claim = if negated {
            format!("not {}", reference)
        } else {
            reference.to_string()
        };
        fs::write(
            self.0.join("main.ac"),
            format!("{}theorem claim {{ {} }}\n", prefix, claim),
        )
        .unwrap();
        Command::new(env!("CARGO_BIN_EXE_verify"))
            .env("VENTICORN_LIBRARY", &self.0)
            .args(["--module", "main"])
            .output()
            .expect("verify Boolean theorem through the CLI")
    }
}

impl Drop for TestLibrary {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn assert_rejected(output: Output) {
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(1), "{stdout}\n{stderr}");
    assert!(stdout.contains("claim could not be verified"), "{stdout}");
    assert!(stdout.contains("0/1 OK"), "{stdout}");
}

#[test]
fn locally_defined_false_is_not_a_provable_fact() {
    assert_rejected(TestLibrary::new().verify(false, false, false));
}

#[test]
fn imported_false_is_not_a_provable_fact() {
    assert_rejected(TestLibrary::new().verify(false, true, false));
}

#[test]
fn negated_true_is_not_a_provable_fact() {
    for imported in [false, true] {
        assert_rejected(TestLibrary::new().verify(true, imported, true));
    }
}

#[test]
fn true_definitions_and_negated_false_definitions_are_provable() {
    for imported in [false, true] {
        for value in [false, true] {
            let output = TestLibrary::new().verify(value, imported, !value);
            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert!(output.status.success(), "{stdout}\n{stderr}");
            assert!(stdout.contains("1/1 OK"), "{stdout}");
        }
    }
}
