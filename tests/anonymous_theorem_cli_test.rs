// Modified for Venticorn: anonymous declarations retain their trust and proof boundaries in the CLI.
use std::fs;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

static NEXT_DIRECTORY: AtomicUsize = AtomicUsize::new(0);

fn verify(source: &str) -> (bool, String) {
    let id = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
    let root =
        std::env::temp_dir().join(format!("venticorn_anonymous_{}_{}", std::process::id(), id));
    fs::create_dir(&root).unwrap();
    fs::write(root.join("main.ac"), source).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_verify"))
        .env("VENTICORN_LIBRARY", &root)
        .args(["--module", "main"])
        .output()
        .unwrap();
    fs::remove_dir_all(root).unwrap();
    let text = format!(
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(!text.contains("panicked"), "{text}");
    assert!(matches!(output.status.code(), Some(0 | 1)), "{text}");
    (output.status.success(), text)
}

#[test]
fn anonymous_axioms_can_support_anonymous_theorem_proofs() {
    let (success, text) = verify("let b: Bool = axiom\naxiom { b }\ntheorem { b }\n");
    assert!(success, "{text}");
    assert!(text.contains("1/1 OK"), "{text}");
}

#[test]
fn anonymous_theorems_keep_parameter_and_premise_proof_obligations() {
    let (success, text) = verify(
        r#"
        theorem(value: Bool) { value or not value }
        theorem<T>(value: T) { value = value }
        theorem(value: Bool) { value -> value } by { value }
    "#,
    );
    assert!(success, "{text}");
}

#[test]
fn false_anonymous_theorems_are_not_skipped() {
    for source in [
        "theorem { false }",
        "theorem { true }\ntheorem { false }",
        "let b: Bool = axiom\naxiom { b }\ntheorem { not b }",
    ] {
        let (success, text) = verify(source);
        assert!(!success, "{text}");
        assert!(text.contains("could not be verified"), "{text}");
        assert!(!text.contains("not supported"), "{text}");
    }
}

#[test]
fn a_named_theorem_cannot_prove_itself_by_citation() {
    let (success, text) = verify("theorem circular { false } by { circular }");
    assert!(!success, "{text}");
    assert!(text.contains("could not be verified"), "{text}");
}

#[test]
fn anonymous_match_claims_use_source_labels_without_changing_proof_results() {
    let prefix = "inductive Choice {\n first\n second\n}\n";
    for (branch, expected) in [("true", true), ("false", false)] {
        let source = format!("{prefix}theorem {{ match Choice.first {{ Choice.first {{ {branch} }} Choice.second {{ false }} }} }}");
        let (success, text) = verify(&source);
        assert_eq!(success, expected, "{text}");
        if !success {
            assert!(
                text.contains("claim at line 5 could not be verified"),
                "{text}"
            );
        }
    }
}
