// Modified for Venticorn: reject inconsistent declarations through the actual verifier.
use std::fs;
use std::process::Command;

#[test]
fn contradictory_declarations_fail_before_proof_search() {
    let root = std::env::temp_dir().join(format!("venticorn_recursion_{}", std::process::id()));
    fs::create_dir_all(&root).unwrap();
    for (name, source, diagnostic) in [
        (
            "self_loop",
            "define loop(b: Bool) -> Bool { not loop(b) }\ntheorem contradiction { false }\n",
            "termination checker",
        ),
        (
            "negative_inductive",
            r#"
            inductive Bad {
                node(Bad -> Bool)
            }
            define eval(b: Bad) -> Bool {
                match b { Bad.node(f) { f(b) } }
            }
            let liar: Bad = Bad.node(function(x: Bad) { not eval(x) })
            theorem contradiction { false }
        "#,
            "recursive constructor fields must use the inductive type directly",
        ),
    ] {
        fs::write(root.join(format!("{name}.ac")), source).unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_verify"))
            .env("VENTICORN_LIBRARY", &root)
            .args(["--module", name])
            .output()
            .unwrap();
        let text = format!(
            "{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(output.status.code(), Some(1), "{text}");
        assert!(text.contains(diagnostic), "{text}");
        assert!(!text.contains("panicked"), "{text}");
    }
    fs::remove_dir_all(root).unwrap();
}
