// Modified for Venticorn: verify match semantics through the real command-line tool.
use std::fs;
use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

static NEXT_DIRECTORY: AtomicUsize = AtomicUsize::new(0);
struct TestLibrary(PathBuf);
impl TestLibrary {
    fn new() -> Self {
        let id = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let path =
            std::env::temp_dir().join(format!("venticorn_match_{}_{}", std::process::id(), id));
        fs::create_dir(&path).unwrap();
        Self(path)
    }

    fn verify(&self, module: &str, source: &str, succeeds: bool) {
        fs::write(self.0.join(format!("{module}.ac")), source).unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_verify"))
            .env("VENTICORN_LIBRARY", &self.0)
            .args(["--module", module])
            .output()
            .expect("run match CLI fixture");
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
                stdout.contains("claim could not be verified"),
                "{stdout}\n{stderr}"
            );
        }
    }
}
impl Drop for TestLibrary {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

const DEFINITIONS: &str = r#"
inductive Item {
    wrap(Bool)
    empty
}
define payload(item: Item) -> Bool {
    match item {
        Item.wrap(bit) { bit }
        Item.empty { false }
    }
}
"#;

#[test]
fn selected_match_branch_preserves_true_and_false() {
    let library = TestLibrary::new();
    for bit in [false, true] {
        for negated in [false, true] {
            let not = if negated { "not " } else { "" };
            library.verify("main", &format!("{DEFINITIONS}\nlet input: Bool = {bit}\ntheorem claim {{ {not}payload(Item.wrap(input)) }}\n"), bit != negated);
        }
    }
}

#[test]
fn imported_match_definition_does_not_prove_a_false_branch() {
    let library = TestLibrary::new();
    fs::write(library.0.join("dependency.ac"), DEFINITIONS).unwrap();
    library.verify("main", "import dependency\nlet input: Bool = false\ntheorem claim { dependency.payload(dependency.Item.wrap(input)) }\n", false);
    library.verify("main", "import dependency\nlet input: Bool = true\ntheorem claim { dependency.payload(dependency.Item.wrap(input)) }\n", true);
}

#[test]
fn match_case_variables_remain_distinct_from_enclosing_arguments() {
    let library = TestLibrary::new();
    let definition = r#"
define same(item: Item, outside: Bool) -> Bool {
    match item {
        Item.wrap(inside) { inside = outside }
        Item.empty { outside }
    }
}
"#;
    library.verify(
        "main",
        &format!("{DEFINITIONS}\n{definition}\ntheorem claim {{ same(Item.wrap(true), true) }}\n"),
        true,
    );
    library.verify("main", &format!("{DEFINITIONS}\n{definition}\nlet off: Bool = false\ntheorem claim {{ same(Item.wrap(off), true) }}\n"), false);
}

#[test]
fn nested_match_and_conditional_results_keep_the_selected_value() {
    let library = TestLibrary::new();
    let definition = r#"
define nested(item: Item) -> Bool {
    match item {
        Item.wrap(first) {
            match Item.wrap(first) {
                Item.wrap(second) { if second { true } else { false } }
                Item.empty { false }
            }
        }
        Item.empty { false }
    }
}
"#;
    for bit in [false, true] {
        library.verify("main", &format!("{DEFINITIONS}\n{definition}\nlet input: Bool = {bit}\ntheorem claim {{ nested(Item.wrap(input)) }}\n"), bit);
    }
}

#[test]
fn match_in_both_equality_operands_and_function_arguments_is_supported() {
    let library = TestLibrary::new();
    let matched = "match Item.wrap(true) {\nItem.wrap(bit) { bit }\nItem.empty { absent }\n}";
    for claim in [
        format!("({matched}) = true"),
        format!("true = ({matched})"),
        format!("identity({matched})"),
    ] {
        library.verify("main", &format!("{DEFINITIONS}\nlet absent: Bool = false\ndefine identity(bit: Bool) -> Bool {{ bit }}\ntheorem claim {{ {claim} }}\n"), true);
    }
}

#[test]
fn quantified_match_preserves_an_enclosing_function_argument() {
    let library = TestLibrary::new();
    let definition = r#"
define project(item: Item, outside: Bool) -> Bool {
    match item {
        Item.wrap(inside) { outside }
        Item.empty { outside }
    }
}
theorem claim(item: Item) { project(item, true) }
"#;
    library.verify("main", &format!("{DEFINITIONS}\n{definition}"), true);
}

#[test]
fn quantified_data_valued_match_reconstructs_its_scrutinee() {
    let library = TestLibrary::new();
    let definition = r#"
define copy(item: Item) -> Item {
    match item {
        Item.wrap(bit) { Item.wrap(bit) }
        Item.empty { Item.empty }
    }
}
theorem claim(item: Item) { copy(item) = item }
"#;
    library.verify("main", &format!("{DEFINITIONS}\n{definition}"), true);
}
