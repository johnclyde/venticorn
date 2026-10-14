// Modified for Venticorn: completion candidates must come from evaluated bindings.
use std::path::Path;
use tower_lsp::lsp_types::CompletionItemKind;
use venticorn::project::Project;

fn project() -> Project {
    let mut project = Project::new_mock();
    project.mock(
        "/mock/nat.ac",
        "inductive Nat {\n zero\n suc(Nat)\n}\nlet saved: Nat = Nat.zero\n",
    );
    project.mock("/mock/main.ac", "from nat import Nat\n");
    project.expect_ok("main");
    project
}

#[test]
fn import_completion_uses_loaded_types_and_constants() {
    let project = project();
    for (prefix, label, kind) in [
        ("from nat import N", "Nat", CompletionItemKind::CLASS),
        ("from nat import sav", "saved", CompletionItemKind::CONSTANT),
    ] {
        let items = project
            .get_completions(Path::new("/mock/main.ac"), 0, prefix)
            .unwrap();
        assert_eq!(items.len(), 1);
        assert_eq!(items[0].label, label);
        assert_eq!(items[0].kind, Some(kind));
    }
    assert!(project
        .get_completions(Path::new("/mock/main.ac"), 0, "from unknown import N")
        .is_none());
    assert!(project
        .get_completions(Path::new("/mock/main.ac"), 0, "from nat import zzz")
        .unwrap()
        .is_empty());
}
