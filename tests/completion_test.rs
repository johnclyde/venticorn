// Modified for Venticorn: completion candidates must come from evaluated bindings.
use std::path::Path;
use tower_lsp::lsp_types::CompletionItemKind;
use venticorn::project::Project;

fn project() -> Project {
    let mut project = Project::new_mock();
    project.mock(
        "/mock/nat.ac",
        "inductive Nat {\n zero\n suc(Nat)\n}\nlet saved: Nat = axiom\n",
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
            .get_completions(Some(Path::new("/mock/main.ac")), 0, prefix)
            .unwrap();
        assert_eq!(items.len(), 1);
        assert_eq!(items[0].label, label);
        assert_eq!(items[0].kind, Some(kind));
    }
    assert!(project
        .get_completions(Some(Path::new("/mock/main.ac")), 0, "from unknown import N")
        .is_none());
    assert!(project
        .get_completions(Some(Path::new("/mock/main.ac")), 0, "from nat import zzz")
        .unwrap()
        .is_empty());
}

fn labels(project: &Project, path: &str, line: u32, prefix: &str) -> Vec<String> {
    project
        .get_completions(Some(Path::new(path)), line, prefix)
        .unwrap_or_default()
        .into_iter()
        .map(|item| item.label)
        .collect()
}

#[test]
fn imported_names_omit_aliases_theorems_and_keywords() {
    let mut project = project();
    project.mock("/mock/exports.ac", "from nat import Nat, saved\ntype Renamed: Nat\nlet secret: Bool = true\ntheorem shown { true }\n");
    project.expect_ok("exports");
    assert_eq!(
        labels(&project, "/mock/main.ac", 0, "from exports import s"),
        ["secret"]
    );
    assert!(labels(&project, "/mock/main.ac", 0, "from exports import N").is_empty());
    assert!(labels(&project, "/mock/main.ac", 0, "from exports import R").is_empty());
}

#[test]
fn local_completion_preserves_aliases_keywords_and_proof_scope() {
    let mut project = project();
    project.update_file(Path::new("/mock/main.ac").to_path_buf(), "from nat import Nat, saved\nlet foo: Nat = saved\nlet bar: Nat = saved\ntheorem goal<T>(bop: T) {\n bop = bop\n} by {\n // completion\n}\n", 1).unwrap();
    project.expect_ok("main");
    assert_eq!(
        labels(&project, "/mock/main.ac", 6, "b"),
        ["by", "bar", "bop"]
    );
    assert_eq!(
        labels(&project, "/mock/main.ac", 6, "fo"),
        ["forall", "foo"]
    );
    assert_eq!(labels(&project, "/mock/main.ac", 6, "sav"), ["saved"]);
    assert_eq!(labels(&project, "/mock/main.ac", 6, "T"), ["T"]);
    assert!(labels(&project, "/mock/main.ac", 8, "bop").is_empty());
    assert!(labels(&project, "/mock/main.ac", 8, "T").is_empty());
    assert!(labels(&project, "/mock/main.ac", 6, "foo ").is_empty());
}

#[test]
fn member_and_module_completions_use_canonical_types() {
    let mut project = project();
    project
        .update_file(
            Path::new("/mock/main.ac").to_path_buf(),
            "from nat import Nat, saved\ntype Renamed: Nat\nlet alias: Nat = saved\n",
            1,
        )
        .unwrap();
    project.expect_ok("main");
    for (prefix, expected) in [
        ("Nat.s", vec!["suc"]),
        ("Renamed.s", vec!["suc"]),
        ("alias.s", vec!["suc"]),
        ("nat.N", vec!["Nat"]),
        ("na", vec!["nat"]),
        ("(sav", vec!["saved"]),
        ("identity<Nat>(sav", vec!["saved"]),
        ("from nat import Nat, sav", vec!["saved"]),
        ("from nat import Nat,sav", vec!["saved"]),
        // A nullary constructor is a static value, not an applicable instance member.
        ("alias.z", vec![]),
    ] {
        assert_eq!(
            labels(&project, "/mock/main.ac", 2, prefix),
            expected,
            "{prefix}"
        );
    }
}

#[test]
fn completion_does_not_reuse_words_before_the_cursor_or_in_comments() {
    let project = project();
    for prefix in [
        "Nat;",
        "Nat ",
        "// Nat.s",
        "true // Nat.s",
        "Nat..s",
        ".Nat",
        "missing.N",
        "Bool.s",
        "import nat",
        "from nat N",
        "from ../nat import sav",
        "from nat import Nat.s",
        "from nat import (sav",
        "from nat import Nat,,sav",
        "Nat..",
        "missing.",
        ".",
    ] {
        assert!(
            labels(&project, "/mock/main.ac", 0, prefix).is_empty(),
            "{prefix}"
        );
    }
    assert!(project
        .get_completions(Some(Path::new("/missing/main.ac")), 0, "N")
        .is_none());
}

#[test]
fn completion_supports_external_modules_and_keeps_sibling_bindings_private() {
    let mut project = project();
    project.mock("/elsewhere/external.ac", "from nat import Nat\ntheorem first<T>(local: T) {\n local = local\n} by {\n // first\n}\ntheorem second(other: Nat) {\n other = other\n} by {\n // second\n}\n");
    let reference = project
        .module_ref_from_path(Path::new("/elsewhere/external.ac"))
        .unwrap();
    assert!(
        project.get_env_by_ref(&reference).is_some(),
        "external module did not load"
    );
    assert_eq!(
        labels(&project, "/elsewhere/external.ac", 4, "loc"),
        ["local"]
    );
    assert_eq!(labels(&project, "/elsewhere/external.ac", 4, "T"), ["T"]);
    assert!(labels(&project, "/elsewhere/external.ac", 9, "loc").is_empty());
    assert!(labels(&project, "/elsewhere/external.ac", 9, "T").is_empty());
    assert_eq!(
        labels(&project, "/elsewhere/external.ac", 9, "oth"),
        ["other"]
    );
}

#[test]
fn completion_respects_declaration_order_and_nested_block_boundaries() {
    let mut project = project();
    project.mock("/mock/other.ac", "let imported: Bool = axiom\n");
    let source = "from nat import Nat\n\
// before later declarations\n\
problem {\n\
 // before local declaration\n\
 let local: Bool = axiom\n\
 forall(bound: Bool) {\n\
  // inside forall\n\
  bound or not bound\n\
 } // closing forall\n\
 // after forall\n\
 match Nat.zero {\n\
  Nat.zero { true }\n\
  Nat.suc(pred) {\n\
   // inside case\n\
   true\n\
  } // closing case\n\
 }\n\
 // after match\n\
 true\n\
} // closing problem\n\
// after problem\n\
type Future: axiom\n\
let future: Bool = axiom\n\
from other import imported\n";
    project
        .update_file(Path::new("/mock/main.ac").to_path_buf(), source, 1)
        .unwrap();
    project.expect_ok("main");
    let line = |marker: &str| {
        source
            .lines()
            .position(|line| line.contains(marker))
            .unwrap() as u32
    };
    for prefix in ["Fut", "fut", "oth", "imp"] {
        let actual = labels(&project, "/mock/main.ac", line("before later"), prefix);
        assert!(
            actual.is_empty() || actual == ["import"],
            "{prefix}: {actual:?}"
        );
    }
    assert!(labels(&project, "/mock/main.ac", line("before local"), "loc").is_empty());
    assert_eq!(
        labels(&project, "/mock/main.ac", line("inside forall"), "loc"),
        ["local"]
    );
    assert_eq!(
        labels(&project, "/mock/main.ac", line("inside forall"), "bou"),
        ["bound"]
    );
    for marker in [
        "closing forall",
        "after forall",
        "after match",
        "closing problem",
        "after problem",
    ] {
        assert!(
            labels(&project, "/mock/main.ac", line(marker), "bou").is_empty(),
            "{marker}"
        );
    }
    assert_eq!(
        labels(&project, "/mock/main.ac", line("inside case"), "pre"),
        ["pred"]
    );
    for marker in [
        "closing case",
        "after match",
        "closing problem",
        "after problem",
    ] {
        assert!(
            labels(&project, "/mock/main.ac", line(marker), "pre").is_empty(),
            "{marker}"
        );
    }
    assert!(labels(&project, "/mock/main.ac", line("closing problem"), "loc").is_empty());
}

#[test]
fn completion_hides_members_until_their_declarations() {
    let mut project = Project::new_mock();
    let source = "inductive Local {\n zero\n}\nlet value: Local = axiom\n// before member\nclass Local {\n define later(self) -> Local { self }\n}\n// after member\n";
    project.mock("/mock/main.ac", source);
    project.expect_ok("main");
    for prefix in ["Local.la", "value.la"] {
        assert!(labels(&project, "/mock/main.ac", 4, prefix).is_empty());
        assert_eq!(labels(&project, "/mock/main.ac", 8, prefix), ["later"]);
    }
}

#[test]
fn local_aliases_are_visible_only_after_their_declaration() {
    let mut project = Project::new_mock();
    project.mock(
        "/mock/main.ac",
        "// before\nlet earlier: Bool = axiom\nlet later: Bool = earlier\n// after\n",
    );
    project.expect_ok("main");
    assert!(labels(&project, "/mock/main.ac", 0, "lat").is_empty());
    assert_eq!(labels(&project, "/mock/main.ac", 3, "lat"), ["later"]);
}

#[test]
fn member_aliases_and_alias_namespaces_preserve_declaration_visibility() {
    let mut project = Project::new_mock();
    let source = "inductive Local {\n zero\n}\nlet value: Local = axiom\nclass Local {\n define base(self) -> Local { self }\n}\n// before aliases\nlet alias: Local = value\nclass Local {\n let later: Local -> Local = Local.base\n}\n// after aliases\n";
    project.mock("/mock/main.ac", source);
    project.expect_ok("main");
    for prefix in ["Local.la", "value.la", "alias.ba", "alias.la"] {
        assert!(
            labels(&project, "/mock/main.ac", 7, prefix).is_empty(),
            "{prefix}"
        );
        let expected = if prefix.ends_with("ba") {
            "base"
        } else {
            "later"
        };
        assert_eq!(
            labels(&project, "/mock/main.ac", 12, prefix),
            [expected],
            "{prefix}"
        );
    }
}

#[test]
fn after_dot_completion_lists_only_resolved_exports_or_applicable_members() {
    let mut project = project();
    project
        .update_file(
            Path::new("/mock/main.ac").to_path_buf(),
            "from nat import Nat, saved\ntype Renamed: Nat\nlet alias: Nat = saved\n",
            1,
        )
        .unwrap();
    project.expect_ok("main");
    for (prefix, expected) in [
        ("nat.", vec!["Nat", "saved"]),
        ("Nat.", vec!["induction", "suc", "zero"]),
        ("Renamed.", vec!["induction", "suc", "zero"]),
        ("alias.", vec!["suc"]),
    ] {
        let mut actual = labels(&project, "/mock/main.ac", 2, prefix);
        actual.sort();
        assert_eq!(actual, expected, "{prefix}");
    }
    assert!(labels(&project, "/mock/main.ac", 2, "").is_empty());
}

#[test]
fn untitled_completion_only_uses_loaded_imports() {
    let project = project();
    let items = project
        .get_completions(None, 0, "from nat import N")
        .unwrap();
    assert_eq!(
        items
            .iter()
            .map(|item| item.label.as_str())
            .collect::<Vec<_>>(),
        ["Nat"]
    );
    for prefix in ["saved", "Nat.", "from missing import N"] {
        assert!(project.get_completions(None, 0, prefix).is_none());
    }
}
