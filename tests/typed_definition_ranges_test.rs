use venticorn::project::Project;

#[test]
fn completion_ranges_retain_typed_members_aliases_and_import_cutoffs() {
    let mut project = Project::new_mock();
    project.mock(
        "/mock/library.ac",
        "type Export: axiom
let value: Bool = true",
    );
    let source = "typeclass T: Marked {
 flag: Bool
}
inductive State {
 clean
}
instance State: Marked {
 let flag: Bool = true
}
class State {
 let later: Bool = true
}
let earlier: Bool = true
let alias: Bool = earlier
from library import Export, value
";
    project.mock("/mock/main.ac", source);
    let module = project.expect_ok("main");
    let env = project.get_env_by_id(module).unwrap();
    let line = |needle: &str| {
        source
            .lines()
            .position(|text| text.contains(needle))
            .unwrap() as u32
    };
    let labels = |at, prefix| {
        env.get_completions(&project, at, prefix)
            .unwrap_or_default()
            .into_iter()
            .map(|item| item.label)
            .collect::<Vec<_>>()
    };
    for (declaration, prefix, expected) in [
        ("let flag", "State.Marked.f", "flag"),
        ("let later", "State.l", "later"),
        ("let alias", "ali", "alias"),
        ("from library", "Exp", "Export"),
        ("from library", "library.v", "value"),
    ] {
        let at = line(declaration);
        assert!(
            labels(at - 1, prefix).is_empty(),
            "{prefix} leaked before its declaration"
        );
        assert_eq!(labels(at, prefix), [expected], "{prefix}");
    }
}
