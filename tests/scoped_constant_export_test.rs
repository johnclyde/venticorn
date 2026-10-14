// Modified for Venticorn: reject unsupported polymorphic exports before admitting a claim.
use venticorn::environment::Environment;
use venticorn::project::Project;
use venticorn::statement::Statement;

#[test]
fn scoped_generic_export_reports_a_source_error_without_partial_admission() {
    for last_claim in [
        "identity(flag) = flag",
        "identity(flag) = flag and identity(Item.only) = Item.only",
    ] {
        let mut env = Environment::new_test();
        env.add("inductive Item {\n only\n}");
        let nodes_before = env.nodes.len();
        let last_line_before = env.last_line();
        let source = format!("forall(flag: Bool) {{\n define identity<T>(value: T) -> T {{ value }}\n {last_claim}\n}}");
        let statement = Statement::parse_str(&source).unwrap();
        let error = env
            .add_statement(&mut Project::new_mock(), &statement)
            .unwrap_err();
        assert_eq!(
            error.message(),
            "cannot export scoped generic constant 'identity' from this block"
        );
        assert_eq!(error.range().start.line, 3);
        assert_eq!(env.nodes.len(), nodes_before);
        assert_eq!(env.last_line(), last_line_before);
        assert!(!env.bindings.has_identifier("identity"));
        assert!(!env.bindings.has_identifier("flag"));
        assert!(!env.bindings.has_type_name("T"));
        env.add("forall(flag: Bool) {\n let local: Bool = flag\n forall(other: Bool) { local = flag or other }\n}");
        env.nodes.last().unwrap().claim.value.validate().unwrap();
    }
}

#[test]
fn ordinary_local_functions_export_with_their_concrete_type() {
    let mut env = Environment::new_test();
    env.add("forall(flag: Bool) {\n define identity(value: Bool) -> Bool { value }\n forall(other: Bool) { identity(flag) = flag or other }\n}");
    env.nodes.last().unwrap().claim.value.validate().unwrap();
}
