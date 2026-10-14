// Modified for Venticorn: generated types must keep their canonical module identity.
use venticorn::expression::Expression;
use venticorn::project::Project;

fn roundtrip(project: &mut Project, module: &str, input: &str, expected: &str) {
    let id = project.load_module_by_name(module).unwrap();
    if let venticorn::module::Module::Error(error) = project.get_module_by_id(id) {
        panic!("{module}: {error}");
    }
    let env = project.get_env_by_id(id).unwrap();
    let value = env
        .bindings
        .evaluate_value(project, &Expression::expect_value(input), None)
        .unwrap();
    let code = env.bindings.value_to_code(&value).unwrap();
    assert_eq!(code, expected);
    let recovered = env
        .bindings
        .evaluate_value(project, &Expression::expect_value(&code), None)
        .unwrap();
    assert_eq!(value, recovered);
}
#[test]
fn imported_types_generate_qualified_names_and_prefer_local_aliases() {
    let mut project = Project::new_mock();
    project.mock("/mock/boolbox.ac", "structure BoolBox {\n item: Bool\n}");
    project.mock("/mock/qualified.ac", "import boolbox");
    roundtrip(
        &mut project,
        "qualified",
        "forall(b: boolbox.BoolBox) { true }",
        "forall(x0: boolbox.BoolBox) { true }",
    );
    roundtrip(
        &mut project,
        "qualified",
        "forall(f: boolbox.BoolBox -> Bool) { true }",
        "forall(x0: boolbox.BoolBox -> Bool) { true }",
    );
    project.mock(
        "/mock/aliased.ac",
        "import boolbox\ntype Box: boolbox.BoolBox",
    );
    roundtrip(
        &mut project,
        "aliased",
        "forall(b: boolbox.BoolBox) { true }",
        "forall(x0: Box) { true }",
    );
}
#[test]
fn transitive_types_without_an_accessible_name_fail_cleanly() {
    let mut project = Project::new_mock();
    project.mock(
        "/mock/hidden.ac",
        "type Secret: axiom\nlet value: Secret = axiom",
    );
    project.mock(
        "/mock/bridge.ac",
        "import hidden\nlet value: hidden.Secret = hidden.value",
    );
    project.mock("/mock/main.ac", "import bridge");
    let main = project.load_module_by_name("main").unwrap();
    let hidden = project.load_module_by_name("hidden").unwrap();
    let hidden_env = project.get_env_by_id(hidden).unwrap();
    let value = hidden_env
        .bindings
        .evaluate_value(
            &project,
            &Expression::expect_value("forall(x: Secret) { true }"),
            None,
        )
        .unwrap();
    let error = project
        .get_env_by_id(main)
        .unwrap()
        .bindings
        .value_to_code(&value)
        .unwrap_err();
    assert_eq!(error.error_type(), "UnnamedType");
}

#[test]
fn unavailable_import_errors_name_the_constant_that_code_generation_needs() {
    let mut project = Project::new_mock();
    project.mock("/mock/hidden.ac", "let secret: Bool = axiom");
    project.mock("/mock/main.ac", "theorem ready { true }");
    let hidden = project.expect_ok("hidden");
    let main = project.expect_ok("main");
    let secret = project
        .get_env_by_id(hidden)
        .unwrap()
        .bindings
        .get_constant_value("secret")
        .unwrap();
    let error = project
        .get_env_by_id(main)
        .unwrap()
        .bindings
        .value_to_code(&secret)
        .unwrap_err();
    assert_eq!(error.error_type(), "UnimportedModule");
    assert_eq!(
        error.to_string(),
        "could not generate code using 'secret' because it is not imported"
    );
}
