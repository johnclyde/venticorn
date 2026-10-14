// Modified for Venticorn: implication spelling preserves Boolean semantics and source ranges.
use tower_lsp::lsp_types::{Position, SemanticTokenType};
use venticorn::builder::BuildStatus;
use venticorn::environment::Environment;
use venticorn::expression::Expression;
use venticorn::project::Project;
use venticorn::token::{Token, TokenType};

#[test]
fn implies_has_keyword_metadata_without_consuming_identifier_prefixes() {
    let tokens = Token::scan("implies implies_value impliesx");
    assert_eq!(tokens[0].token_type, TokenType::Implies);
    assert_eq!(tokens[0].lsp_type(), Some(SemanticTokenType::KEYWORD));
    assert_eq!(tokens[1].token_type, TokenType::Identifier);
    assert_eq!(tokens[2].token_type, TokenType::Identifier);
    let claim = Expression::expect_value("not a implies b");
    let premise = claim.premise().unwrap();
    assert_eq!(premise.to_string(), "not a");
    assert_eq!(premise.range().start, Position::new(0, 0));
    assert_eq!(premise.range().end, Position::new(0, 5));
}

#[test]
fn implies_matches_arrow_precedence_associativity_and_codegen() {
    let mut env = Environment::new_test();
    env.add("let a: Bool = axiom\nlet b: Bool = axiom\nlet c: Bool = axiom");
    let project = Project::new_mock();
    for (input, canonical) in [
        ("a implies b", "a -> b"),
        ("not a implies b", "not a -> b"),
        ("a implies b and c", "a -> b and c"),
        ("a or b implies c", "a or b -> c"),
        ("a implies b implies c", "a -> b -> c"),
        ("a implies (b implies c)", "a -> (b -> c)"),
        ("a -> (b implies c)", "a -> (b -> c)"),
    ] {
        let value = env
            .bindings
            .evaluate_value(&project, &Expression::expect_value(input), None)
            .unwrap();
        let expected = env
            .bindings
            .evaluate_value(&project, &Expression::expect_value(canonical), None)
            .unwrap();
        assert_eq!(value, expected, "{input}");
        let generated = env.bindings.value_to_code(&value).unwrap();
        assert_eq!(generated, canonical, "{input}");
        let recovered = env
            .bindings
            .evaluate_value(&project, &Expression::expect_value(&generated), None)
            .unwrap();
        assert_eq!(recovered, value);
    }
}

#[test]
fn implication_truth_table_is_verified_without_proving_false_implications() {
    for a in [false, true] {
        for b in [false, true] {
            let mut project = Project::new_mock();
            project.mock(
                "/mock/main.ac",
                &format!(
                    "let a: Bool = {a}\nlet b: Bool = {b}\ntheorem {{ (a implies b) = {} }}",
                    !a || b
                ),
            );
            let report = project.sync_build_report();
            assert_eq!(
                report.status,
                BuildStatus::Good,
                "{a} implies {b}: {:?}",
                report.events
            );
        }
    }
    let mut invalid = Project::new_mock();
    invalid.mock("/mock/main.ac", "theorem { true implies false }");
    assert_eq!(invalid.sync_build_report().status, BuildStatus::Warning);
    assert_eq!(invalid.cached_build().num_modules(), 0);
    let mut project = Project::new_mock();
    project.mock(
        "/mock/main.ac",
        "let a: Bool = axiom\ntheorem { a implies a }\ntheorem { not a implies not a }",
    );
    assert_eq!(project.sync_build_report().status, BuildStatus::Good);
}

#[test]
fn implies_requires_boolean_operands_and_is_not_a_type_arrow() {
    for source in [
        "type Item: axiom\nlet a: Item = axiom\ntheorem { a implies a }",
        "type Item: axiom\nlet a: Item = axiom\ntheorem { true implies a }",
        "let f: Bool implies Bool = axiom",
        "let implies: Bool = true",
    ] {
        let mut project = Project::new_mock();
        project.mock("/mock/main.ac", source);
        assert_eq!(
            project.sync_build_report().status,
            BuildStatus::Error,
            "{source}"
        );
    }
}
