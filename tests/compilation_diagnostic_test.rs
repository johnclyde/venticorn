// Modified for Venticorn: compiler ranges use the editor protocol's UTF-16 units.
use tower_lsp::lsp_types::{Position, Range};
use venticorn::compilation::Error;
use venticorn::project::Project;
use venticorn::token::Token;

fn assert_error_span(code: &str, text: &str) {
    assert_diagnostic(code, text, "unknown identifier");
}

fn assert_diagnostic(code: &str, text: &str, message: &str) -> String {
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", code);
    let errors = project.errors();
    assert_eq!(errors.len(), 1);
    let error = errors[0].1;
    assert!(error.message().contains(message), "{error}");
    let start = code.find(text).unwrap();
    let position = |end: usize| {
        let prefix = &code[..end];
        Position::new(
            prefix.bytes().filter(|byte| *byte == b'\n').count() as u32,
            prefix.rsplit('\n').next().unwrap().encode_utf16().count() as u32,
        )
    };
    assert_eq!(
        error.range(),
        Range::new(position(start), position(start + text.len()))
    );
    error.message().to_string()
}

#[test]
fn diagnostic_columns_count_utf16_before_and_within_the_span() {
    assert_error_span("let x𐐀é: Bool = missing", "missing");
    assert_error_span("let x: Bool = y𐐀é", "y𐐀é");
}

#[test]
fn token_storage_stays_in_bytes_while_positions_use_utf16() {
    let tokens = Token::scan("x𐐀é other");
    assert_eq!(tokens[0].text(), "x𐐀é");
    assert_eq!(tokens[0].len, 7);
    assert_eq!(tokens[0].end_pos(), Position::new(0, 4));
    assert_eq!(tokens[1].text(), "other");
    assert_eq!(tokens[1].start, 8);
    assert_eq!(
        tokens[1].range(),
        Range::new(Position::new(0, 5), Position::new(0, 10))
    );
}

#[test]
fn empty_and_end_of_line_errors_keep_a_visible_caret() {
    let empty = Token::empty();
    let error = Error::new(&empty, &empty, "missing expression");
    assert_eq!(
        error.range(),
        Range::new(Position::new(0, 0), Position::new(0, 0))
    );
    assert!(error.to_string().ends_with("\n^\n"));
    let tokens = Token::scan("x𐐀é");
    let last = tokens.last().unwrap();
    let error = Error::new(last, last, "missing expression");
    assert_eq!(
        error.range(),
        Range::new(Position::new(0, 4), Position::new(0, 4))
    );
    assert!(error.to_string().ends_with("   ^\n"));
}

#[test]
fn secondary_import_errors_cover_the_import_without_duplicate_root_diagnostics() {
    use venticorn::builder::BuildStatus;
    use venticorn::module::ModuleRef;
    let mut project = Project::new_mock();
    project.mock("/mock/broken.ac", "theorem broken { missing }");
    project.mock("/mock/main.ac", "import broken");
    let errors = project.errors();
    assert_eq!(errors.len(), 2);
    let secondary = errors.iter().find(|(_, error)| error.secondary).unwrap().1;
    assert_eq!(
        secondary.range(),
        Range::new(Position::new(0, 0), Position::new(0, 13))
    );
    let (status, events) = project.sync_build();
    assert_eq!(status, BuildStatus::Error);
    let located: Vec<_> = events
        .iter()
        .filter(|event| event.diagnostic.is_some())
        .collect();
    assert_eq!(located.len(), 1);
    assert_eq!(located[0].module, ModuleRef::Name("broken".to_string()));
    assert!(events.iter().all(|event| event.verified.is_none()));
}

#[test]
fn error_ranges_preserve_endpoints_across_lines() {
    let tokens = Token::scan("start\n  end𐐀");
    let last = tokens.iter().find(|token| token.text() == "end𐐀").unwrap();
    let error = Error::secondary(&tokens[0], last, "unavailable dependency");
    assert_eq!(
        error.range(),
        Range::new(Position::new(0, 0), Position::new(1, 7))
    );
}

#[test]
fn numeric_class_type_errors_cover_the_complete_type_expression() {
    assert_diagnostic(
        "type Number: axiom\nclass Number {\n let 0: (Bool -> Bool) = axiom\n}",
        "(Bool -> Bool)",
        "numeric class variables must be the class type",
    );
}

#[test]
fn grouped_list_errors_cover_the_entire_expression() {
    use venticorn::expression::{Expression, Terminator};
    use venticorn::token::{TokenIter, TokenType};
    let mut tokens = TokenIter::new(Token::scan("left and right"));
    let (expression, _) =
        Expression::parse_value(&mut tokens, Terminator::Is(TokenType::NewLine)).unwrap();
    let error = expression.flatten_list(false).unwrap_err();
    assert!(error.message().contains("expected a grouped list"));
    assert_eq!(
        error.range(),
        Range::new(Position::new(0, 0), Position::new(0, 14))
    );
}

#[test]
fn misplaced_binders_are_highlighted_as_complete_parser_expressions() {
    assert_diagnostic(
        "theorem bad { true forall(x: Bool) { x } }",
        "forall(x: Bool) { x }",
        "expected a grouping",
    );
}

#[test]
fn pattern_arity_errors_cover_the_argument_group() {
    assert_diagnostic(
        "inductive Foo {\n bar(Bool)\n }\ndefine f(v: Foo) -> Bool { match v { Foo.bar(x, y) { x } } }",
        "(x, y)",
        "expected 1 arguments but got 2",
    );
}

#[test]
fn invalid_member_names_cover_the_entire_right_hand_expression() {
    assert_diagnostic(
        "type Thing: axiom\nlet x: Thing = axiom\nlet bad: Bool = x.(true and false)",
        "(true and false)",
        "expected an identifier after a dot",
    );
}

#[test]
fn function_argument_errors_cover_complete_argument_expressions() {
    for argument in [
        "true and false",
        "true or false",
        "true implies false",
        "true -> false",
        "true = false",
        "true != false",
        "not true",
    ] {
        assert_diagnostic(
            &format!("type Thing: axiom\ndefine accept(x: Thing) -> Bool {{ axiom }}\nlet bad: Bool = accept({argument})"),
            argument,
            "expected type Thing",
        );
    }
    assert_diagnostic(
        "let bad: Bool = (true and false)(true)",
        "(true and false)",
        "expected a function",
    );
}

#[test]
fn conflicting_type_definitions_cover_the_full_statement() {
    assert_diagnostic(
        "type Thing: axiom\ntype Thing: Bool",
        "type Thing: Bool",
        "type name 'Thing' already defined",
    );
}

#[test]
fn invalid_numeral_defaults_cover_the_complete_type_expression() {
    assert_diagnostic(
        "numerals (Bool -> Bool)",
        "(Bool -> Bool)",
        "numerals type must be a data type",
    );
}

#[test]
fn import_resolution_errors_cover_the_whole_statement() {
    assert_diagnostic(
        "import missing.module",
        "import missing.module",
        "import error",
    );
}

#[test]
fn constructor_identity_errors_cover_the_complete_pattern() {
    assert_diagnostic(
        "inductive Foo {\n bar\n }\ninductive Other {\n wrong(Bool)\n }\ndefine f(v: Foo) -> Bool { match v { Other.wrong(b) { b } } }",
        "Other.wrong(b)",
        "expected type Foo",
    );
}

#[test]
fn application_result_type_errors_cover_the_function_expression() {
    assert_diagnostic(
        "type Thing: axiom\nlet f: Bool -> Bool = axiom\nlet bad: Thing = (f)(true)",
        "(f)",
        "expected type Thing",
    );
}

#[test]
fn nested_and_applied_axioms_are_errors_without_retained_bindings() {
    use venticorn::environment::Environment;
    use venticorn::statement::Statement;
    for source in [
        "let bad: Bool = axiom(true)",
        "let bad: Bool = not axiom",
        "let bad: Bool = (axiom)",
        "define bad(x: Bool) -> Bool { axiom(true) }",
        "define bad(x: Bool) -> Bool { not axiom }",
        "define bad<T>(x: T) -> Bool { axiom(true) }",
    ] {
        let mut env = Environment::new_test();
        let statement = Statement::parse_str(source).unwrap();
        let error = env
            .add_statement(&mut Project::new_mock(), &statement)
            .unwrap_err();
        assert_eq!(
            error.message(),
            "axiom is only allowed as a complete declaration value"
        );
        let start = source.find("axiom").unwrap() as u32;
        assert_eq!(
            error.range(),
            Range::new(Position::new(0, start), Position::new(0, start + 5))
        );
        assert!(!env.bindings.has_identifier("bad"));
        assert!(!env.bindings.has_identifier("x"));
        assert!(!env.bindings.has_type_name("T"));
        assert!(env.nodes.is_empty());
        env.add("let bad: Bool = axiom");
        assert!(env.bindings.has_identifier("bad"));
    }
}

#[test]
fn axiomatic_types_require_a_bare_axiom_and_valid_declarations_still_work() {
    use venticorn::environment::Environment;
    use venticorn::statement::Statement;
    for source in ["type Bad: axiom(Bool)", "type Bad: (axiom)"] {
        let mut env = Environment::new_test();
        let statement = Statement::parse_str(source).unwrap();
        env.add_statement(&mut Project::new_mock(), &statement)
            .unwrap_err();
        assert!(!env.bindings.has_type_name("Bad"));
    }
    let mut env = Environment::new_test();
    env.add(
        "type Thing: axiom\nlet thing: Thing = axiom\ndefine identity(x: Thing) -> Thing { axiom }",
    );
    assert!(env.bindings.has_type_name("Thing"));
    assert!(env.bindings.has_identifier("thing"));
    assert!(env.bindings.has_identifier("identity"));
}

#[test]
fn infix_member_and_type_errors_cover_the_complete_operation() {
    let declarations = "type Number: axiom\nclass Number {\n define add(self, other: Number) -> Number { axiom }\n}\nlet a: Number = axiom\n";
    assert_diagnostic(
        &format!("{declarations}let bad: Number = a + true"),
        "a + true",
        "expected type Number",
    );
    assert_diagnostic(
        &format!("{declarations}let bad: Bool = a + a"),
        "a + a",
        "expected type Bool",
    );
    assert_eq!(
        assert_diagnostic(
            &format!("{declarations}let bad: Number = a * a"),
            "a * a",
            "unknown attribute 'Number.mul'",
        ),
        "unknown attribute 'Number.mul'",
    );
}

#[test]
fn terminal_diagnostics_underline_complete_spans_and_preserve_tab_prefixes() {
    let tokens = Token::scan("\t𐐀é left + right suffix");
    let first = tokens.iter().find(|token| token.text() == "left").unwrap();
    let last = tokens.iter().find(|token| token.text() == "right").unwrap();
    let error = Error::new(first, last, "bad operation");
    assert_eq!(
        error.to_string(),
        "bad operation:\n\t𐐀é left + right suffix\n\t   ^^^^^^^^^^^^\n"
    );
    assert_eq!(
        error.range(),
        Range::new(Position::new(0, 5), Position::new(0, 17))
    );
}

#[test]
fn terminal_multiline_diagnostics_highlight_only_the_first_line_suffix() {
    let tokens = Token::scan("\tleft +\n  right");
    let first = tokens.iter().find(|token| token.text() == "left").unwrap();
    let last = tokens.iter().find(|token| token.text() == "right").unwrap();
    assert_eq!(
        Error::new(first, last, "bad operation").to_string(),
        "bad operation:\n\tleft +\n\t^^^^^^\n"
    );
}

#[test]
fn empty_expression_errors_point_to_the_consumed_terminator() {
    assert_diagnostic(
        "let empty: Bool = ()\nlet next: Bool = true",
        ")",
        "expected an expression here",
    );
}

#[test]
fn unexpected_value_operators_name_the_operator_and_cover_the_expression() {
    assert_diagnostic(
        "let bad: Bool = true, false",
        "true, false",
        "unexpected operator ',' in value expression",
    );
}
