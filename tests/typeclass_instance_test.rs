use venticorn::environment::Environment;

#[test]
#[ignore = "concrete instance admission is not implemented yet"]
fn concrete_magma_instance_is_admitted() {
    let mut env = Environment::new_test();
    env.add(
        r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }
            
            inductive State {
                clean
                dirty
            }

            instance State: Magma {
                define mul(self, other: State) -> State {
                    if self = State.clean and other = State.clean {
                        State.clean
                    } else {
                        State.dirty
                    }
                }
            }
            "#,
    );
}

#[test]
fn instance_header_body_ranges_and_following_statement_are_preserved() {
    use tower_lsp::lsp_types::{Position, Range};
    use venticorn::statement::{Statement, StatementInfo};
    use venticorn::token::{Token, TokenIter};
    let source = "instance State: algebra.Magma {\n    define mul(self, other: State) -> State {\n        State.dirty\n    }\n}";
    let mut tokens = TokenIter::new(Token::scan(&format!("{source}\ntheorem {{ true }}")));
    let (first, _) = Statement::parse(&mut tokens, false).unwrap();
    let first = first.unwrap();
    assert_eq!(first.to_string(), source);
    assert_eq!(
        first.range(),
        Range::new(Position::new(0, 0), Position::new(4, 1))
    );
    let StatementInfo::Instance(instance) = first.statement else {
        panic!()
    };
    assert_eq!(
        instance.type_name.range(),
        Range::new(Position::new(0, 9), Position::new(0, 14))
    );
    assert_eq!(
        instance.typeclass.range(),
        Range::new(Position::new(0, 16), Position::new(0, 29))
    );
    assert_eq!(
        instance.body.range(),
        Range::new(Position::new(0, 30), Position::new(4, 1))
    );
    assert_eq!(instance.body.statements.len(), 1);
    assert_eq!(
        instance.body.statements[0].range().start,
        Position::new(1, 4)
    );
    assert_eq!(instance.body.statements[0].range().end, Position::new(3, 5));
    let (second, _) = Statement::parse(&mut tokens, false).unwrap();
    assert!(matches!(
        second.unwrap().statement,
        StatementInfo::Theorem(_)
    ));
}

#[test]
fn malformed_and_truncated_instance_declarations_return_diagnostics() {
    use venticorn::statement::Statement;
    use venticorn::token::{Token, TokenIter};
    for source in [
        "instance",
        "instance State",
        "instance State:",
        "instance state: Magma {}",
        "instance State Magma {}",
        "instance State: Magma",
        "instance State: Magma {",
        "instance State: Magma { define mul(self, other: State) -> State { State.dirty }",
    ] {
        assert!(Statement::parse_str(source).is_err(), "{source}");
    }
    let source = "instance State: algebra.Magma { define keep(self) -> State { self } }";
    for end in source.char_indices().map(|(i, _)| i).chain([source.len()]) {
        let mut tokens = TokenIter::new(Token::scan(&source[..end]));
        let _ = Statement::parse(&mut tokens, false);
    }
}

#[test]
fn unsupported_instance_admission_is_located_and_publishes_nothing() {
    use venticorn::builder::BuildStatus;
    use venticorn::project::Project;
    use venticorn::statement::Statement;
    let source = "instance State: Magma { define mul(self, other: State) -> State { self } }";
    let mut env = Environment::new_test();
    env.add("let kept: Bool = true");
    let nodes = env.nodes.len();
    let line = env.last_line();
    let statement = Statement::parse_str(source).unwrap();
    let error = env
        .add_statement(&mut Project::new_mock(), &statement)
        .unwrap_err();
    assert!(error
        .message()
        .contains("instance declarations are not supported yet"));
    assert_eq!(error.range(), statement.first_token.range());
    assert_eq!(env.nodes.len(), nodes);
    assert_eq!(env.last_line(), line);
    assert!(env.bindings.name_in_use("kept"));
    for name in ["State", "Magma", "State.mul"] {
        assert!(!env.bindings.name_in_use(name));
    }
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", source);
    assert_eq!(project.errors().len(), 1);
    let report = project.sync_build_report();
    assert_eq!(report.status, BuildStatus::Error);
    assert!(report.events.iter().all(|event| event.verified.is_none()));
    assert_eq!(project.cached_build().num_modules(), 0);
}

#[test]
fn instance_declaration_exact_format_round_trip() {
    let source = indoc::indoc! {"
        instance State: Magma {
            define mul(self, other: State) -> State {
                State.dirty
            }
        }"};
    let statement = venticorn::statement::Statement::parse_str(source).unwrap();
    assert_eq!(statement.to_string(), source);
}
