use venticorn::environment::Environment;

#[test]
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
fn undefined_instance_target_is_located_and_publishes_nothing() {
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
    assert_eq!(error.message(), "undefined type name 'State'");
    use tower_lsp::lsp_types::{Position, Range};
    assert_eq!(
        error.range(),
        Range::new(Position::new(0, 9), Position::new(0, 14))
    );
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

#[test]
fn instance_preparation_rolls_back_members_facts_and_declaration_identity() {
    use venticorn::project::Project;
    use venticorn::statement::Statement;
    let setup =
        "typeclass T: Marked {\n value: T\n keep: T -> T\n}\ninductive State {\n clean\n dirty\n}";
    let valid = "instance State: Marked {\n let value: State = State.clean\n define keep(self) -> State { self }\n}";
    for (body, reason) in [
        (
            "let value: State = State.clean",
            "missing required member 'keep'",
        ),
        (
            "let value: State = State.clean\n let extra: Bool = true",
            "unknown or duplicate",
        ),
        (
            "let value: State = State.clean\n define extra(self) -> State { self }",
            "unknown or duplicate",
        ),
        (
            "let value: State = State.clean\n let value: State = State.dirty",
            "unknown or duplicate",
        ),
        (
            "let value: Bool = true\n define keep(self) -> State { self }",
            "must have type State",
        ),
        (
            "let value: State = State.clean\n define keep(self) -> Bool { true }",
            "must have type State -> State",
        ),
        (
            "let value: State = State.clean\n define keep<U>(self) -> State { self }",
            "cannot declare type parameters",
        ),
        (
            "let value: State = State.clean\n theorem { true }",
            "only let and define",
        ),
    ] {
        let mut env = Environment::new_test();
        env.add(setup);
        let nodes = env.nodes.len();
        let line = env.last_line();
        let error = env
            .add_statement(
                &mut Project::new_mock(),
                &Statement::parse_str(&format!("instance State: Marked {{\n{body}\n}}")).unwrap(),
            )
            .unwrap_err();
        assert!(error.message().contains(reason), "{error}");
        assert_eq!(env.nodes.len(), nodes);
        assert_eq!(env.last_line(), line);
        for name in [
            "State.Marked.value",
            "State.Marked.keep",
            "State.Marked.extra",
        ] {
            assert!(!env.bindings.name_in_use(name), "{name}");
        }
        env.add(valid);
        let nodes = env.nodes.len();
        let error = env
            .add_statement(
                &mut Project::new_mock(),
                &Statement::parse_str(valid).unwrap(),
            )
            .unwrap_err();
        assert_eq!(error.message(), "instance already defined");
        assert_eq!(env.nodes.len(), nodes);
    }
}

#[test]
fn instance_targets_are_local_canonical_nongeneric_types() {
    use venticorn::project::Project;
    use venticorn::statement::Statement;
    for target in ["Bool", "Alias", "Box"] {
        let mut env = Environment::new_test();
        env.add("typeclass T: Empty {\n flag: Bool\n}\ninductive State {\n clean\n}\ntype Alias: State\nstructure Box<T> {\n value: T\n}");
        let nodes = env.nodes.len();
        let error = env
            .add_statement(
                &mut Project::new_mock(),
                &Statement::parse_str(&format!("instance {target}: Empty {{}}")).unwrap(),
            )
            .unwrap_err();
        assert_eq!(
            error.message(),
            "instance target must be a canonical nongeneric data type in this module"
        );
        assert_eq!(env.nodes.len(), nodes);
        env.add("instance State: Empty {\n let flag: Bool = true\n}");
        env.bad("instance State: Empty {\n let flag: Bool = true\n}");
    }
    let mut project = Project::new_mock();
    project.mock("/mock/foreign.ac", "inductive State {\n clean\n}");
    project.mock(
        "/mock/main.ac",
        "from foreign import State\ntypeclass T: Empty {\n flag: Bool\n}\ninstance State: Empty {}",
    );
    assert!(project
        .errors()
        .iter()
        .any(|(_, error)| error.message().contains("canonical nongeneric")));
    let mut parent = Environment::new_test();
    parent.add("typeclass T: Empty {\n flag: Bool\n}\ninductive State {\n clean\n}");
    let mut child = parent.child(0, false);
    let nodes = child.nodes.len();
    let error = child
        .add_statement(
            &mut Project::new_mock(),
            &Statement::parse_str("instance State: Empty {}").unwrap(),
        )
        .unwrap_err();
    assert_eq!(
        error.message(),
        "instance declarations are only supported at the top level"
    );
    assert_eq!(child.nodes.len(), nodes);
    parent.add("instance State: Empty {\n let flag: Bool = true\n}");
}

#[test]
fn instance_class_lookup_is_canonical_and_display_collisions_are_rejected() {
    use venticorn::project::Project;
    use venticorn::statement::Statement;
    let mut project = Project::new_mock();
    project.mock("/mock/left.ac", "typeclass T: Marked {\n flag: Bool\n}");
    project.mock("/mock/right.ac", "typeclass T: Marked {\n flag: T\n}");
    project.mock("/mock/main.ac", "import left\nimport right\ninductive State {\n clean\n}\ninstance State: left.Marked {\n let flag: Bool = true\n}");
    let module = project.expect_ok("main");
    let mut env = project.get_env_by_id(module).unwrap().child(0, false);
    env.top_level = true;
    let nodes = env.nodes.len();
    let statement =
        Statement::parse_str("instance State: right.Marked {\n let flag: State = State.clean\n}")
            .unwrap();
    let error = env.add_statement(&mut project, &statement).unwrap_err();
    assert_eq!(
        error.message(),
        "instance namespace conflicts with a different typeclass"
    );
    assert_eq!(env.nodes.len(), nodes);
    assert_eq!(
        env.bindings
            .get_constant_value("State.Marked.flag")
            .unwrap()
            .get_type(),
        venticorn::acorn_type::AcornType::Bool
    );
    let error = env
        .add_statement(
            &mut project,
            &Statement::parse_str("instance State: Missing {}").unwrap(),
        )
        .unwrap_err();
    assert!(error.message().contains("unknown identifier"), "{error}");
    assert_eq!(env.nodes.len(), nodes);
}

#[test]
fn admitted_implementations_do_not_grant_unchecked_concrete_bounds() {
    let mut env = Environment::new_test();
    env.add("typeclass T: Marked {\n flag: Bool\n}\ninductive State {\n clean\n}\ninstance State: Marked {\n let flag: Bool = true\n}");
    env.bad("let invalid: Bool = Marked.flag<State>");
    env.add("define generic<T: Marked>(value: T) -> Bool { Marked.flag<T> }");
    env.bad("let invalid: Bool = generic(State.clean)");
}

#[test]
fn concrete_instance_implementation_body_is_admitted() {
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
fn instance_requires_every_declared_member() {
    let mut env = Environment::new_test();
    env.add(
        r#"
            typeclass B: Bimagma {
                mul1: (B, B) -> B
                mul2: (B, B) -> B
            }

            inductive State {
                clean
                dirty
            }
            "#,
    );
    let nodes = env.nodes.len();
    let line = env.last_line();
    env.bad(
        r#"
            instance State: Bimagma {
                define mul1(self, other: State) -> State {
                    State.clean
                }
            }
            "#,
    );
    assert_eq!(env.nodes.len(), nodes);
    assert_eq!(env.last_line(), line);
    assert!(!env.bindings.name_in_use("State.Bimagma.mul1"));
    assert!(!env.bindings.name_in_use("State.Bimagma.mul2"));
    env.add("instance State: Bimagma {\n define mul1(self, other: State) -> State { self }\n define mul2(self, other: State) -> State { other }\n}");
}

#[test]
fn imported_class_requirements_come_from_the_canonical_defining_module() {
    use venticorn::project::Project;
    for (actual, accepted) in [("true", false), ("State.clean", true)] {
        let mut project = Project::new_mock();
        project.mock("/mock/left.ac", "typeclass T: Marked {\n value: Bool\n}");
        project.mock("/mock/right.ac", "typeclass T: Marked {\n value: T\n}");
        let value_type = if accepted { "State" } else { "Bool" };
        project.mock("/mock/main.ac", &format!("import left\nimport right\ninductive State {{\n clean\n}}\ninstance State: right.Marked {{\n let value: {value_type} = {actual}\n}}"));
        if accepted {
            let module = project.expect_ok("main");
            let env = project.get_env_by_id(module).unwrap();
            assert_eq!(
                env.bindings
                    .get_constant_value("State.Marked.value")
                    .unwrap()
                    .get_type(),
                env.bindings.get_type_for_name("State").unwrap().clone()
            );
        } else {
            assert!(project.errors().iter().any(
                |(_, error)| error.message() == "instance member 'value' must have type State"
            ));
        }
    }
}

#[test]
fn instance_rejects_undeclared_members() {
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
            "#,
    );
    let nodes = env.nodes.len();
    env.bad(
        r#"
            instance State: Magma {
                define mul(self, other: State) -> State {
                    State.clean
                }
                define add(self, other: State) -> State {
                    State.clean
                }
            }
            "#,
    );
    assert_eq!(env.nodes.len(), nodes);
    assert!(!env.bindings.name_in_use("State.Magma.mul"));
    assert!(!env.bindings.name_in_use("State.Magma.add"));
}
