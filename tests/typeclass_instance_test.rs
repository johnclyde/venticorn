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
    for (target, expected) in [
        ("Bool", "we can only bind members to data types"),
        ("Alias", "we cannot bind members to type aliases"),
        (
            "Box",
            "instance target must be a canonical nongeneric data type in this module",
        ),
    ] {
        let mut env = Environment::new_test();
        env.add("typeclass T: Empty {\n flag: Bool\n}\ninductive State {\n clean\n}\ntype Alias: State\nstructure Box<T> {\n value: T\n}");
        let nodes = env.nodes.len();
        let error = env
            .add_statement(
                &mut Project::new_mock(),
                &Statement::parse_str(&format!("instance {target}: Empty {{}}")).unwrap(),
            )
            .unwrap_err();
        assert_eq!(error.message(), expected);
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
    assert!(project.errors().iter().any(|(_, error)| error
        .message()
        .contains("we can only bind members to types in the current module")));
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
fn concrete_bounds_require_a_preceding_matching_instance() {
    let mut env = Environment::new_test();
    env.add("typeclass T: Marked {\n flag: Bool\n}\ninductive State {\n clean\n}");
    env.add("define generic<T: Marked>(value: T) -> Bool { Marked.flag<T> }");
    env.bad("let invalid: Bool = Marked.flag<State>");
    env.bad("let invalid: Bool = generic(State.clean)");
    env.add("instance State: Marked {\n let flag: Bool = true\n}");
    env.add("let explicit: Bool = Marked.flag<State>");
    env.add("let inferred: Bool = generic(State.clean)");
    env.bad("let invalid: Bool = generic(true)");
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

#[test]
fn instance_member_signatures_match_the_class() {
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
                define mul(self, other: State) -> Bool {
                    true
                }
            }
            "#,
    );
    assert_eq!(env.nodes.len(), nodes);
    assert!(!env.bindings.name_in_use("State.Magma.mul"));
}

#[test]
fn concrete_instance_members_are_accessible() {
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

            theorem commutative(a: State, b: State) {
                State.Magma.mul(a, b) = State.Magma.mul(b, a)
            }
            "#,
    );
}

#[test]
fn declared_concrete_instances_support_generic_class_members() {
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

            theorem commutative(a: State, b: State) {
                Magma.mul(a, b) = Magma.mul(b, a)
            }
            "#,
    );
}

#[test]
fn instance_constant_members_are_admitted() {
    let mut env = Environment::new_test();
    env.add(
        r#"
            typeclass P: PointedSet {
                basepoint: P
            }

            inductive Z2 {
                zero
                one
            }

            instance Z2: PointedSet {
                let basepoint: Z2 = Z2.zero
            }
            "#,
    );
}

#[test]
fn instance_constant_members_reject_extras() {
    let mut env = Environment::new_test();
    env.add(
        r#"
            typeclass P: PointedSet {
                basepoint: P
            }

            inductive Z2 {
                zero
                one
            }
            "#,
    );
    env.bad(
        r#"
            instance Z2: PointedSet {
                let basepoint: Z2 = Z2.zero
                let other: Z2 = Z2.one
            }
            "#,
    );
    assert!(!env.bindings.name_in_use("Z2.PointedSet.basepoint"));
    assert!(!env.bindings.name_in_use("Z2.PointedSet.other"));
}

#[test]
fn instance_constant_members_require_the_declared_type() {
    let mut env = Environment::new_test();
    env.add(
        r#"
            typeclass P: PointedSet {
                basepoint: P
            }

            inductive Z2 {
                zero
                one
            }
            "#,
    );
    env.bad(
        r#"
            instance Z2: PointedSet {
                let basepoint: Bool = true
            }
            "#,
    );
    assert!(!env.bindings.name_in_use("Z2.PointedSet.basepoint"));
    assert!(!env.bindings.name_in_use("Z2.PointedSet.other"));
}

#[test]
fn forbid_class_on_alias_849() {
    let mut env = Environment::new_test();
    let input = r#"
            type Foo: axiom
            type Bar: Foo
            class Bar {
                let b: Bool = true
            }
            "#;
    let error = env
        .add_tokens(
            &mut venticorn::project::Project::new_mock(),
            venticorn::token::Token::scan(input),
        )
        .unwrap_err();
    assert_eq!(error.message(), "we cannot bind members to type aliases");
    assert_eq!(error.range().start.line, 3);
    assert!(!env.bindings.name_in_use("Bar.b"));
}

#[test]
fn forbid_class_on_alias_850() {
    let mut env = Environment::new_test();
    env.add(
        r#"
            type Foo: axiom
            type Bar: Foo
            "#,
    );
    env.bad(
        r#"
            class Bar {
                let b: Bool = true
            }
            "#,
    );
}

#[test]
fn forbid_instance_on_alias_851() {
    let mut env = Environment::new_test();
    env.add(
        r#"
            typeclass F: Flagged {
                flag: Bool
            }
            type Foo: axiom
            type Bar: Foo
            "#,
    );
    env.bad(
        r#"
            instance Bar: Flagged {
                let flag: Bool = true
            }
            "#,
    );
}

#[test]
fn typechecking_captures_instance_relationships_853() {
    let mut env = Environment::new_test();
    env.add(
        r#"
            typeclass F: Flagged {
                flag: Bool
            }
            type Foo: axiom
            instance Foo: Flagged {
                let flag: Bool = true
            }
            define get_flag<F: Flagged>(x: F) -> Bool {
                F.flag
            }
            "#,
    );
}

#[test]
fn arbitrary_type_attributes_854() {
    let mut env = Environment::new_test();
    env.add(
        r#"
            typeclass F: Flagged {
                flag: Bool
            }
            theorem goal<F: Flagged> {
                F.flag or not F.flag
            }
            "#,
    );
}

#[test]
fn typechecking_captures_instance_relationships_856() {
    let mut env = Environment::new_test();
    env.add(
        r#"
        typeclass F: Flagged {
            flag: Bool
        }
        type Foo: axiom
        instance Foo: Flagged {
            let flag: Bool = true
        }
        define get_flag<F: Flagged>(x: F) -> Bool {
            F.flag
        }
        "#,
    );
    env.bad(
        r#"
        theorem goal {
            get_flag(true)
        }
        "#,
    );
}

#[test]
fn bool_not_instance_of_anything_858() {
    let mut env = Environment::new_test();
    env.add(
        r#"
        typeclass F: Flagged {
            flag: Bool
        }
        type Foo: axiom
        instance Foo: Flagged {
            let flag: Bool = true
        }
        define get_flag<F: Flagged>(x: F) -> Bool {
            F.flag
        }
        "#,
    );
    env.bad(
        r#"
        theorem goal {
            get_flag(true)
        }
        "#,
    );
}

#[test]
fn typechecking_captures_instance_relationships_858() {
    let mut env = Environment::new_test();
    env.add(
        r#"
        typeclass F: Flagged {
            flag: Bool
        }
        type Foo: axiom
        define get_flag<F: Flagged>(x: F) -> Bool {
            F.flag
        }
        "#,
    );
    env.bad(
        r#"
        theorem goal(f: Foo) {
            get_flag(f)
        }
        "#,
    );
}

#[test]
fn typechecking_captures_instance_relationships_860() {
    let mut env = Environment::new_test();
    env.add(
        r#"
        typeclass F: Flagged {
            flag: Bool
        }
        type Foo: axiom
        type Bar: axiom
        instance Bar: Flagged {
            let flag: Bool = true
        }
        define get_flag<F: Flagged>(x: F) -> Bool {
            F.flag
        }
        theorem goal_bar(b: Bar) {
            get_flag(b)
        }
        "#,
    );
    env.bad(
        r#"
        theorem goal_foo(f: Foo) {
            get_flag(f)
        }
        "#,
    );
}

#[test]
#[ignore = "pending callable typeclass conditions"]
fn typeclasses_can_have_conditions_862() {
    let mut env = Environment::new_test();
    env.add(
        r#"
        typeclass S: Singleton {
            value: S

            unique(x: S) {
                x = S.value
            }
        }

        theorem are_equal<S: Singleton>(a: S, b: S) {
            a = b
        } by {
            Singleton.unique(a)
            Singleton.unique(b)
        }
        "#,
    );
}
