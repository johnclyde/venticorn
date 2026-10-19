use venticorn::fact::Fact;
use venticorn::project::Project;
use venticorn::proof_step::Truthiness;
use venticorn::prover::Outcome;
use venticorn::source::SourceType;

#[test]
fn parsed_definitions_keep_their_complete_declaration_view_and_proof_behavior() {
    let mut project = Project::new_mock();
    project.mock(
        "/mock/main.ac",
        "typeclass M: Marked {\n flag: Bool\n}\ndefine chosen<T: Marked, U> -> Bool { true }\ndefine fixed -> Bool { true }\ntheorem goal { fixed }",
    );
    let module = project.expect_ok("main");
    let env = project.get_env_by_id(module).unwrap();
    let mut names = Vec::new();
    for node in &env.nodes {
        let Some(Fact::Definition(definition)) = node.get_fact() else {
            continue;
        };
        let proposition = definition.proposition();
        let SourceType::ConstantDefinition(value, name) = &proposition.source.source_type else {
            panic!("definition source")
        };
        assert_eq!(proposition.params, env.bindings.get_params(name));
        assert_eq!(definition.potential().clone().to_generic_value(), *value);
        assert_eq!(
            definition.definition(),
            env.bindings.get_definition(name).unwrap()
        );
        assert_eq!(proposition.truthiness(), Truthiness::Factual);
        assert_eq!(proposition.source.depth, 0);
        assert_eq!(proposition.source.module, module);
        assert!(proposition.source.importable);
        assert!(node.is_structural());
        assert!(!node.has_goal());
        if name == "chosen" {
            assert_eq!(proposition.params.len(), 2);
            assert!(proposition.params[0].typeclass.is_some());
            assert!(proposition.has_generic());
        } else {
            assert_eq!(name, "fixed");
            assert!(proposition.params.is_empty());
            assert!(!proposition.has_generic());
        }
        names.push(name.clone());
    }
    assert_eq!(names, ["chosen", "fixed"]);
    let goals = env.iter_goals().collect::<Vec<_>>();
    assert_eq!(goals.len(), 1);
    for node in goals {
        let context = node.goal_context().unwrap();
        for shallow in [true, false] {
            let mut prover = project.prover_for_node(&node, false);
            prover.set_goal(&context);
            let outcome = if shallow {
                prover.quick_shallow_search()
            } else {
                prover.quick_search()
            };
            assert_eq!(outcome, Outcome::Success);
            assert!(prover.get_proof().is_some());
        }
    }
}
