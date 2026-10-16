// Modified for Venticorn: unsupported normalized types report errors at the term boundary.
use venticorn::acorn_type::{AcornType, FunctionType};
use venticorn::acorn_value::{AcornValue, FunctionApplication};
use venticorn::normalizer::Normalizer;

fn constant(typ: AcornType, params: Vec<AcornType>) -> AcornValue {
    AcornValue::new_constant(10, "value".into(), params, typ)
}

#[test]
fn unresolved_type_metadata_is_rejected_for_variables_and_all_constants() {
    let variable = AcornType::Variable(venticorn::acorn_type::TypeParam {
        name: "T".into(),
        typeclass: None,
    });
    for value in [
        AcornValue::Variable(0, variable.clone()),
        constant(variable.clone(), vec![]),
        constant(variable.clone(), vec![AcornType::Bool]),
        constant(AcornType::Bool, vec![variable]),
    ] {
        let error = Normalizer::new()
            .term_from_value(&value, false)
            .unwrap_err();
        assert!(error.0.contains("must be instantiated"), "{error:?}");
    }
}

#[test]
fn unsupported_function_shapes_return_errors_instead_of_type_map_panics() {
    let unary = AcornType::new_functional(vec![AcornType::Bool], AcornType::Bool);
    let empty = AcornType::Function(FunctionType {
        arg_types: vec![],
        return_type: Box::new(AcornType::Bool),
    });
    let curried = AcornType::Function(FunctionType {
        arg_types: vec![AcornType::Bool],
        return_type: Box::new(unary),
    });
    for (typ, message) in [
        (empty, "has no arguments"),
        (curried, "functional return type"),
    ] {
        for params in [vec![], vec![AcornType::Bool]] {
            let error = Normalizer::new()
                .term_from_value(&constant(typ.clone(), params), false)
                .unwrap_err();
            assert!(error.0.contains(message), "{error:?}");
        }
        let nested = AcornType::new_functional(vec![typ], AcornType::Bool);
        let value = constant(nested, vec![]);
        assert!(Normalizer::new().term_from_value(&value, false).is_err());
    }
    let bad_result = AcornType::Variable(venticorn::acorn_type::TypeParam {
        name: "T".into(),
        typeclass: None,
    });
    let function = constant(
        AcornType::new_functional(vec![AcornType::Bool], bad_result),
        vec![],
    );
    let application = AcornValue::Application(FunctionApplication {
        function: Box::new(function),
        args: vec![AcornValue::Bool(true)],
    });
    let error = Normalizer::new()
        .term_from_value(&application, false)
        .unwrap_err();
    assert!(error.0.contains("must be instantiated"), "{error:?}");
}
