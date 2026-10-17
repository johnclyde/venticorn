use crate::acorn_type::{AcornType, TypeParam};
use crate::acorn_value::AcornValue;
use crate::compilation::{self, ErrorSource};
use crate::module::ModuleId;
use crate::unresolved_constant::UnresolvedConstant;

// A named declaration may still need type arguments before it becomes a proof value.
#[derive(Clone, Debug, PartialEq)]
pub enum PotentialValue {
    Unresolved(UnresolvedConstant),
    Resolved(AcornValue),
}

impl PotentialValue {
    pub fn constant(
        module_id: ModuleId,
        name: &str,
        constant_type: AcornType,
        params: Vec<TypeParam>,
    ) -> Self {
        if params.is_empty() {
            Self::Resolved(AcornValue::new_constant(
                module_id,
                name.to_string(),
                vec![],
                constant_type,
            ))
        } else {
            Self::Unresolved(UnresolvedConstant {
                module_id,
                name: name.to_string(),
                params,
                generic_type: constant_type,
            })
        }
    }

    // Internal callers use this only after introducing a constant with no type parameters.
    pub fn resolved(self) -> Option<AcornValue> {
        match self {
            PotentialValue::Resolved(value) => Some(value),
            PotentialValue::Unresolved(..) => None,
        }
    }

    // Pending declarations expose their generic signature only to inference.
    pub fn get_type(&self) -> AcornType {
        match self {
            PotentialValue::Unresolved(unresolved) => unresolved.generic_type.clone(),
            PotentialValue::Resolved(value) => value.get_type(),
        }
    }

    pub fn value(self, source: &dyn ErrorSource) -> compilation::Result<AcornValue> {
        match self {
            PotentialValue::Resolved(value) => Ok(value),
            PotentialValue::Unresolved(unresolved) => Err(source.error(&format!(
                "value {} requires type arguments",
                unresolved.name
            ))),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::acorn_type::Typeclass;
    use crate::proof_scope::ProofScope;
    use crate::token::TokenType;

    #[test]
    fn constant_constructor_preserves_ordered_phantom_bounds() {
        let class = Typeclass {
            module_id: 2,
            name: "Marked".into(),
        };
        let formals = vec![
            TypeParam {
                name: "Z".into(),
                typeclass: Some(class.clone()),
            },
            TypeParam::unconstrained("A"),
        ];
        let value = PotentialValue::constant(1, "flag", AcornType::Bool, formals.clone());
        let PotentialValue::Unresolved(declaration) = value else {
            panic!("phantom formals must remain unresolved even with a Boolean signature");
        };
        assert_eq!(declaration.params, formals);
        let token = TokenType::Identifier.new_token("flag");
        let scope = ProofScope::default();
        assert!(declaration
            .resolve(&token, vec![AcornType::Bool, AcornType::Bool], &scope)
            .is_err());
        let bounded = AcornType::Arbitrary(TypeParam {
            name: "Fixed".into(),
            typeclass: Some(class),
        });
        let actuals = vec![bounded, AcornType::Bool];
        let AcornValue::Constant(instance) = declaration
            .resolve(&token, actuals.clone(), &scope)
            .unwrap()
        else {
            panic!("expected a specialized constant");
        };
        assert_eq!(instance.params, actuals);
        assert_eq!(instance.instance_type, AcornType::Bool);
    }
}
