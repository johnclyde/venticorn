use crate::acorn_type::{AcornType, TypeParam};
use crate::acorn_value::AcornValue;
use crate::compilation::{self, ErrorSource};
use crate::module::ModuleId;
use crate::names::{GlobalName, LocalName};
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
        Self::constant_named(
            GlobalName::new(module_id, LocalName::from_legacy(name)),
            constant_type,
            params,
        )
    }

    pub fn constant_named(
        name: GlobalName,
        constant_type: AcornType,
        params: Vec<TypeParam>,
    ) -> Self {
        if params.is_empty() {
            Self::Resolved(AcornValue::constant_named(name, vec![], constant_type))
        } else {
            Self::Unresolved(UnresolvedConstant {
                name,
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

    // Complete declaration-order formals, including parameters absent from the signature.
    pub fn unresolved_params(&self) -> &[TypeParam] {
        match self {
            Self::Unresolved(value) => &value.params,
            Self::Resolved(_) => &[],
        }
    }

    // Resolve the declaration generically without inferring formals from its signature.
    pub fn to_generic_value(self) -> AcornValue {
        match self {
            Self::Unresolved(value) => value.to_generic_value(),
            Self::Resolved(value) => value,
        }
    }

    pub fn value(self, source: &dyn ErrorSource) -> compilation::Result<AcornValue> {
        match self {
            PotentialValue::Resolved(value) => Ok(value),
            PotentialValue::Unresolved(unresolved) => Err(source.error(&format!(
                "value {} requires type arguments",
                unresolved.name.local_name
            ))),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::acorn_type::Typeclass;
    use crate::constant_name::{GlobalConstantName, LocalConstantName};
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

    #[test]
    fn generic_value_preserves_complete_formals_and_resolved_aliases() {
        let formals = vec![
            TypeParam {
                name: "Phantom".into(),
                typeclass: Some(Typeclass {
                    module_id: 7,
                    name: "Marked".into(),
                }),
            },
            TypeParam::unconstrained("Other"),
        ];
        let value = PotentialValue::constant(3, "flag", AcornType::Bool, formals.clone())
            .to_generic_value();
        let AcornValue::Constant(instance) = value else {
            panic!("expected constant")
        };
        assert_eq!(instance.name.module_id, 3);
        assert_eq!(instance.name.local_name.to_string(), "flag");
        assert_eq!(
            instance.params,
            formals
                .into_iter()
                .map(AcornType::Variable)
                .collect::<Vec<_>>()
        );
        assert_eq!(instance.instance_type, AcornType::Bool);
        let resolved = AcornValue::Lambda(
            vec![AcornType::Bool],
            Box::new(AcornValue::Variable(0, AcornType::Bool)),
        );
        assert_eq!(
            PotentialValue::Resolved(resolved.clone()).to_generic_value(),
            resolved
        );
    }

    #[test]
    fn pending_names_keep_canonical_classes_and_bounded_legacy_compatibility() {
        let params = vec![TypeParam::unconstrained("Phantom")];
        let old = PotentialValue::constant(3, "Pair.new", AcornType::Bool, params.clone());
        let typed = PotentialValue::constant_named(
            GlobalConstantName::new(3, LocalConstantName::attribute("Pair", "new")),
            AcornType::Bool,
            params.clone(),
        );
        assert_eq!(old, typed);
        let first = Typeclass {
            module_id: 7,
            name: "Marked".into(),
        };
        let other = Typeclass {
            module_id: 8,
            name: "Marked".into(),
        };
        let make = |class: &Typeclass| {
            PotentialValue::constant_named(
                GlobalConstantName::new(3, LocalConstantName::instance(class, "flag", "State")),
                AcornType::Bool,
                params.clone(),
            )
        };
        let left = make(&first);
        let right = make(&other);
        let opaque = PotentialValue::constant(3, "State.Marked.flag", AcornType::Bool, params);
        assert_ne!(left, right);
        assert_ne!(left, opaque);
        assert_ne!(right, opaque);
        let PotentialValue::Unresolved(declaration) = left else {
            panic!("expected pending")
        };
        assert_eq!(
            declaration.name,
            GlobalConstantName::new(3, LocalConstantName::instance(&first, "flag", "State"))
        );
        assert_eq!(declaration.params, [TypeParam::unconstrained("Phantom")]);
    }
}
