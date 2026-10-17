use crate::acorn_type::AcornType;
use crate::acorn_value::AcornValue;
use crate::compilation::{self, ErrorSource};
use crate::unresolved_constant::UnresolvedConstant;

// A named declaration may still need type arguments before it becomes a proof value.
#[derive(Clone, Debug, PartialEq)]
pub enum PotentialValue {
    Unresolved(UnresolvedConstant),
    Resolved(AcornValue),
}

impl PotentialValue {
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
