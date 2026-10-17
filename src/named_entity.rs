use crate::acorn_type::{AcornType, Typeclass, UnresolvedType};
use crate::acorn_value::AcornValue;
use crate::compilation::{self, ErrorSource};
use crate::module::ModuleId;
use crate::potential_value::PotentialValue;
use crate::unresolved_constant::UnresolvedConstant;

// A name can refer to any of these things.
#[derive(Debug)]
pub(crate) enum NamedEntity {
    Value(AcornValue),
    Type(AcornType),
    Module(ModuleId),
    Typeclass(Typeclass),
    Instance(ModuleId, String),
    Unresolved(UnresolvedConstant),
    UnresolvedType(UnresolvedType),
}

impl NamedEntity {
    pub(crate) fn new(value: PotentialValue) -> Self {
        match value {
            PotentialValue::Unresolved(unresolved) => NamedEntity::Unresolved(unresolved),
            PotentialValue::Resolved(value) => NamedEntity::Value(value),
        }
    }

    pub(crate) fn expect_potential_value(
        self,
        expected_type: Option<&AcornType>,
        source: &dyn ErrorSource,
    ) -> compilation::Result<PotentialValue> {
        match self {
            NamedEntity::Unresolved(unresolved) => Ok(PotentialValue::Unresolved(unresolved)),
            entity => Ok(PotentialValue::Resolved(
                entity.expect_value(expected_type, source)?,
            )),
        }
    }

    pub(crate) fn expect_value(
        self,
        expected_type: Option<&AcornType>,
        source: &dyn ErrorSource,
    ) -> compilation::Result<AcornValue> {
        match self {
            NamedEntity::Unresolved(unresolved) => Err(source.error(&format!(
                "value {} requires type arguments",
                unresolved.name.local_name
            ))),
            NamedEntity::Value(value) => {
                value.check_type(source, expected_type)?;
                Ok(value)
            }
            NamedEntity::Type(_) | NamedEntity::UnresolvedType(_) => {
                Err(source.error("name refers to a type but we expected a value"))
            }
            NamedEntity::Module(_) => {
                Err(source.error("name refers to a module but we expected a value"))
            }
            NamedEntity::Typeclass(_) => {
                Err(source.error("name refers to a typeclass but we expected a value"))
            }
            NamedEntity::Instance(..) => Err(source.error("instance namespace is not a value")),
        }
    }

    pub(crate) fn expect_type(self, source: &dyn ErrorSource) -> compilation::Result<AcornType> {
        match self {
            NamedEntity::Unresolved(unresolved) => Err(source.error(&format!(
                "value {} requires type arguments",
                unresolved.name.local_name
            ))),
            NamedEntity::Value(_) => {
                Err(source.error("name refers to a value but we expected a type"))
            }
            NamedEntity::Type(t) => Ok(t),
            NamedEntity::UnresolvedType(t) => Err(source.error(&format!(
                "type {} requires {} type parameters",
                t.name,
                t.params.len()
            ))),
            NamedEntity::Module(_) => {
                Err(source.error("name refers to a module but we expected a type"))
            }
            NamedEntity::Typeclass(_) => {
                Err(source.error("name refers to a typeclass but we expected a type"))
            }
            NamedEntity::Instance(..) => Err(source.error("instance namespace is not a type")),
        }
    }
}
