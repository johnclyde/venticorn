use crate::acorn_type::{AcornType, TypeParam};
use crate::acorn_value::AcornValue;
use crate::compilation::{self, ErrorSource};
use crate::module::ModuleId;
use crate::proof_scope::ProofScope;

// A generic declaration whose type arguments have not been inferred yet.
#[derive(Clone, Debug, PartialEq)]
pub struct UnresolvedConstant {
    pub(crate) module_id: ModuleId,
    pub(crate) name: String,
    // Complete formal parameters remain in declaration order, including phantom bounds.
    pub(crate) params: Vec<TypeParam>,
    pub(crate) generic_type: AcornType,
}

impl UnresolvedConstant {
    pub(crate) fn resolve(
        &self,
        source: &dyn ErrorSource,
        actuals: Vec<AcornType>,
        scope: &ProofScope,
    ) -> compilation::Result<AcornValue> {
        if actuals.len() != self.params.len() {
            return Err(source.error(&format!(
                "expected {} type parameters, but got {}",
                self.params.len(),
                actuals.len()
            )));
        }
        for (formal, actual) in self.params.iter().zip(&actuals) {
            if !formal.accepts_in_scope(actual, scope) {
                return Err(source.error(&format!(
                    "type argument {} does not satisfy the class bound on {}",
                    actual, formal.name
                )));
            }
        }
        let substitutions = self
            .params
            .iter()
            .zip(&actuals)
            .map(|(formal, actual)| (formal.name.clone(), actual.clone()))
            .collect::<Vec<_>>();
        let instance_type = self.generic_type.instantiate(&substitutions);
        Ok(AcornValue::constant(
            self.module_id,
            self.name.clone(),
            actuals,
            instance_type,
        ))
    }
}
