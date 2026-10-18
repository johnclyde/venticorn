// Modified for Venticorn: theorem and axiom names are optional source metadata.
use std::fmt;

use tower_lsp::lsp_types::Range;

use crate::acorn_type::AcornType;
use crate::acorn_value::AcornValue;
use crate::module::ModuleId;
use crate::proof_step::Truthiness;

// Compatibility exports for existing source metadata callers.
pub use crate::source::{Source, SourceType};

// A value along with information on where to find it in the source.
#[derive(Debug, Clone)]
pub struct Proposition {
    // A boolean value. The essence of the proposition is "value is true".
    pub value: AcornValue,

    // Where this proposition came from.
    pub source: Source,

    // An explicit proof-context role never changes the declaration source.
    contextual_truthiness: Option<Truthiness>,
}

impl fmt::Display for Proposition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.value.fmt(f)
    }
}

impl Proposition {
    // Construct a proposition with its source's default lexical role.
    pub fn new(value: AcornValue, source: Source) -> Self {
        Self {
            value,
            source,
            contextual_truthiness: None,
        }
    }

    // Supply a role for this proof context without rewriting source provenance.
    pub fn with_truthiness(mut self, truthiness: Truthiness) -> Self {
        self.contextual_truthiness = Some(truthiness);
        self
    }

    // Effective role in this proof context, falling back to the declaration scope.
    pub fn truthiness(&self) -> Truthiness {
        self.contextual_truthiness.unwrap_or_else(|| {
            if matches!(self.source.source_type, SourceType::NegatedGoal) {
                Truthiness::Counterfactual
            } else if self.source.depth == 0 {
                Truthiness::Factual
            } else {
                Truthiness::Hypothetical
            }
        })
    }

    // Set the declaration location without changing exportability or source identity.
    pub fn with_depth(mut self, depth: u32) -> Self {
        self.source.depth = depth;
        self
    }

    pub fn theorem(
        axiomatic: bool,
        value: AcornValue,
        module: ModuleId,
        range: Range,
        name: Option<String>,
    ) -> Proposition {
        Proposition::new(value, Source::theorem(axiomatic, module, range, 0, name))
    }

    pub fn anonymous(value: AcornValue, module: ModuleId, range: Range) -> Proposition {
        Proposition::new(value, Source::anonymous(module, range, 0))
    }

    // The relationship marker is separate from the block that proves its laws.
    pub fn instance(
        value: Option<AcornValue>,
        module: ModuleId,
        range: Range,
        name: String,
        class: String,
    ) -> Proposition {
        Proposition::new(
            value.unwrap_or(AcornValue::Bool(true)),
            Source::instance(module, range, 0, name, class),
        )
    }

    // The constraint block proves inhabitation; its exported claim remains vacuous.
    pub fn inhabited(module: ModuleId, type_name: &str, range: Range) -> Proposition {
        Proposition::new(
            AcornValue::Bool(true),
            Source::inhabited(module, type_name, range, 0),
        )
    }

    // Compatibility constructor for callers without a more specific member name.
    pub fn type_definition(
        value: AcornValue,
        module: ModuleId,
        range: Range,
        name: String,
    ) -> Proposition {
        Self::type_member_definition(value, module, range, name, "definition".into())
    }

    pub fn type_member_definition(
        value: AcornValue,
        module: ModuleId,
        range: Range,
        name: String,
        member: String,
    ) -> Proposition {
        Proposition::new(
            value,
            Source::type_definition(module, range, 0, name, member),
        )
    }

    pub fn constant_definition(
        value: AcornValue,
        module: ModuleId,
        range: Range,
        constant: AcornValue,
    ) -> Proposition {
        let name = constant
            .as_name()
            .map(|(_, name)| name.to_string())
            .unwrap_or_else(|| constant.to_string());
        Self::named_constant_definition(value, module, range, constant, name)
    }

    pub fn named_constant_definition(
        value: AcornValue,
        module: ModuleId,
        range: Range,
        constant: AcornValue,
        name: String,
    ) -> Proposition {
        Proposition::new(
            value,
            Source::constant_definition(module, range, 0, constant, name),
        )
    }

    pub fn premise(value: AcornValue, module: ModuleId, range: Range) -> Proposition {
        Proposition::new(value, Source::premise(module, range, 0))
    }

    pub fn with_negated_goal(&self, value: AcornValue) -> Proposition {
        let mut proposition = self.with_value(value);
        proposition.source = self.source.as_negated_goal();
        proposition.with_truthiness(Truthiness::Counterfactual)
    }

    // Just changes the value while keeping the other stuff intact
    pub fn with_value(&self, value: AcornValue) -> Proposition {
        Self {
            value,
            source: self.source.clone(),
            contextual_truthiness: self.contextual_truthiness,
        }
    }

    // Theorems and axioms can have names
    // Compatibility name for theorem/axiom declarations, distinct from Source::name.
    pub fn name(&self) -> Option<&str> {
        self.theorem_name()
    }

    pub fn theorem_name(&self) -> Option<&str> {
        match &self.source.source_type {
            SourceType::Axiom(name) | SourceType::Theorem(name) => name.as_deref(),
            _ => None,
        }
    }

    // Substitute provided type variables while preserving unresolved formals.
    pub fn instantiate(&self, params: &[(String, AcornType)]) -> Proposition {
        let value = self.value.instantiate(params);
        let source = match &self.source.source_type {
            SourceType::ConstantDefinition(v, name) => Source {
                source_type: SourceType::ConstantDefinition(v.instantiate(params), name.clone()),
                ..self.source.clone()
            },
            _ => self.source.clone(),
        };
        Self {
            value,
            source,
            contextual_truthiness: self.contextual_truthiness,
        }
    }
}
