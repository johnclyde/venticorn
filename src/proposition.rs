// Modified for Venticorn: theorem and axiom names are optional source metadata.
use std::fmt;

use tower_lsp::lsp_types::Range;

use crate::acorn_type::{AcornType, TypeParam};
use crate::acorn_value::AcornValue;
use crate::module::ModuleId;
use crate::proof_scope::ProofScope;
use crate::proof_step::Truthiness;
use std::collections::{HashMap, HashSet};

// Compatibility exports for existing source metadata callers.
pub use crate::source::{Source, SourceType};

// A value along with information on where to find it in the source.
#[derive(Debug, Clone)]
pub struct Proposition {
    // A boolean value. The essence of the proposition is "value is true".
    pub value: AcornValue,

    // Complete ordered formals, including parameters absent from the value.
    pub params: Vec<TypeParam>,

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
        Self::generic(value, vec![], source)
    }

    /// Construct a proposition retaining every declared formal, including phantom bounds.
    pub fn generic(value: AcornValue, params: Vec<TypeParam>, source: Source) -> Self {
        Self {
            value,
            params,
            source,
            contextual_truthiness: None,
        }
    }

    /// Unresolved declaration or definition metadata cannot enter a fixed proof path.
    pub fn has_generic(&self) -> bool {
        !self.params.is_empty()
            || self.value.is_generic()
            || matches!(&self.source.source_type,
                SourceType::ConstantDefinition(value, _) if value.is_generic())
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
            params: self.params.clone(),
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

    /// Substitute with lexical authority. Missing formals remain ordered and bounded.
    /// Generic actuals for explicit formals are unsupported and leave the input untouched.
    pub fn try_instantiate(
        &self,
        substitutions: &[(String, AcornType)],
        scope: &ProofScope,
    ) -> Result<Self, String> {
        let mut map = HashMap::new();
        for (name, actual) in substitutions {
            if map.insert(name.clone(), actual.clone()).is_some() {
                return Err(format!("duplicate substitution for {name}"));
            }
        }
        let mut names = HashSet::new();
        let mut remaining = Vec::new();
        for formal in &self.params {
            if !names.insert(&formal.name) {
                return Err(format!("duplicate proposition parameter {}", formal.name));
            }
            match map.get(&formal.name) {
                None => remaining.push(formal.clone()),
                Some(actual) => {
                    if actual.is_generic() {
                        return Err(format!(
                            "generic remapping of proposition parameter {} is unsupported",
                            formal.name
                        ));
                    }
                    if !formal.accepts_in_scope(actual, scope) {
                        return Err(format!(
                            "type does not satisfy proposition parameter {}",
                            formal.name
                        ));
                    }
                }
            }
        }
        if !self.value.accepts_substitution_in_scope(&map, scope)
            || matches!(&self.source.source_type, SourceType::ConstantDefinition(value, _)
                if !value.accepts_substitution_in_scope(&map, scope))
        {
            return Err("substitution violates proposition type bounds".into());
        }
        let mut result = self.instantiate_values(substitutions);
        result.params = remaining;
        Ok(result)
    }

    /// Compatibility substitution has no concrete membership authority. For explicit
    /// metadata, a rejected substitution returns the entire original unchanged;
    /// its unresolved formals keep normalization, goals and cache reuse fail-closed.
    /// Legacy propositions without explicit descriptors preserve their prior behavior.
    pub fn instantiate(&self, substitutions: &[(String, AcornType)]) -> Self {
        if self.params.is_empty() {
            self.instantiate_values(substitutions)
        } else {
            self.try_instantiate(substitutions, &ProofScope::default())
                .unwrap_or_else(|_| self.clone())
        }
    }

    fn instantiate_values(&self, substitutions: &[(String, AcornType)]) -> Self {
        let value = self.value.instantiate(substitutions);
        let source = match &self.source.source_type {
            SourceType::ConstantDefinition(value, name) => Source {
                source_type: SourceType::ConstantDefinition(
                    value.instantiate(substitutions),
                    name.clone(),
                ),
                ..self.source.clone()
            },
            _ => self.source.clone(),
        };
        Self {
            value,
            params: self.params.clone(),
            source,
            contextual_truthiness: self.contextual_truthiness,
        }
    }
}
#[cfg(test)]
mod explicit_parameters_tests {
    use super::*;
    use crate::acorn_type::{Class, Typeclass};
    use crate::environment::Environment;
    use crate::fact::Fact;
    use crate::goal::{Goal, GoalContext};
    use crate::monomorphizer::Monomorphizer;
    use crate::normalizer::Normalizer;
    use crate::project::Project;
    use crate::prover::{Outcome, Prover};

    fn setup() -> (TypeParam, AcornType, ProofScope, ProofScope, ProofScope) {
        let class = Typeclass {
            module_id: 7,
            name: "Marked".into(),
        };
        let formal = TypeParam {
            name: "T".into(),
            typeclass: Some(class.clone()),
        };
        let data = Class::new(8, "Item".into());
        let actual = AcornType::Data(data.clone(), vec![]);
        let mut allowed = ProofScope::default();
        allowed.record_instance(data.module_id, &data.name, &class);
        let mut denied = allowed.clone();
        denied.deny_instance(data.module_id, &data.name, &class);
        let mut foreign = ProofScope::default();
        foreign.record_instance(
            data.module_id,
            &data.name,
            &Typeclass {
                module_id: 9,
                ..class
            },
        );
        (formal, actual, allowed, denied, foreign)
    }

    fn same(left: &Proposition, right: &Proposition) {
        assert_eq!(left.value, right.value);
        assert_eq!(left.params, right.params);
        assert_eq!(left.source, right.source);
        assert_eq!(left.truthiness(), right.truthiness());
    }

    #[test]
    fn partial_formals_and_rejected_remappings_preserve_complete_metadata() {
        let (t, actual, allowed, denied, foreign) = setup();
        let u = TypeParam::unconstrained("U");
        let v = TypeParam {
            name: "V".into(),
            ..t.clone()
        };
        let value = AcornValue::constant(
            7,
            "flag".into(),
            vec![
                AcornType::Variable(t.clone()),
                AcornType::Variable(u.clone()),
            ],
            AcornType::Bool,
        );
        let source = Source {
            module: 7,
            depth: 3,
            importable: true,
            source_type: SourceType::ConstantDefinition(value.clone(), "flag".into()),
            ..Source::mock()
        };
        let original = Proposition::generic(value, vec![t.clone(), u.clone(), v.clone()], source)
            .with_truthiness(Truthiness::Counterfactual);
        same(&original, &original.try_instantiate(&[], &allowed).unwrap());
        let partial = original
            .try_instantiate(&[("T".into(), actual.clone())], &allowed)
            .unwrap();
        assert_eq!(partial.params, vec![u.clone(), v.clone()]);
        assert!(partial.has_generic());
        assert_eq!(partial.truthiness(), original.truthiness());
        let SourceType::ConstantDefinition(defined, _) = &partial.source.source_type else {
            panic!("definition")
        };
        assert_eq!(defined, &partial.value);
        assert_eq!(partial.source.module, original.source.module);
        assert_eq!(partial.source.range, original.source.range);
        assert_eq!(partial.source.depth, original.source.depth);
        assert_eq!(partial.source.importable, original.source.importable);
        let completed = partial
            .try_instantiate(
                &[("U".into(), AcornType::Bool), ("V".into(), actual.clone())],
                &allowed,
            )
            .unwrap();
        assert!(completed.params.is_empty());
        assert!(!completed.has_generic());
        assert_eq!(completed.truthiness(), original.truthiness());
        assert_eq!(
            partial.with_value(AcornValue::Bool(true)).params,
            partial.params
        );
        let negated = partial.with_negated_goal(AcornValue::Bool(false));
        assert_eq!(negated.params, partial.params);
        assert_eq!(negated.truthiness(), Truthiness::Counterfactual);
        assert_eq!(negated.source, partial.source.as_negated_goal());
        for scope in [ProofScope::default(), denied, foreign] {
            assert!(original
                .try_instantiate(&[("T".into(), actual.clone())], &scope)
                .is_err());
        }
        // Compatibility has no concrete authority and preserves every field on rejection.
        same(&original, &original.instantiate(&[("T".into(), actual)]));
        let generic = AcornType::Variable(TypeParam {
            name: "Renamed".into(),
            ..t.clone()
        });
        for actual in [
            generic.clone(),
            AcornType::Data(Class::new(8, "List".into()), vec![generic]),
        ] {
            let substitutions = [("T".into(), actual)];
            assert!(original
                .try_instantiate(&substitutions, &allowed)
                .unwrap_err()
                .contains("generic remapping"));
            same(&original, &original.instantiate(&substitutions));
        }
        let source_only = original.with_value(AcornValue::Bool(true));
        assert!(source_only
            .try_instantiate(&[("T".into(), AcornType::Bool)], &allowed)
            .is_err());
        // An implicit bound present only in definition metadata is checked too.
        let implicit = Proposition::new(AcornValue::Bool(true), source_only.source.clone());
        assert!(implicit
            .try_instantiate(&[("T".into(), AcornType::Bool)], &allowed)
            .is_err());
    }

    #[test]
    fn explicit_bounds_control_demand_and_phantom_facts_never_emit() {
        let (formal, actual, allowed, denied, foreign) = setup();
        let predicate =
            |actual| AcornValue::constant(7, "predicate".into(), vec![actual], AcornType::Bool);
        // The occurrence is deliberately unconstrained; the declaration metadata carries the bound.
        let law = Proposition::generic(
            predicate(AcornType::Variable(TypeParam::unconstrained("T"))),
            vec![formal.clone()],
            Source::mock(),
        )
        .with_truthiness(Truthiness::Factual);
        let project = Project::new_mock();
        for (scope, expected) in [
            (ProofScope::default(), Outcome::Exhausted),
            (denied, Outcome::Exhausted),
            (foreign, Outcome::Exhausted),
            (allowed.clone(), Outcome::Success),
        ] {
            let mut context = GoalContext::new(
                &Environment::new(8),
                Goal::Prove(Proposition::new(predicate(actual.clone()), Source::mock())),
                0,
                0,
                0,
            );
            context.proof_scope = scope.clone();
            let mut prover = Prover::with_scope(&project, false, scope);
            prover.add_fact(Fact::Proposition(law.clone()));
            prover.set_goal(&context);
            let mut shallow = prover.clone();
            assert_eq!(prover.quick_search(), expected);
            assert_eq!(shallow.quick_verification_search(), expected);
            if expected == Outcome::Success {
                assert!(prover.get_proof().is_some());
            }
        }
        let phantom = Proposition::generic(
            AcornValue::Bool(false),
            vec![formal.clone()],
            Source::mock(),
        );
        let rejected = phantom.instantiate(&[(
            "T".into(),
            AcornType::Variable(TypeParam::unconstrained("Renamed")),
        )]);
        same(&phantom, &rejected);
        assert!(rejected.has_generic());
        let mut mono = Monomorphizer::with_scope(allowed.clone());
        mono.add_fact(Fact::Proposition(rejected));
        assert!(mono.take_propositions().is_empty());
        let mut partial = law;
        partial.params.push(TypeParam {
            name: "Unused".into(),
            ..formal
        });
        mono.add_fact(Fact::Proposition(partial));
        mono.add_monomorphs(&predicate(actual));
        assert!(mono.take_propositions().is_empty());
        let mut normalizer = Normalizer::new();
        assert_eq!(
            normalizer
                .normalize_monomorphic_fact(Fact::Proposition(phantom))
                .unwrap_err(),
            "cannot normalize unresolved proposition metadata"
        );
    }

    #[test]
    fn phantom_goal_metadata_is_rejected_before_value_only_verification() {
        let (formal, actual, allowed, _, _) = setup();
        let original = Proposition::generic(AcornValue::Bool(true), vec![formal], Source::mock());
        let fixed = original
            .try_instantiate(&[("T".into(), actual)], &allowed)
            .unwrap();
        let project = Project::new_mock();
        for (prop, valid) in [(original, false), (fixed, true)] {
            let mut context = GoalContext::new(&Environment::new(8), Goal::Prove(prop), 0, 0, 0);
            context.proof_scope = allowed.clone();
            assert_eq!(context.goal.has_generic(), !valid);
            let mut prover = Prover::with_scope(&project, false, allowed.clone());
            prover.set_goal(&context);
            let mut shallow = prover.clone();
            if valid {
                assert_eq!(prover.quick_search(), Outcome::Success);
                assert_eq!(shallow.quick_verification_search(), Outcome::Success);
                assert!(prover.get_proof().is_some());
            } else {
                let expected =
                    Outcome::Error("cannot prove a goal with unresolved generic metadata".into());
                assert_eq!(prover.quick_search(), expected);
                assert_eq!(shallow.quick_verification_search(), expected);
                assert!(prover.get_proof().is_none());
            }
        }
    }
}
