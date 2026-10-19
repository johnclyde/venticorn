use std::collections::HashMap;
use std::fmt;

use crate::acorn_type::AcornType;
use crate::acorn_value::AcornValue;
use crate::fact::Fact;
use crate::names::GlobalName;
use crate::proof_step::Truthiness;
use crate::proposition::{MonomorphicProposition, Proposition};

/// A sorted substitution of type variables belonging to one fact.
#[derive(PartialEq, Eq, Clone)]
struct PropParams {
    params: Vec<(String, AcornType)>,
}

impl PropParams {
    fn new(params: impl IntoIterator<Item = (String, AcornType)>) -> Self {
        let mut params: Vec<_> = params.into_iter().collect();
        params.sort();
        Self { params }
    }
}

/// Actual types for a constant, kept in declaration order rather than fact-name order.
#[derive(PartialEq, Eq, Clone)]
struct ConstantParams {
    params: Vec<AcornType>,
}

impl fmt::Display for ConstantParams {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (i, t) in self.params.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", t)?;
        }
        Ok(())
    }
}

impl ConstantParams {
    fn new(params: Vec<AcornType>) -> Self {
        Self { params }
    }

    /// Every replacement type must be fixed before it can drive proof search.
    fn assert_full(&self) {
        for t in &self.params {
            assert!(!t.is_generic(), "bad monomorphization: {}", self);
        }
    }
}

/// A generic proposition, its proof role and the complete substitutions already emitted.
#[derive(Clone)]
struct GenericPropInfo {
    proposition: Proposition,
    /// Partial substitutions from several constants are not combined.
    instantiations: Vec<PropParams>,
}

/// A canonical generic constant's demands and occurrences share one index entry.
#[derive(Clone, Default)]
struct GenericConstantInfo {
    instantiations: Vec<ConstantParams>,
    occurrences: Vec<(usize, ConstantParams)>,
}

/// A helper structure to determine which monomorphs are necessary.
/// Tracks the generic constants used by each fact and the concrete instances needed by proofs.
#[derive(Clone)]
pub struct Monomorphizer {
    /// Immutable lexical authority; relation facts cannot grant or revive memberships.
    scope: crate::proof_scope::ProofScope,
    /// Generic propositions retain their own independent type-variable namespaces.
    prop_info: Vec<GenericPropInfo>,

    /// Facts that are fully monomorphized.
    /// The Monomorphizer only writes to this, never reads.
    output: Vec<MonomorphicProposition>,

    /// Facts, goals and definitions request concrete instances in declaration order.
    constant_info: HashMap<GlobalName, GenericConstantInfo>,
}

impl Monomorphizer {
    pub fn new() -> Monomorphizer {
        Self::with_scope(crate::proof_scope::ProofScope::default())
    }

    pub fn with_scope(scope: crate::proof_scope::ProofScope) -> Self {
        Monomorphizer {
            scope,
            prop_info: vec![],
            output: vec![],
            constant_info: HashMap::new(),
        }
    }

    /// Adds a fact that could be either generic or monomorphic.
    pub fn add_fact(&mut self, fact: Fact) {
        match fact {
            Fact::Proposition(proposition) => {
                self.add_proposition(proposition);
            }
            Fact::Definition(definition) => self.add_proposition(definition.into_proposition()),
            Fact::Instance(data, class, _) => {
                // Reflections must already belong to the captured lexical scope.
                // They cannot revive denied or not-yet-visible memberships.
                if !self.scope.has_class_membership(&data, &class) {
                    return;
                }
                // The immutable scope already contains all allowed relations;
                // no output or mutable membership table is needed.
            }
        }
    }

    fn add_proposition(&mut self, proposition: Proposition) {
        // Directly admitted facts can expose concrete instances needed by definitions.
        self.add_monomorphs(&proposition.value);

        let i = self.prop_info.len();
        let mut instances = vec![];
        proposition
            .value
            .find_constants(&|c| !c.params.is_empty() && c.is_generic(), &mut instances);
        if instances.is_empty() {
            // A generic fact without a constant demand cannot yet be specialized safely.
            let Ok(proposition) = proposition.into_monomorphic() else {
                return;
            };

            // There's nothing to monomorphize here. Just output it.
            self.output.push(proposition);
            return;
        }

        self.prop_info.push(GenericPropInfo {
            proposition,
            instantiations: vec![],
        });

        // Store a reference to our generic instances in the index
        for c in &instances {
            let constant_key = c.name.clone();
            let params = ConstantParams::new(c.type_arguments().cloned().collect());
            self.constant_info
                .entry(constant_key)
                .or_default()
                .occurrences
                .push((i, params));
        }

        // Check how this new generic fact should be monomorphized
        for c in instances {
            let constant_key = c.name.clone();
            let instance_params = ConstantParams::new(c.type_arguments().cloned().collect());
            if let Some(info) = self.constant_info.get(&constant_key) {
                for monomorph_params in info.instantiations.clone() {
                    self.try_to_monomorphize_prop(i, &instance_params, &monomorph_params);
                }
            }
        }
    }

    /// Extract checked monomorphic propositions without weakening their metadata guarantee.
    pub fn take_monomorphic(&mut self) -> Vec<MonomorphicProposition> {
        std::mem::take(&mut self.output)
    }

    /// Compatibility output recovers the general representation without cloning.
    pub fn take_propositions(&mut self) -> Vec<Proposition> {
        self.take_monomorphic()
            .into_iter()
            .map(MonomorphicProposition::into_proposition)
            .collect()
    }

    /// Compatibility output derives each role from the moved proposition.
    pub fn take_output(&mut self) -> Vec<(Proposition, Truthiness)> {
        self.take_propositions()
            .into_iter()
            .map(|proposition| {
                let truthiness = proposition.truthiness();
                (proposition, truthiness)
            })
            .collect()
    }

    /// Compatibility collection; each proposition and role move without cloning.
    pub fn take_facts(&mut self) -> Vec<Fact> {
        self.take_propositions()
            .into_iter()
            .map(Fact::Proposition)
            .collect()
    }

    /// Monomorphizes a generic constant.
    /// For every fact that uses this constant, we want to monomorphize the fact to use this
    /// form of the generic constant.
    fn monomorphize_matching_props(
        &mut self,
        constant_key: &GlobalName,
        monomorph_params: &ConstantParams,
    ) {
        monomorph_params.assert_full();
        let info = self.constant_info.entry(constant_key.clone()).or_default();
        if info.instantiations.contains(monomorph_params) {
            return;
        }
        info.instantiations.push(monomorph_params.clone());

        // Clone only this constant's occurrences before recursive demand updates.
        for (prop_id, instance_params) in info.occurrences.clone() {
            self.try_to_monomorphize_prop(prop_id, &instance_params, monomorph_params);
        }
    }

    /// Try to monomorphize the given fact so that the given params match.
    /// The instance params are the way this instance was parametrized in the fact.
    /// The monomorph params are how we would like to parametrize this instance.
    /// It may or may not be possible to match them up.
    /// For example, this may be a fact about `foo<bool, T>`, and our goal
    /// is saying something about `foo<Nat, Nat>`.
    fn try_to_monomorphize_prop(
        &mut self,
        prop_id: usize,
        instance_params: &ConstantParams,
        monomorph_params: &ConstantParams,
    ) {
        // Our goal is to find the "fact params", a way in which we can parametrize
        // the whole fact so that the instance params become the monomorph params.
        if instance_params.params.len() != monomorph_params.params.len() {
            return;
        }
        let mut prop_params = HashMap::new();
        for (instance_type, monomorph_type) in instance_params
            .params
            .iter()
            .zip(monomorph_params.params.iter())
        {
            if !instance_type.match_instance_in_scope(monomorph_type, &mut prop_params, &self.scope)
            {
                return;
            }
        }

        let prop_params = PropParams::new(prop_params);

        if self.prop_info[prop_id]
            .instantiations
            .contains(&prop_params)
        {
            // We already have this monomorph
            return;
        }

        // Check every formal, value and definition bound before substitution and emission.
        let Ok(monomorphic_prop) = self.prop_info[prop_id]
            .proposition
            .try_instantiate(&prop_params.params, &self.scope)
        else {
            return;
        };
        let Ok(monomorphic_prop) = monomorphic_prop.into_monomorphic() else {
            // Matching one constant may leave other type variables in the fact unresolved.
            // Do not emit or remember an incomplete substitution.
            return;
        };
        self.prop_info[prop_id].instantiations.push(prop_params);
        // Definitions can introduce concrete generic calls needed by the current proof.
        // Record this substitution before following those calls to break repeated demand.
        self.add_monomorphs(monomorphic_prop.value());
        self.output.push(monomorphic_prop);
    }

    /// Make sure that we are generating any monomorphizations that are used in this value.
    pub fn add_monomorphs(&mut self, value: &AcornValue) {
        let mut monomorphs = vec![];
        value.find_constants(
            &|c| !c.params.is_empty() && !c.is_generic(),
            &mut monomorphs,
        );
        for c in monomorphs {
            self.monomorphize_matching_props(
                &c.name,
                &ConstantParams::new(c.type_arguments().cloned().collect()),
            );
        }
    }
}

#[cfg(test)]
mod membership_fact_tests {
    use super::*;
    use crate::acorn_type::{Class, TypeParam, Typeclass};
    use crate::project::Project;
    use crate::proof_scope::ProofScope;
    use crate::proposition::{Source, SourceType};
    use crate::prover::{Outcome, Prover};

    #[test]
    fn reflected_membership_cannot_grant_or_revive_bounded_proof_authority() {
        let class = Typeclass {
            module_id: 2,
            name: "Marked".into(),
        };
        let foreign = Typeclass {
            module_id: 9,
            name: "Marked".into(),
        };
        let data = Class::new(3, "Item".into());
        let actual = AcornType::Data(data.clone(), vec![]);
        let formal = AcornType::Variable(TypeParam {
            name: "T".into(),
            typeclass: Some(class.clone()),
        });
        let predicate =
            |actual| AcornValue::constant(2, "flag".into(), vec![actual], AcornType::Bool);
        let law = Fact::new(
            Proposition::new(predicate(formal), Source::mock()),
            Truthiness::Factual,
        );
        let goal = Proposition::new(predicate(actual), Source::mock());
        let reflection = Fact::Instance(
            data.clone(),
            class.clone(),
            Source {
                module: data.module_id,
                source_type: SourceType::Instance(data.name.clone(), class.name.clone()),
                ..Source::mock()
            },
        );
        assert!(reflection.as_proposition().is_none());
        assert!(reflection.truthiness().is_none());
        assert!(reflection.clone().into_proposition().is_none());
        let mut allowed = ProofScope::default();
        allowed.record_instance(data.module_id, &data.name, &class);
        let mut denied = allowed.clone();
        denied.deny_instance(data.module_id, &data.name, &class);
        let mut wrong_owner = ProofScope::default();
        wrong_owner.record_instance(data.module_id, &data.name, &foreign);
        let project = Project::new_mock();
        for (scope, expected) in [
            (ProofScope::default(), Outcome::Exhausted),
            (denied, Outcome::Exhausted),
            (wrong_owner, Outcome::Exhausted),
            (allowed, Outcome::Success),
        ] {
            for reflect_first in [true, false] {
                let original_scope = scope.clone();
                let mut mono = Monomorphizer::with_scope(scope.clone());
                mono.add_fact(reflection.clone());
                assert_eq!(mono.scope, original_scope);
                assert!(mono.take_output().is_empty());
                let mut prover = Prover::with_scope(&project, false, scope.clone());
                if reflect_first {
                    prover.add_fact(reflection.clone());
                }
                prover.add_fact(law.clone());
                if !reflect_first {
                    prover.add_fact(reflection.clone());
                }
                let mut context = crate::goal::GoalContext::new(
                    &crate::environment::Environment::new(2),
                    crate::goal::Goal::Prove(goal.clone()),
                    0,
                    0,
                    0,
                );
                context.proof_scope = scope.clone();
                prover.set_goal(&context);
                let mut shallow = prover.clone();
                assert_eq!(prover.quick_search(), expected);
                assert_eq!(shallow.quick_verification_search(), expected);
                if expected == Outcome::Success {
                    assert!(prover.get_proof().is_some());
                }
            }
        }
    }
}
