use std::collections::HashMap;
use std::fmt;

use crate::acorn_type::AcornType;
use crate::acorn_value::AcornValue;
use crate::constant_name::GlobalConstantName;
use crate::fact::Fact;
use crate::proof_step::Truthiness;
use crate::proposition::Proposition;

// A sorted substitution of type variables belonging to one fact.
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

// Actual types for a constant, kept in declaration order rather than fact-name order.
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

    // Every replacement type must be fixed before it can drive proof search.
    fn assert_full(&self) {
        for t in &self.params {
            assert!(!t.is_generic(), "bad monomorphization: {}", self);
        }
    }
}

// A generic proposition, its proof role and the complete substitutions already emitted.
#[derive(Clone)]
struct GenericPropInfo {
    proposition: Proposition,
    truthiness: Truthiness,
    // Partial substitutions from several constants are not combined.
    instantiations: Vec<PropParams>,
}

// A canonical generic constant's demands and occurrences share one index entry.
#[derive(Clone, Default)]
struct GenericConstantInfo {
    instantiations: Vec<ConstantParams>,
    occurrences: Vec<(usize, ConstantParams)>,
}

// A helper structure to determine which monomorphs are necessary.
// Tracks the generic constants used by each fact and the concrete instances needed by proofs.
#[derive(Clone)]
pub struct Monomorphizer {
    scope: crate::proof_scope::ProofScope,
    // Generic propositions retain their own independent type-variable namespaces.
    prop_info: Vec<GenericPropInfo>,

    // Facts that are fully monomorphized.
    // The Monomorphizer only writes to this, never reads.
    output: Vec<(Proposition, Truthiness)>,

    // Facts, goals and definitions request concrete instances in declaration order.
    constant_info: HashMap<GlobalConstantName, GenericConstantInfo>,
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

    // Adds a fact that could be either generic or monomorphic.
    pub fn add_fact(&mut self, fact: Fact) {
        let Fact::Proposition(proposition, truthiness) = fact;
        // Directly admitted facts can expose concrete instances needed by definitions.
        self.add_monomorphs(&proposition.value);

        let i = self.prop_info.len();
        let mut instances = vec![];
        proposition
            .value
            .find_constants(&|c| !c.params.is_empty() && c.is_generic(), &mut instances);
        if instances.is_empty() {
            // A generic fact without a constant demand cannot yet be specialized safely.
            if proposition.value.is_generic() {
                return;
            }

            // There's nothing to monomorphize here. Just output it.
            self.output.push((proposition, truthiness));
            return;
        }

        self.prop_info.push(GenericPropInfo {
            proposition,
            truthiness,
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

    // Extract monomorphic facts from the prover.
    pub fn take_output(&mut self) -> Vec<(Proposition, Truthiness)> {
        std::mem::take(&mut self.output)
    }

    // Compatibility collection; each proposition and role move without cloning.
    pub fn take_facts(&mut self) -> Vec<Fact> {
        self.take_output()
            .into_iter()
            .map(|(proposition, truthiness)| Fact::Proposition(proposition, truthiness))
            .collect()
    }

    // Monomorphizes a generic constant.
    // For every fact that uses this constant, we want to monomorphize the fact to use this
    // form of the generic constant.
    fn monomorphize_matching_props(
        &mut self,
        constant_key: &GlobalConstantName,
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

    // Try to monomorphize the given fact so that the given params match.
    // The instance params are the way this instance was parametrized in the fact.
    // The monomorph params are how we would like to parametrize this instance.
    // It may or may not be possible to match them up.
    // For example, this may be a fact about foo<bool, T>, and our goal
    // is saying something about foo<Nat, Nat>.
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

        // The selected constant may not expose every bound elsewhere in the same fact.
        if !self.prop_info[prop_id]
            .proposition
            .value
            .accepts_substitution_in_scope(&prop_params, &self.scope)
        {
            return;
        }
        let prop_params = PropParams::new(prop_params);

        if self.prop_info[prop_id]
            .instantiations
            .contains(&prop_params)
        {
            // We already have this monomorph
            return;
        }

        let monomorphic_prop = self.prop_info[prop_id]
            .proposition
            .instantiate(&prop_params.params);
        if monomorphic_prop.value.is_generic() {
            // Matching one constant may leave other type variables in the fact unresolved.
            // Do not emit or remember an incomplete substitution.
            return;
        }
        self.prop_info[prop_id].instantiations.push(prop_params);
        // Definitions can introduce concrete generic calls needed by the current proof.
        // Record this substitution before following those calls to break repeated demand.
        let truthiness = self.prop_info[prop_id].truthiness;
        self.add_monomorphs(&monomorphic_prop.value);
        self.output.push((monomorphic_prop, truthiness));
    }

    // Make sure that we are generating any monomorphizations that are used in this value.
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
