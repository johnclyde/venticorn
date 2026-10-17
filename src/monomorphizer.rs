use std::collections::HashMap;
use std::fmt;

use crate::acorn_type::AcornType;
use crate::acorn_value::AcornValue;
use crate::constant_map::ConstantKey;
use crate::fact::Fact;

// A sorted substitution of type variables belonging to one fact.
#[derive(PartialEq, Eq, Clone)]
struct FactParams {
    params: Vec<(String, AcornType)>,
}

impl FactParams {
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

// A helper structure to determine which monomorphs are necessary.
// Tracks the generic constants used by each fact and the concrete instances needed by proofs.
#[derive(Clone)]
pub struct Monomorphizer {
    scope: crate::proof_scope::ProofScope,
    // Generic facts retain their own independent type-variable namespaces.
    generic_facts: Vec<Fact>,

    // Facts that are fully monomorphized.
    // The Monomorphizer only writes to this, never reads.
    output_facts: Vec<Fact>,

    // The complete substitutions already emitted for each fact.
    // Combining partial substitutions from several constants is not supported.
    // Parallel to generic_facts.
    instantiations_for_fact: Vec<Vec<FactParams>>,

    // The concrete constant instances requested by facts, goals, or their definitions.
    // Indexed by constant id.
    instantiations_for_constant: HashMap<ConstantKey, Vec<ConstantParams>>,

    // An index tracking how each generic constant is used in the generic facts.
    // This is updated whenever we add a fact.
    // Lists (index in generic facts, params for the constant) for each occurrence.
    generic_constants: HashMap<ConstantKey, Vec<(usize, ConstantParams)>>,
}

impl Monomorphizer {
    pub fn new() -> Monomorphizer {
        Self::with_scope(crate::proof_scope::ProofScope::default())
    }

    pub fn with_scope(scope: crate::proof_scope::ProofScope) -> Self {
        Monomorphizer {
            scope,
            generic_facts: vec![],
            output_facts: vec![],
            instantiations_for_fact: vec![],
            instantiations_for_constant: HashMap::new(),
            generic_constants: HashMap::new(),
        }
    }

    // Adds a fact that could be either generic or monomorphic.
    pub fn add_fact(&mut self, fact: Fact) {
        // Directly admitted facts can expose concrete instances needed by definitions.
        self.add_monomorphs(&fact.value);

        let i = self.generic_facts.len();
        let mut instances = vec![];
        fact.value
            .find_constants(&|c| !c.params.is_empty() && c.is_generic(), &mut instances);
        if instances.is_empty() {
            // A generic fact without a constant demand cannot yet be specialized safely.
            if fact.value.is_generic() {
                return;
            }

            // There's nothing to monomorphize here. Just output it.
            self.output_facts.push(fact);
            return;
        }

        self.generic_facts.push(fact);
        self.instantiations_for_fact.push(vec![]);

        // Store a reference to our generic instances in the index
        for c in &instances {
            let constant_key = c.key();
            let params = ConstantParams::new(c.type_arguments().cloned().collect());
            self.generic_constants
                .entry(constant_key)
                .or_insert(vec![])
                .push((i, params));
        }

        // Check how this new generic fact should be monomorphized
        for c in instances {
            let constant_key = c.key();
            let instance_params = ConstantParams::new(c.type_arguments().cloned().collect());
            if let Some(monomorphs) = self.instantiations_for_constant.get(&constant_key) {
                for monomorph_params in monomorphs.clone() {
                    self.try_to_monomorphize_fact(i, &instance_params, &monomorph_params);
                }
            }
        }
    }

    // Extract monomorphic facts from the prover.
    pub fn take_facts(&mut self) -> Vec<Fact> {
        std::mem::take(&mut self.output_facts)
    }

    // Monomorphizes a generic constant.
    // For every fact that uses this constant, we want to monomorphize the fact to use this
    // form of the generic constant.
    fn monomorphize_matching_facts(
        &mut self,
        constant_key: &ConstantKey,
        monomorph_params: &ConstantParams,
    ) {
        monomorph_params.assert_full();
        let monomorphs = self
            .instantiations_for_constant
            .entry(constant_key.clone())
            .or_insert(vec![]);
        if monomorphs.contains(&monomorph_params) {
            // We already have this monomorph
            return;
        }
        monomorphs.push(monomorph_params.clone());

        // Handle all the facts that mention this constant without monomorphizing it.
        if let Some(instances) = self.generic_constants.get(&constant_key) {
            for (fact_id, instance_params) in instances.clone() {
                self.try_to_monomorphize_fact(fact_id, &instance_params, monomorph_params);
            }
        }
    }

    // Try to monomorphize the given fact so that the given params match.
    // The instance params are the way this instance was parametrized in the fact.
    // The monomorph params are how we would like to parametrize this instance.
    // It may or may not be possible to match them up.
    // For example, this may be a fact about foo<bool, T>, and our goal
    // is saying something about foo<Nat, Nat>.
    fn try_to_monomorphize_fact(
        &mut self,
        fact_id: usize,
        instance_params: &ConstantParams,
        monomorph_params: &ConstantParams,
    ) {
        // Our goal is to find the "fact params", a way in which we can parametrize
        // the whole fact so that the instance params become the monomorph params.
        if instance_params.params.len() != monomorph_params.params.len() {
            return;
        }
        let mut fact_params = HashMap::new();
        for (instance_type, monomorph_type) in instance_params
            .params
            .iter()
            .zip(monomorph_params.params.iter())
        {
            if !instance_type.match_instance_in_scope(monomorph_type, &mut fact_params, &self.scope)
            {
                return;
            }
        }

        // The selected constant may not expose every bound elsewhere in the same fact.
        if !self.generic_facts[fact_id]
            .value
            .accepts_substitution_in_scope(&fact_params, &self.scope)
        {
            return;
        }
        let fact_params = FactParams::new(fact_params);

        if self.instantiations_for_fact[fact_id].contains(&fact_params) {
            // We already have this monomorph
            return;
        }

        let monomorphic_fact = self.generic_facts[fact_id].instantiate(&fact_params.params);
        if monomorphic_fact.value.is_generic() {
            // Matching one constant may leave other type variables in the fact unresolved.
            // Do not emit or remember an incomplete substitution.
            return;
        }
        self.instantiations_for_fact[fact_id].push(fact_params);
        // Definitions can introduce concrete generic calls needed by the current proof.
        // Record this substitution before following those calls to break repeated demand.
        self.add_monomorphs(&monomorphic_fact.value);
        self.output_facts.push(monomorphic_fact);
    }

    // Make sure that we are generating any monomorphizations that are used in this value.
    pub fn add_monomorphs(&mut self, value: &AcornValue) {
        let mut monomorphs = vec![];
        value.find_constants(
            &|c| !c.params.is_empty() && !c.is_generic(),
            &mut monomorphs,
        );
        for c in monomorphs {
            self.monomorphize_matching_facts(
                &c.key(),
                &ConstantParams::new(c.type_arguments().cloned().collect()),
            );
        }
    }
}
