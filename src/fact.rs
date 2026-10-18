use crate::acorn_type::AcornType;
use crate::proof_step::Truthiness;
use crate::proposition::Proposition;

// A statement available under a particular proof context.
#[derive(Clone, Debug)]
pub enum Fact {
    Proposition(Proposition, Truthiness),
}

impl Fact {
    // Compatibility constructor for proposition facts.
    pub fn new(proposition: Proposition, truthiness: Truthiness) -> Fact {
        Fact::Proposition(proposition, truthiness)
    }

    pub fn as_proposition(&self) -> Option<&Proposition> {
        match self {
            Fact::Proposition(proposition, _) => Some(proposition),
        }
    }

    pub fn truthiness(&self) -> Option<Truthiness> {
        match self {
            Fact::Proposition(_, truthiness) => Some(*truthiness),
        }
    }

    pub fn into_proposition(self) -> Option<(Proposition, Truthiness)> {
        match self {
            Fact::Proposition(proposition, truthiness) => Some((proposition, truthiness)),
        }
    }

    pub fn local(&self) -> bool {
        matches!(self.truthiness(), Some(role) if role != Truthiness::Factual)
    }

    // Substitutes known type variables, preserving those not provided.
    pub fn instantiate(&self, params: &[(String, AcornType)]) -> Fact {
        match self {
            Fact::Proposition(proposition, truthiness) => {
                Fact::Proposition(proposition.instantiate(params), *truthiness)
            }
        }
    }
}
