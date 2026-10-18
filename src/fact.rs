use crate::acorn_type::AcornType;
use crate::proof_step::Truthiness;
use crate::proposition::Proposition;

// A proposition and the contextual role under which it is available.
#[derive(Clone, Debug)]
pub struct Fact {
    pub proposition: Proposition,
    pub truthiness: Truthiness,
}

impl Fact {
    pub fn new(proposition: Proposition, truthiness: Truthiness) -> Fact {
        Fact {
            proposition,
            truthiness,
        }
    }

    pub fn local(&self) -> bool {
        self.truthiness != Truthiness::Factual
    }

    // Substitutes known type variables, preserving those not provided.
    pub fn instantiate(&self, params: &[(String, AcornType)]) -> Fact {
        Fact::new(self.proposition.instantiate(params), self.truthiness)
    }
}
