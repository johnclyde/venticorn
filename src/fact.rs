use crate::acorn_type::{AcornType, Class, Typeclass};
use crate::acorn_value::AcornValue;
use crate::proof_step::Truthiness;
use crate::proposition::Proposition;
use crate::source::Source;

// A statement available under a particular proof context.
#[derive(Clone, Debug)]
pub enum Fact {
    Proposition(Proposition),
    // A declaration relation, never an independent grant of proof authority.
    Instance(Class, Typeclass, Source),
}

impl Fact {
    /// Construct a fresh proposition with the source's default lexical role.
    /// Existing propositions should retain their metadata through Fact::new.
    pub fn proposition(value: AcornValue, source: Source) -> Self {
        Fact::Proposition(Proposition::new(value, source))
    }

    pub fn is_instance(&self) -> bool {
        matches!(self, Fact::Instance(..))
    }

    pub fn source(&self) -> &Source {
        match self {
            Fact::Proposition(proposition) => &proposition.source,
            Fact::Instance(_, _, source) => source,
        }
    }

    // Compatibility constructor records the explicit role on the proposition.
    pub fn new(proposition: Proposition, truthiness: Truthiness) -> Fact {
        Fact::Proposition(proposition.with_truthiness(truthiness))
    }

    pub fn as_proposition(&self) -> Option<&Proposition> {
        match self {
            Fact::Proposition(proposition) => Some(proposition),
            Fact::Instance(..) => None,
        }
    }

    pub fn truthiness(&self) -> Option<Truthiness> {
        self.as_proposition().map(Proposition::truthiness)
    }

    // Compatibility view derives the role rather than storing another copy.
    pub fn into_proposition(self) -> Option<(Proposition, Truthiness)> {
        match self {
            Fact::Proposition(proposition) => {
                let truthiness = proposition.truthiness();
                Some((proposition, truthiness))
            }
            Fact::Instance(..) => None,
        }
    }

    pub fn local(&self) -> bool {
        matches!(self.truthiness(), Some(role) if role != Truthiness::Factual)
    }

    // Substitutes known type variables, preserving those not provided and the role.
    pub fn instantiate(&self, params: &[(String, AcornType)]) -> Fact {
        match self {
            Fact::Proposition(proposition) => Fact::Proposition(proposition.instantiate(params)),
            Fact::Instance(data, class, source) => {
                Fact::Instance(data.clone(), class.clone(), source.clone())
            }
        }
    }
}
