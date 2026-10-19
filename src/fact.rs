use crate::acorn_type::{AcornType, Class, Typeclass};
use crate::acorn_value::AcornValue;
use crate::potential_value::PotentialValue;
use crate::proof_step::Truthiness;
use crate::proposition::Proposition;
use crate::source::Source;

/// A defining equation with one authoritative proposition metadata record.
/// This public constructor conveys equality only, never permission to alias atoms.
#[derive(Clone, Debug)]
pub struct DefinitionFact {
    potential: PotentialValue,
    definition: AcornValue,
    proposition: Proposition,
}

impl DefinitionFact {
    pub fn new(
        potential: PotentialValue,
        definition: AcornValue,
        source: Source,
    ) -> Result<Self, String> {
        let params = potential.unresolved_params().to_vec();
        let constant = potential.clone().to_generic_value();
        if !matches!(constant, AcornValue::Constant(_)) {
            return Err("a definition fact requires a named constant".into());
        }
        constant.validate()?;
        definition.validate()?;
        if constant.get_type() != definition.get_type() {
            return Err("a definition fact must preserve the declared type".into());
        }
        let value = constant.inflate_function_definition(definition.clone());
        value.validate()?;
        Ok(Self {
            potential,
            definition,
            proposition: Proposition::generic(value, params, source),
        })
    }

    pub fn potential(&self) -> &PotentialValue {
        &self.potential
    }

    pub fn definition(&self) -> &AcornValue {
        &self.definition
    }

    pub fn proposition(&self) -> &Proposition {
        &self.proposition
    }

    pub fn into_proposition(self) -> Proposition {
        self.proposition
    }

    pub(crate) fn with_truthiness(mut self, role: Truthiness) -> Self {
        self.proposition = self.proposition.with_truthiness(role);
        self
    }

    // Expansion may change an equation. Such a fact keeps the resulting proposition,
    // but no longer carries a defining payload that describes the pre-expansion value.
    pub(crate) fn prepare(self, transform: impl FnOnce(Proposition) -> Proposition) -> Fact {
        let proposition = transform(self.proposition.clone());
        if proposition.value == self.proposition.value
            && proposition.params == self.proposition.params
        {
            Fact::Definition(Self {
                proposition,
                ..self
            })
        } else {
            Fact::Proposition(proposition)
        }
    }
}

// A statement available under a particular proof context.
#[derive(Clone, Debug)]
pub enum Fact {
    Proposition(Proposition),
    Definition(DefinitionFact),
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
            Fact::Definition(definition) => &definition.proposition.source,
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
            Fact::Definition(definition) => Some(definition.proposition()),
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
            Fact::Definition(definition) => {
                let proposition = definition.into_proposition();
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
            // Substitution consumes the defining relationship; no alias capability survives.
            Fact::Definition(definition) => {
                Fact::Proposition(definition.proposition.instantiate(params))
            }
            Fact::Instance(data, class, source) => {
                Fact::Instance(data.clone(), class.clone(), source.clone())
            }
        }
    }
}

#[cfg(test)]
mod definition_tests {
    use super::*;
    use crate::acorn_type::TypeParam;
    use crate::names::{GlobalName, LocalName};
    use crate::normalizer::Normalizer;
    use crate::source::SourceType;

    #[test]
    fn definition_view_preserves_complete_formals_source_and_context() {
        let formals = vec![
            TypeParam {
                name: "Phantom".into(),
                typeclass: Some(Typeclass {
                    module_id: 7,
                    name: "Marked".into(),
                }),
            },
            TypeParam::unconstrained("Other"),
        ];
        let potential = PotentialValue::constant_named(
            GlobalName::new(3, LocalName::unqualified("flag")),
            AcornType::Bool,
            formals.clone(),
        );
        let value = potential.clone().to_generic_value();
        let source = Source::constant_definition(3, Default::default(), 4, value.clone(), "flag");
        let definition =
            DefinitionFact::new(potential.clone(), AcornValue::Bool(true), source.clone())
                .unwrap()
                .with_truthiness(Truthiness::Counterfactual);
        assert_eq!(definition.potential(), &potential);
        assert_eq!(definition.definition(), &AcornValue::Bool(true));
        let fact = Fact::Definition(definition);
        let proposition = fact.as_proposition().unwrap();
        assert_eq!(proposition.params, formals);
        assert_eq!(
            proposition.value,
            AcornValue::equals(value, AcornValue::Bool(true))
        );
        assert_eq!(fact.source(), &source);
        assert_eq!(fact.truthiness(), Some(Truthiness::Counterfactual));
        let partial = fact.instantiate(&[("Other".into(), AcornType::Bool)]);
        assert!(matches!(partial, Fact::Proposition(_)));
        let partial = partial.as_proposition().unwrap();
        assert_eq!(partial.params, formals[..1]);
        assert!(partial.has_generic());
        assert_eq!(partial.truthiness(), Truthiness::Counterfactual);
        assert_eq!(partial.source.depth, 4);
        assert_eq!(partial.source.range, source.range);
        assert_eq!(partial.source.importable, source.importable);
        let SourceType::ConstantDefinition(AcornValue::Constant(reference), _) =
            &partial.source.source_type
        else {
            panic!("definition metadata retained")
        };
        assert_eq!(reference.params[0], AcornType::Variable(formals[0].clone()));
        assert_eq!(reference.params[1], AcornType::Bool);
        assert!(Normalizer::new().normalize_monomorphic_fact(fact).is_err());
    }

    #[test]
    fn definition_expansion_keeps_only_consistent_payloads() {
        let potential = PotentialValue::constant(1, "flag", AcornType::Bool, vec![]);
        let original =
            DefinitionFact::new(potential, AcornValue::Bool(true), Source::mock()).unwrap();
        let stamped = original.clone().prepare(|mut p| {
            p.source.depth = 2;
            p.source.importable = false;
            p.with_truthiness(Truthiness::Hypothetical)
        });
        assert!(matches!(stamped, Fact::Definition(_)));
        assert_eq!(stamped.source().depth, 2);
        assert!(!stamped.source().importable);
        assert_eq!(stamped.truthiness(), Some(Truthiness::Hypothetical));
        let changed = original.prepare(|p| p.with_value(AcornValue::Bool(true)));
        assert!(matches!(changed, Fact::Proposition(_)));
        assert_eq!(
            changed.as_proposition().unwrap().value,
            AcornValue::Bool(true)
        );
    }

    #[test]
    fn definition_constructor_checks_types_and_lowers_an_explicit_equation() {
        let potential = PotentialValue::constant(1, "flag", AcornType::Bool, vec![]);
        let definition =
            DefinitionFact::new(potential.clone(), AcornValue::Bool(true), Source::mock()).unwrap();
        let expected = definition.proposition().clone();
        let mut normalizer = Normalizer::new();
        let steps = normalizer
            .normalize_monomorphic_fact(Fact::Definition(definition))
            .unwrap();
        assert!(!steps.is_empty());
        assert!(steps
            .iter()
            .all(|step| step.truthiness == Truthiness::Factual));
        let direct = Normalizer::new()
            .normalize_monomorphic_fact(Fact::Proposition(expected))
            .unwrap();
        assert_eq!(steps.len(), direct.len());
        for (actual, expected) in steps.iter().zip(&direct) {
            assert_eq!(actual.clause, expected.clause);
        }
        let lambda = AcornValue::Lambda(
            vec![AcornType::Bool],
            Box::new(AcornValue::Variable(0, AcornType::Bool)),
        );
        assert!(DefinitionFact::new(potential, lambda.clone(), Source::mock()).is_err());
        assert!(DefinitionFact::new(
            PotentialValue::Resolved(AcornValue::Bool(true)),
            AcornValue::Bool(true),
            Source::mock()
        )
        .is_err());
        let function = PotentialValue::constant(1, "identity", lambda.get_type(), vec![]);
        let definition = DefinitionFact::new(function, lambda, Source::mock()).unwrap();
        assert!(matches!(
            definition.proposition().value,
            AcornValue::ForAll(..)
        ));
        definition.proposition().value.validate().unwrap();
    }
}
