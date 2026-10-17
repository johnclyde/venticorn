// Modified for Venticorn: preserve anonymous goal identity when code generation is unavailable.
use tower_lsp::lsp_types::Range;

use crate::acorn_value::AcornValue;
use crate::environment::Environment;
use crate::module::ModuleId;
use crate::proposition::Proposition;

#[derive(Debug, Clone)]
pub enum Goal {
    // Prove that this proposition is true.
    Prove(Proposition),

    // Find a simplified form of this value.
    Solve(AcornValue, Range),
}

impl Goal {
    pub fn value(&self) -> &AcornValue {
        match self {
            Goal::Prove(p) => &p.value,
            Goal::Solve(v, _) => v,
        }
    }

    pub fn range(&self) -> Range {
        match self {
            Goal::Prove(p) => p.source.range,
            Goal::Solve(_, r) => *r,
        }
    }
}

// A goal along with some information related to it.
pub struct GoalContext {
    pub proof_scope: crate::proof_scope::ProofScope,
    pub module_id: ModuleId,

    // Legacy storage for the human-readable description. Use description() when displaying it.
    pub name: String,

    // The goal itself.
    pub goal: Goal,

    // The zero-based line where we would insert a proof for this goal.
    // The last line of a proof block, or the first line of a blockless claim.
    pub proof_insertion_line: u32,

    // Whether we need to insert a block, if we do insert a proof.
    pub insert_block: bool,

    // Whether it's okay if we discover an inconsistency in the provided facts.
    // If it's not okay, we warn the user.
    pub inconsistency_okay: bool,

    // Inclusive source bounds, including the entire proof block.
    pub first_line: u32,
    pub last_line: u32,

    // Cache identity includes every enclosing proof block, whose later statements
    // may affect this goal’s hypotheses or inconsistency policy.
    pub(crate) cache_last_line: u32,
}

impl GoalContext {
    // Human-readable text is separate from the stable source identifier used by fact selection.
    pub fn description(&self) -> &str {
        &self.name
    }

    pub fn new(
        env: &Environment,
        goal: Goal,
        proof_insertion_line: u32,
        first_line: u32,
        last_line: u32,
    ) -> GoalContext {
        let name = match &goal {
            Goal::Prove(proposition) => match proposition.theorem_name() {
                Some(name) => name.to_string(),
                None => env
                    .bindings
                    .value_to_code(&proposition.value)
                    .unwrap_or_else(|_| {
                        format!("claim at line {}", proposition.source.range.start.line + 1)
                    }),
            },
            Goal::Solve(value, range) => env
                .bindings
                .value_to_code(value)
                .map(|code| format!("solve {}", code))
                .unwrap_or_else(|_| format!("solve at line {}", range.start.line + 1)),
        };
        GoalContext {
            proof_scope: env.bindings.proof_scope().clone(),
            module_id: env.module_id,
            name,
            goal,
            proof_insertion_line,
            insert_block: env.implicit,
            inconsistency_okay: env.includes_explicit_false,
            first_line,
            last_line,
            cache_last_line: last_line,
        }
    }
}
