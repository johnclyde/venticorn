// Modified for Venticorn: completed verification metadata with a read-only public API.
use crate::acorn_value::AcornValue;
use crate::goal::{Goal, GoalContext};
use crate::module::{ModuleHash, ModuleRef};
use crate::project::ModuleFingerprint;
use std::collections::{BTreeMap, BTreeSet, HashMap};

// Advisory source selections, never evidence that a current goal is verified.
// Module references survive load-ID changes; sets keep shared source groups intact.
pub type PremiseSet = BTreeMap<ModuleRef, BTreeSet<String>>;
use tower_lsp::lsp_types::Range;

// The obligation and policy are checked in addition to source identity. Module
// IDs inside values are deliberately compared conservatively for partial reuse.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CachedGoal {
    prove: bool,
    value: AcornValue,
    range: Range,
    full_range: (u32, u32),
    context_end: u32,
    inconsistency_okay: bool,
}

impl CachedGoal {
    pub fn new(goal: &GoalContext) -> Self {
        Self {
            prove: matches!(goal.goal, Goal::Prove(_)),
            value: goal.goal.value().clone(),
            range: goal.goal.range(),
            full_range: (goal.first_line, goal.last_line),
            context_end: goal.cache_last_line,
            inconsistency_okay: goal.inconsistency_okay,
        }
    }

    fn matches(&self, goal: &GoalContext) -> bool {
        self.prove == matches!(goal.goal, Goal::Prove(_))
            && &self.value == goal.goal.value()
            && self.range == goal.goal.range()
            && self.full_range == (goal.first_line, goal.last_line)
            && self.context_end == goal.cache_last_line
            && self.inconsistency_okay == goal.inconsistency_okay
    }
}

// Completed in-process verification metadata. Reuse also checks the current source,
// complete goal ranges and successful transitive dependencies.
#[derive(Debug, Clone)]
pub struct CachedModule {
    hash: ModuleHash,
    direct_dependencies: Vec<ModuleRef>,
    verified: Vec<(u32, u32)>,
    goals: Vec<CachedGoal>,
    theorem_premises: BTreeMap<String, PremiseSet>,
}

impl CachedModule {
    // Learned only in this process. Persistent result records do not contain hints.
    pub fn theorem_premises(&self) -> &BTreeMap<String, PremiseSet> {
        &self.theorem_premises
    }

    pub fn fingerprint(&self) -> ModuleFingerprint {
        self.hash.fingerprint()
    }

    pub fn module_hash(&self) -> &ModuleHash {
        &self.hash
    }

    pub fn direct_dependencies(&self) -> &[ModuleRef] {
        &self.direct_dependencies
    }

    pub fn verified(&self) -> &[(u32, u32)] {
        &self.verified
    }
}

#[derive(Debug, Default, Clone)]
pub struct BuildCache {
    modules: HashMap<ModuleRef, CachedModule>,
}

impl BuildCache {
    pub fn num_modules(&self) -> usize {
        self.modules.len()
    }

    pub fn get(&self, module: &ModuleRef) -> Option<&CachedModule> {
        self.modules.get(module)
    }

    // Only finalized build snapshots are published. Entries for other targets remain valid.
    pub(crate) fn merge_completed(&mut self, completed: &BuildCache) {
        for (module, replacement) in &completed.modules {
            let mut replacement = replacement.clone();
            // Dataset builds do not extract hints. Preserve previously learned
            // memory hints only for exactly the same completed obligations.
            if replacement.theorem_premises.is_empty() {
                if let Some(previous) = self.modules.get(module) {
                    if previous.hash == replacement.hash
                        && previous.goals == replacement.goals
                        && previous.verified == replacement.verified
                    {
                        replacement.theorem_premises = previous.theorem_premises.clone();
                    }
                }
            }
            self.modules.insert(module.clone(), replacement);
        }
    }

    pub(crate) fn matches(
        &self,
        module: &ModuleRef,
        hash: Option<&ModuleHash>,
        expected: &[(u32, u32)],
    ) -> bool {
        self.get(module)
            .is_some_and(|cached| Some(&cached.hash) == hash && cached.verified == expected)
    }

    pub(crate) fn matches_prefix(
        &self,
        module: &ModuleRef,
        hash: &ModuleHash,
        goal: &GoalContext,
        index: usize,
    ) -> bool {
        self.get(module).is_some_and(|cached| {
            cached.goals.len() == cached.verified.len()
                && cached.verified.get(index) == Some(&(goal.first_line, goal.last_line))
                && cached
                    .goals
                    .get(index)
                    .is_some_and(|cached_goal| cached_goal.matches(goal))
                && hash.matches_through_line(&cached.hash, goal.cache_last_line)
        })
    }

    // Called only after Builder verifies every expected goal in the module.
    pub(crate) fn insert_completed(
        &mut self,
        module: ModuleRef,
        hash: ModuleHash,
        direct_dependencies: Vec<ModuleRef>,
        verified: Vec<(u32, u32)>,
        goals: Vec<CachedGoal>,
        theorem_premises: BTreeMap<String, PremiseSet>,
    ) {
        self.modules.insert(
            module,
            CachedModule {
                hash,
                direct_dependencies,
                verified,
                goals,
                theorem_premises,
            },
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::builder::Builder;
    use crate::project::Project;

    #[test]
    fn prefix_lookup_rejects_changed_obligation_or_policy_even_with_same_source() {
        let mut project = Project::new_mock();
        project.mock("/mock/main.ac", "theorem identity { true }\n");
        let cache = project.sync_build_report().cache.unwrap();
        let module = ModuleRef::Name("main".into());
        let env = project.get_env_by_ref(&module).unwrap();
        let mut goal = env.iter_goals().next().unwrap().goal_context().unwrap();
        let hash = project.get_module_hash(env.module_id).unwrap();
        assert!(cache.matches_prefix(&module, hash, &goal, 0));
        goal.inconsistency_okay = !goal.inconsistency_okay;
        assert!(!cache.matches_prefix(&module, hash, &goal, 0));
        goal.inconsistency_okay = !goal.inconsistency_okay;
        let original = goal.goal.clone();
        goal.goal = Goal::Solve(original.value().clone(), original.range());
        assert!(!cache.matches_prefix(&module, hash, &goal, 0));
        goal.goal = original;
        if let Goal::Prove(ref mut proposition) = goal.goal {
            proposition.value = AcornValue::Bool(false);
        }
        assert!(!cache.matches_prefix(&module, hash, &goal, 0));
    }

    #[test]
    fn stale_or_incomplete_goal_ranges_cannot_be_replayed() {
        for ranges in [vec![], vec![(0, 1)], vec![(0, 0), (0, 0)]] {
            let mut original = Project::new_mock();
            original.mock("/mock/main.ac", "theorem identity { true }");
            let mut cache = original.sync_build_report().cache.unwrap();
            cache
                .modules
                .get_mut(&ModuleRef::Name("main".into()))
                .unwrap()
                .verified = ranges;
            let mut project = Project::new_mock();
            project.mock("/mock/main.ac", "theorem identity { true }");
            let mut builder = Builder::with_cache(cache, |_| {});
            project.build(&mut builder);
            assert_eq!((builder.num_success, builder.num_cached), (1, 0));
        }
    }
}
