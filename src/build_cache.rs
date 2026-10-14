// Modified for Venticorn: completed verification metadata with a read-only public API.
use crate::module::{ModuleHash, ModuleRef};
use crate::project::ModuleFingerprint;
use std::collections::HashMap;

// Completed in-process verification metadata. Reuse also checks the current source,
// complete goal ranges and successful transitive dependencies.
#[derive(Debug, Clone)]
pub struct CachedModule {
    hash: ModuleHash,
    direct_dependencies: Vec<ModuleRef>,
    verified: Vec<(u32, u32)>,
}

impl CachedModule {
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
        self.modules.extend(completed.modules.clone());
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

    // Called only after Builder verifies every expected goal in the module.
    pub(crate) fn insert_completed(
        &mut self,
        module: ModuleRef,
        hash: ModuleHash,
        direct_dependencies: Vec<ModuleRef>,
        verified: Vec<(u32, u32)>,
    ) {
        self.modules.insert(
            module,
            CachedModule {
                hash,
                direct_dependencies,
                verified,
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
