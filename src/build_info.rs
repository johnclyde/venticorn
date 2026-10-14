// Modified for Venticorn: publication state belongs to a specific build generation.
use std::collections::HashMap;
use tower_lsp::lsp_types::{Diagnostic, Url};

use crate::builder::BuildEvent;
use crate::interfaces::{DocumentProgress, ProgressResponse};

#[derive(Debug, PartialEq)]
pub struct DiagnosticUpdate {
    pub url: Url,
    pub diagnostics: Vec<Diagnostic>,
    pub version: Option<i32>,
}

#[derive(Default)]
struct DocumentBuildInfo {
    version: Option<i32>,
    publish: bool,
    verified: Vec<u32>,
    diagnostics: Vec<Diagnostic>,
}

#[derive(Default)]
pub struct BuildInfo {
    generation: u64,
    id: Option<u32>,
    done: i32,
    total: i32,
    docs: HashMap<Url, DocumentBuildInfo>,
    live_versions: HashMap<Url, i32>,
}

impl BuildInfo {
    pub fn generation(&self) -> u64 {
        self.generation
    }

    // Call under the publication lock before a document transition can wait on
    // project locks. An older consumer can never claim this generation later.
    pub fn invalidate(&mut self, live_versions: HashMap<Url, i32>) -> Vec<DiagnosticUpdate> {
        self.generation = self
            .generation
            .checked_add(1)
            .expect("build generation exhausted");
        self.id = None;
        self.done = 0;
        self.total = 0;
        let mut urls: Vec<_> = self
            .docs
            .keys()
            .chain(live_versions.keys())
            .cloned()
            .collect();
        urls.sort();
        urls.dedup();
        let updates = urls
            .into_iter()
            .map(|url| DiagnosticUpdate {
                version: live_versions.get(&url).copied(),
                url,
                diagnostics: Vec::new(),
            })
            .collect();
        self.docs.clear();
        self.live_versions = live_versions;
        updates
    }

    pub fn reset(
        &mut self,
        project_versions: impl IntoIterator<Item = (Url, i32)>,
        live_versions: HashMap<Url, i32>,
    ) -> Vec<DiagnosticUpdate> {
        let updates = self.invalidate(live_versions);
        for (url, version) in project_versions {
            let publish = self.live_versions.get(&url) == Some(&version);
            self.docs.insert(
                url,
                DocumentBuildInfo {
                    version: Some(version),
                    publish,
                    ..Default::default()
                },
            );
        }
        updates
    }

    pub fn accepts(&self, generation: u64, build_id: u32) -> bool {
        generation == self.generation
            && build_id != 0
            && (self.id.is_none() || self.id == Some(build_id))
    }

    pub fn handle_event(
        &mut self,
        generation: u64,
        url: Option<Url>,
        event: &BuildEvent,
    ) -> Option<DiagnosticUpdate> {
        if !self.accepts(generation, event.build_id) {
            return None;
        }
        self.id = Some(event.build_id);
        if let Some((done, total)) = event.progress {
            self.done = done;
            self.total = total;
        }
        let url = url?;
        let live = self.live_versions.contains_key(&url);
        let doc = self
            .docs
            .entry(url.clone())
            .or_insert_with(|| DocumentBuildInfo {
                // Imported disk-only modules have no editor version. An open file
                // missing from the project snapshot must not be treated as disk-only.
                publish: !live,
                ..Default::default()
            });
        if !doc.publish {
            return None;
        }
        if let Some((first, _)) = &event.verified {
            if !doc.verified.contains(first) {
                doc.verified.push(*first);
            }
        }
        if let Some(diagnostic) = &event.diagnostic {
            doc.diagnostics.push(diagnostic.clone());
            return Some(DiagnosticUpdate {
                url,
                version: doc.version,
                diagnostics: doc.diagnostics.clone(),
            });
        }
        None
    }

    pub fn progress(&self) -> ProgressResponse {
        ProgressResponse {
            build_id: self.id,
            done: self.done,
            total: self.total,
            docs: self
                .docs
                .iter()
                .filter(|(_, doc)| doc.publish)
                .filter_map(|(url, doc)| {
                    doc.version.map(|version| {
                        (
                            url.clone(),
                            DocumentProgress {
                                version,
                                verified: if doc.diagnostics.iter().any(|diagnostic| {
                                    diagnostic.severity
                                        != Some(
                                            tower_lsp::lsp_types::DiagnosticSeverity::INFORMATION,
                                        )
                                        && diagnostic.severity
                                            != Some(tower_lsp::lsp_types::DiagnosticSeverity::HINT)
                                }) {
                                    Vec::new()
                                } else {
                                    doc.verified.clone()
                                },
                            },
                        )
                    })
                })
                .collect(),
        }
    }
}

#[cfg(test)]
mod tests {
    // Modified for Venticorn: adversarial build publication ordering.
    use super::BuildInfo;
    use crate::builder::BuildEvent;
    use crate::module::ModuleRef;
    use std::collections::HashMap;
    use tower_lsp::lsp_types::{Diagnostic, Range, Url};

    fn url() -> Url {
        Url::parse("file:///proof.ac").unwrap()
    }
    fn versions(version: i32) -> HashMap<Url, i32> {
        HashMap::from([(url(), version)])
    }
    fn event(id: u32) -> BuildEvent {
        BuildEvent {
            build_id: id,
            module: ModuleRef::Anonymous,
            progress: Some((1, 1)),
            log_message: None,
            verified: Some((4, 4)),
            diagnostic: Some(Diagnostic {
                severity: Some(tower_lsp::lsp_types::DiagnosticSeverity::INFORMATION),
                ..Diagnostic::new_simple(Range::default(), "timing".to_string())
            }),
        }
    }

    #[test]
    fn stale_generation_cannot_claim_a_new_build_or_publish_after_same_version_reopen() {
        let mut info = BuildInfo::default();
        info.reset(versions(7), versions(7));
        let old = info.generation();
        assert_eq!(
            info.handle_event(old, Some(url()), &event(1))
                .unwrap()
                .version,
            Some(7)
        );
        let closed = info.invalidate(HashMap::new());
        assert_eq!(closed.len(), 1);
        assert_eq!(closed[0].version, None);
        assert!(closed[0].diagnostics.is_empty());
        info.reset(versions(7), versions(7));
        let reopened = info.generation();
        assert_ne!(old, reopened);
        assert!(info.handle_event(old, Some(url()), &event(1)).is_none());
        assert_eq!(info.progress().build_id, None);
        assert!(info.progress().docs[&url()].verified.is_empty());
        info.handle_event(reopened, Some(url()), &event(2));
        assert!(info.handle_event(old, Some(url()), &event(1)).is_none());
        assert!(info
            .handle_event(reopened, Some(url()), &event(1))
            .is_none());
        assert_eq!(info.progress().build_id, Some(2));
        assert_eq!(info.progress().docs[&url()].verified, vec![4]);
    }

    #[test]
    fn edited_documents_suppress_old_snapshot_results_and_clear_with_the_current_version() {
        let mut info = BuildInfo::default();
        info.reset(versions(3), versions(3));
        let before_edit = info.generation();
        info.handle_event(before_edit, Some(url()), &event(1));
        let cleared = info.invalidate(versions(4));
        assert_eq!(cleared[0].version, Some(4));
        assert!(cleared[0].diagnostics.is_empty());
        info.reset(versions(3), versions(4));
        assert!(info
            .handle_event(info.generation(), Some(url()), &event(2))
            .is_none());
        assert!(!info.progress().docs.contains_key(&url()));
        info.reset(versions(4), versions(4));
        let published = info
            .handle_event(info.generation(), Some(url()), &event(3))
            .unwrap();
        assert_eq!(published.version, Some(4));
    }

    #[test]
    fn disk_modules_have_unversioned_diagnostics_and_no_editor_verification_lines() {
        let mut info = BuildInfo::default();
        info.reset([], HashMap::new());
        let published = info
            .handle_event(info.generation(), Some(url()), &event(1))
            .unwrap();
        assert_eq!(published.version, None);
        assert!(info.progress().docs.is_empty());
    }

    #[test]
    fn a_zero_goal_build_clears_previous_progress_and_duplicate_ranges_are_collapsed() {
        let mut info = BuildInfo::default();
        info.reset(versions(1), versions(1));
        let generation = info.generation();
        info.handle_event(generation, Some(url()), &event(1));
        info.handle_event(generation, Some(url()), &event(1));
        assert_eq!(info.progress().docs[&url()].verified, vec![4]);
        info.reset(versions(2), versions(2));
        let mut empty = event(2);
        empty.progress = Some((0, 0));
        empty.verified = None;
        empty.diagnostic = None;
        info.handle_event(info.generation(), None, &empty);
        assert_eq!(info.progress().build_id, Some(2));
        assert_eq!(info.progress().done, 0);
        assert_eq!(info.progress().total, 0);
        assert!(info.progress().docs[&url()].verified.is_empty());
    }
}
