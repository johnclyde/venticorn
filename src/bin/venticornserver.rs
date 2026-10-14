// Modified for Venticorn.
// The Venticorn language server, normally started by the editor extension.
use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::atomic::AtomicBool;
use std::sync::Arc;

use chrono;
use clap::Parser;
use dashmap::DashMap;
use tokio::sync::{mpsc, Mutex, RwLock, RwLockWriteGuard};
use tower_lsp::jsonrpc;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};
use venticorn::block::NodeCursor;
use venticorn::build_info::BuildInfo;
use venticorn::interfaces::{
    InfoParams, InfoResponse, ProgressParams, ProgressResponse, SearchParams, SearchResponse,
    SearchStatus,
};
use venticorn::live_document::LiveDocument;
use venticorn::module::{Module, ModuleRef};
use venticorn::project::Project;
use venticorn::prover::{Outcome, Prover};
use venticorn::token::Token;

#[derive(Clone, Parser)]
#[command(about = "Venticorn language server")]
struct Args {
    /// Workspace directory used for local library discovery.
    #[arg(long)]
    workspace_root: Option<PathBuf>,

    /// Installed extension directory containing the bundled acornlib library.
    #[arg(long)]
    extension_root: Option<PathBuf>,
}

// Keep selection independent of the server process working directory.
fn select_library(args: &Args, workspace_uri: Option<&Url>) -> jsonrpc::Result<PathBuf> {
    if let Some(root) = Project::library_override()
        .map_err(|error| jsonrpc::Error::invalid_params(error.to_string()))?
    {
        return Ok(root);
    }
    let workspace_root = match &args.workspace_root {
        Some(path) => Some(path.clone()),
        None => workspace_uri
            .map(|uri| {
                uri.to_file_path().map_err(|_| {
                    jsonrpc::Error::invalid_params(format!(
                        "workspace root is not a local file URI: {}",
                        uri
                    ))
                })
            })
            .transpose()?,
    };
    if let Some(path) = &workspace_root {
        if let Some(root) = Project::find_local_library(path)
            .map_err(|error| jsonrpc::Error::invalid_params(error.to_string()))?
        {
            return Ok(root);
        }
    }
    if let Some(extension_root) = &args.extension_root {
        if !extension_root.is_dir() {
            return Err(jsonrpc::Error::invalid_params(format!(
                "extension root is not a directory: {}",
                extension_root.display()
            )));
        }
        let bundled = extension_root.join("acornlib");
        if !bundled.is_dir() {
            return Err(jsonrpc::Error::invalid_params(format!(
                "bundled library is not a directory: {}",
                bundled.display()
            )));
        }
        return bundled
            .canonicalize()
            .map_err(|error| jsonrpc::Error::invalid_params(error.to_string()));
    }
    Err(jsonrpc::Error::invalid_params(match workspace_root {
        Some(path) => format!(
            "no library found from {}; set VENTICORN_LIBRARY to its directory",
            path.display()
        ),
        None => "open a workspace folder or set VENTICORN_LIBRARY to its directory".to_string(),
    }))
}

// Messages appear in the "Venticorn Language Server" output channel.
fn log(message: &str) {
    let timestamp = chrono::Local::now().format("%H:%M:%S%.3f");
    let stamped = format!("[{}] {}", timestamp, message);
    eprintln!("{}", stamped);
}

fn log_with_doc(url: &Url, version: i32, message: &str) {
    let filename = url
        .path_segments()
        .and_then(|parts| parts.last())
        .unwrap_or(url.as_str());
    log(&format!("{} v{}: {}", filename, version, message));
}

// A search task is a long-running task that searches for a proof.
// The language server can work on one search task at a time.
// The SearchTask tracks information around that request.
// It is clonable so that it can be used both by the thread doing the task, and
// threads handling requests.
// The thread doing the search updates the task with its information, while threads handling
// concurrent user requests can read it.
#[derive(Clone)]
struct SearchTask {
    project: Arc<RwLock<Project>>,
    url: Url,
    version: i32,

    // While we are proving, most of the time the thread running the 'run' method
    // will hold a write lock on the prover.
    // The task will release and reacquire the lock intermittently, and the RwLock is fair so other
    // threads get a chance to use the prover.
    prover: Arc<RwLock<Prover>>,

    // The module that we're searching for a proof in
    module_ref: ModuleRef,

    // The line in the document the user selected to kick off this task.
    selected_line: u32,

    // The path to the goal
    path: Vec<usize>,

    // A displayable name for the goal
    goal_name: String,

    // The range of the goal in the document
    goal_range: Range,

    // The Status is periodically updated by the task.
    // It can indicate either partial progress or completion.
    status: Arc<RwLock<SearchStatus>>,

    // Set this flag to true when a subsequent search task has been created
    superseded: Arc<AtomicBool>,

    // Zero-based line where we would insert a proof for this goal
    proof_insertion_line: u32,

    // Whether we need to also insert a block, if we do insert a proof.
    insert_block: bool,

    // The search id set by the extenson for the original search that created this task.
    // The extension may send new searches with essentially the same parameters, that we
    // discard. This is inevitable because the extension doesn't have enough information to
    // disambiguoute searches. Only the language server does.
    // Thus, when we get redundant searches, we keep using the original id downstream.
    id: i32,
}

impl SearchTask {
    // Makes a response based on the current state of the task
    async fn response(&self) -> SearchResponse {
        let status = self.status.read().await.clone();
        SearchResponse {
            uri: self.url.clone(),
            version: self.version,
            failure: None,
            loading: false,
            goal_name: Some(self.goal_name.clone()),
            goal_range: Some(self.goal_range.clone()),
            status,
            proof_insertion_line: self.proof_insertion_line,
            insert_block: self.insert_block,
            id: self.id,
        }
    }

    // Runs the search task.
    async fn run(&self) {
        // This holds a read lock on the project the whole time.
        // It seems like we should be able to avoid this, but maybe it's just fine.
        let project = self.project.read().await;
        let env = match project.get_env_by_ref(&self.module_ref) {
            Some(env) => env,
            None => {
                log(&format!("no environment for {:?}", self.module_ref));
                return;
            }
        };

        log(&format!("running search task for {}", self.goal_name));

        loop {
            // Each iteration through the loop reacquires the write lock on the prover.
            // This lets other threads access the prover in between iterations.
            let mut prover = self.prover.write().await;
            let outcome = prover.partial_search();
            let status = match outcome {
                Outcome::Success => {
                    let proof = prover.get_proof().unwrap();
                    let steps = prover.to_proof_info(&project, &env.bindings, &proof);

                    let (code, error) = match proof.to_code(&env.bindings) {
                        Ok(code) => (Some(code), None),
                        Err(e) => (None, Some(e.to_string())),
                    };

                    SearchStatus::success(code, error, steps, proof.needs_simplification(), &prover)
                }

                Outcome::Inconsistent
                | Outcome::Exhausted
                | Outcome::Constrained
                | Outcome::Error => SearchStatus::stopped(&prover, outcome),

                Outcome::Timeout => SearchStatus::pending(&prover),

                Outcome::Interrupted => {
                    // No point in providing a result for this task, since nobody is listening.
                    log(&format!("goal {} interrupted", self.goal_name));
                    return;
                }
            };

            // Update the status
            let mut locked_status = self.status.write().await;
            *locked_status = status;

            if outcome != Outcome::Timeout {
                // We're done
                log(&format!("search task for {} completed", self.goal_name));
                break;
            }
        }
    }
}

// One backend per selected library.
// Handles one initialized project; connection initialization belongs to LazyBackend.
struct Backend {
    client: Client,

    // The project we're working on
    project: Arc<RwLock<Project>>,

    // Publication state is guarded independently of document lifecycle work.
    build: Arc<RwLock<BuildInfo>>,

    // Maps each URI to the most recently saved document text.
    documents: DashMap<Url, Arc<RwLock<LiveDocument>>>,

    // Serialize lifecycle transitions and request setup, never long-running proof work.
    lifecycle: Mutex<()>,

    // The current search task, if any
    search_task: Arc<RwLock<Option<SearchTask>>>,
}

impl Backend {
    fn new(client: Client, project: Project) -> Backend {
        Backend {
            project: Arc::new(RwLock::new(project)),
            client,
            build: Arc::new(RwLock::new(BuildInfo::default())),
            documents: DashMap::new(),
            lifecycle: Mutex::new(()),
            search_task: Arc::new(RwLock::new(None)),
        }
    }

    // Snapshot Arcs before awaiting document locks: never retain DashMap guards.
    async fn live_versions(&self) -> HashMap<Url, i32> {
        let documents: Vec<_> = self
            .documents
            .iter()
            .map(|entry| (entry.key().clone(), Arc::clone(entry.value())))
            .collect();
        let mut versions = HashMap::new();
        for (url, document) in documents {
            versions.insert(url, document.read().await.live_version());
        }
        versions
    }

    // Called while holding lifecycle, after the document change and before any
    // project wait. Publication holds only BuildInfo, never lifecycle/documents.
    async fn invalidate_build(&self) {
        let versions = self.live_versions().await;
        {
            let mut build = self.build.write().await;
            for update in build.invalidate(versions) {
                self.client
                    .publish_diagnostics(update.url, update.diagnostics, update.version)
                    .await;
            }
        }
        // Release BuildInfo before obtaining project: event consumers hold a
        // project read snapshot while waiting for the publication lock.
        self.project.read().await.stop_build();
    }

    async fn spawn_build(&self) {
        let start_time = chrono::Local::now();
        let versions = self.live_versions().await;
        // Producer and consumer share exactly one immutable project snapshot.
        let project = Arc::new(self.project.clone().read_owned().await);
        let generation;
        {
            let mut build = self.build.write().await;
            for update in build.reset(project.open_urls(), versions) {
                self.client
                    .publish_diagnostics(update.url, update.diagnostics, update.version)
                    .await;
            }
            generation = build.generation();
        }
        let (tx, mut rx) = mpsc::unbounded_channel();
        let producer_project = project.clone();
        tokio::spawn(async move {
            tokio::task::block_in_place(move || {
                let mut builder = producer_project.builder(move |event| {
                    // A superseded consumer may already have stopped listening.
                    let _ = tx.send(event);
                });
                producer_project.build(&mut builder);
                let seconds =
                    (chrono::Local::now() - start_time).num_milliseconds() as f64 / 1000.0;
                log(&format!(
                    "verification {} after {:.2}s",
                    builder.status.verb(),
                    seconds
                ));
            });
        });
        let state = self.build.clone();
        let client = self.client.clone();
        tokio::spawn(async move {
            let mut build_id = None;
            while let Some(event) = rx.recv().await {
                let mut build = state.write().await;
                if !build.accepts(generation, event.build_id) {
                    break;
                }
                build_id = Some(event.build_id);
                if let Some(message) = &event.log_message {
                    log(message);
                }
                let url = project.url_from_module_ref(&event.module);
                if let Some(update) = build.handle_event(generation, url, &event) {
                    // Keep the guard through the send so a replacement cannot
                    // begin and then receive a notification from this build.
                    client
                        .publish_diagnostics(update.url, update.diagnostics, update.version)
                        .await;
                }
            }
            if let Some(build_id) = build_id {
                state.write().await.finish(generation, build_id);
            }
        });
    }

    // A lifecycle lock keeps document, project, and search identity changes ordered.
    async fn set_full_text(&self, url: Url, text: String, version: Option<i32>) {
        let _lifecycle = self.lifecycle.lock().await;
        let path = url.to_file_path().ok();
        if path.is_none() && (url.scheme() != "untitled" || version.is_none()) {
            log(&format!(
                "document update ignored for non-file URI: {}",
                url
            ));
            return;
        }
        let version = match version {
            Some(version) => {
                if self.documents.contains_key(&url) {
                    log(&format!("duplicate open ignored for {}", url));
                    return;
                }
                let doc = LiveDocument::new(&text, version);
                self.documents
                    .insert(url.clone(), Arc::new(RwLock::new(doc)));
                version
            }
            None => {
                let doc = match self.documents.get(&url) {
                    Some(doc) => Arc::clone(doc.value()),
                    None => {
                        log(&format!("save ignored for closed document: {}", url));
                        return;
                    }
                };
                let mut doc = doc.write().await;
                if doc.live_version() == doc.saved_version() {
                    if doc.text() != text {
                        log(&format!(
                            "save ignored without a corresponding change: {}",
                            url
                        ));
                    }
                    return;
                }
                match doc.save(&text) {
                    Ok(version) => version,
                    Err(error) => {
                        log(&format!("save ignored for {}: {}", url, error));
                        return;
                    }
                }
            }
        };
        let path = match path {
            Some(path) => path,
            None => return, // Untitled text has editor services, but no project or proof identity.
        };
        self.invalidate_build().await;
        self.set_search_task(None).await;
        let mut project = self.stop_build_and_get_project().await;
        log_with_doc(&url, version, "updating saved text");
        match project.update_file(path, &text, version) {
            Ok(()) => {}
            Err(error) => log(&format!("update failed: {:?}", error)),
        }
        drop(project);
        self.spawn_build().await;
    }

    // If there is a build happening, stops it.
    // Acquires the write lock on the project.
    // Returns a writable reference to the project.
    async fn stop_build_and_get_project(&self) -> RwLockWriteGuard<Project> {
        {
            let project = self.project.read().await;
            project.stop_build();
        }
        // Reallow the build once we acquire the write lock
        let mut project = self.project.write().await;
        project.allow_build();
        project
    }

    fn search_fail(&self, params: SearchParams, message: &str) -> jsonrpc::Result<SearchResponse> {
        log(message);
        Ok(SearchResponse {
            failure: Some(message.to_string()),
            ..SearchResponse::new(params)
        })
    }

    async fn handle_progress_request(
        &self,
        _params: ProgressParams,
    ) -> jsonrpc::Result<ProgressResponse> {
        let _lifecycle = self.lifecycle.lock().await;
        Ok(self.build.read().await.progress())
    }

    // Cancels any current search task.
    // Runs the new task, if it is not None.
    async fn set_search_task(&self, new_task: Option<SearchTask>) {
        // Replace the locked singleton task
        {
            let mut locked_task = self.search_task.write().await;
            if let Some(old_task) = locked_task.as_ref() {
                // Cancel the old task
                old_task
                    .superseded
                    .store(true, std::sync::atomic::Ordering::Relaxed);
            }
            *locked_task = new_task.clone();
        }

        if let Some(new_task) = new_task {
            tokio::spawn(async move {
                new_task.run().await;
            });
        }
    }

    async fn handle_search_request(&self, params: SearchParams) -> jsonrpc::Result<SearchResponse> {
        let _lifecycle = self.lifecycle.lock().await;
        if params.uri.scheme() != "file" {
            return self.search_fail(
                params,
                "save the document to a file before searching for a proof",
            );
        }
        let doc = match self.documents.get(&params.uri) {
            Some(doc) => Arc::clone(doc.value()),
            None => return self.search_fail(params, "no text available"),
        };
        let doc = doc.read().await;
        if params.version != doc.live_version() {
            return self.search_fail(params, "requested document version is not current");
        }
        if params.version != doc.saved_version() {
            return Ok(SearchResponse {
                loading: true,
                ..SearchResponse::new(params)
            });
        }
        let version = doc.saved_version();
        drop(doc);

        // Check if this request matches our current task, based on the selected line.
        // This is less general than checking the full path, but we don't have the
        // full path until we acquire a lock on the project.
        if let Some(current_task) = self.search_task.read().await.as_ref() {
            if current_task.url == params.uri
                && current_task.version == params.version
                && current_task.selected_line == params.selected_line
            {
                return Ok(current_task.response().await);
            }
        }

        let project = self.project.read().await;
        let path = match params.uri.to_file_path() {
            Ok(path) => path,
            Err(_) => {
                // There should be a path available, because we don't run this task without one.
                return self.search_fail(params, "no path available in SearchTask::run");
            }
        };
        match project.get_version(&path) {
            Some(project_version) => {
                if params.version < project_version {
                    let message = &format!(
                        "user requested version {} but the project has version {}",
                        params.version, project_version
                    );
                    return self.search_fail(params, message);
                }
                if params.version > project_version {
                    // The requested version is not loaded yet.
                    return Ok(SearchResponse {
                        loading: true,
                        ..SearchResponse::new(params)
                    });
                }
            }
            None => {
                return self.search_fail(
                    params,
                    &format!("the project has not opened {}", path.display()),
                );
            }
        }
        let module_ref = match project.module_ref_from_path(&path) {
            Ok(name) => name,
            Err(e) => {
                return self.search_fail(params, &format!("module_ref_from_path failed: {:?}", e))
            }
        };
        let env = match project.get_module_by_ref(&module_ref) {
            Module::Ok(env) => env,
            _ => {
                return self.search_fail(
                    params,
                    &format!("could not load module from {:?}", module_ref),
                );
            }
        };

        let path = match env.path_for_line(params.selected_line) {
            Ok(path) => path,
            Err(s) => return self.search_fail(params, &s),
        };

        // Check if this request matches our current task, based on the full path of the goal.
        // This is slower (because we had to acquire the project lock first)
        // but catches more situations than just checking the selected line.
        if let Some(current_task) = self.search_task.read().await.as_ref() {
            if current_task.url == params.uri
                && current_task.version == params.version
                && current_task.path == path
            {
                return Ok(current_task.response().await);
            }
        }
        let node = NodeCursor::from_path(env, &path);
        let goal_context = match node.goal_context() {
            Ok(goal_context) => goal_context,
            Err(s) => return self.search_fail(params, &s),
        };
        let superseded = Arc::new(AtomicBool::new(false));
        let mut prover = Prover::new(&project, false);
        for fact in node.usable_facts(&project) {
            prover.add_fact(fact);
        }
        prover.set_goal(&goal_context);
        prover.stop_flags.push(superseded.clone());
        let status = SearchStatus::pending(&prover);

        // Create a new search task
        let new_task = SearchTask {
            project: self.project.clone(),
            url: params.uri.clone(),
            version,
            prover: Arc::new(RwLock::new(prover)),
            module_ref,
            selected_line: params.selected_line,
            path,
            goal_name: goal_context.name.clone(),
            goal_range: goal_context.goal.range(),
            status: Arc::new(RwLock::new(status)),
            superseded,
            proof_insertion_line: goal_context.proof_insertion_line,
            insert_block: goal_context.insert_block,
            id: params.id,
        };

        // A minimal response before any data has been collected
        let mut response = new_task.response().await;
        response.loading = true;

        self.set_search_task(Some(new_task)).await;

        Ok(response)
    }

    fn info_fail(&self, params: InfoParams, message: &str) -> jsonrpc::Result<InfoResponse> {
        log(message);
        Ok(InfoResponse {
            search_id: params.search_id,
            failure: Some(message.to_string()),
            result: None,
        })
    }

    async fn handle_info_request(&self, params: InfoParams) -> jsonrpc::Result<InfoResponse> {
        let _lifecycle = self.lifecycle.lock().await;
        let locked_task = self.search_task.read().await;

        let task = match locked_task.as_ref() {
            Some(task) => task,
            None => return self.info_fail(params, "no search task available"),
        };
        if task.id != params.search_id {
            let failure = format!(
                "info request has search id {}, task has id {}",
                params.search_id, task.id
            );
            return self.info_fail(params, &failure);
        }
        let project = self.project.read().await;
        let prover = task.prover.read().await;
        let env = match project.get_env_by_ref(&task.module_ref) {
            Some(env) => env,
            None => {
                return self.info_fail(params, "no environment available");
            }
        };
        let result = prover.info_result(&project, &env.bindings, params.clause_id);
        let failure = match result {
            Some(_) => None,
            None => Some(format!("no info available for clause {}", params.clause_id)),
        };
        Ok(InfoResponse {
            search_id: params.search_id,
            failure,
            result,
        })
    }

    async fn did_save(&self, params: DidSaveTextDocumentParams) {
        let uri = params.text_document.uri;
        let text = match params.text {
            Some(text) => text,
            None => {
                log("no text available in did_save");
                return;
            }
        };
        self.set_full_text(uri, text, None).await;
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        let uri = params.text_document.uri;
        let text = params.text_document.text;
        let version = params.text_document.version;
        self.set_full_text(uri, text, Some(version)).await;
    }

    // Edits invalidate proof searches, but a save is required to rebuild the project.
    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        let _lifecycle = self.lifecycle.lock().await;
        let url = params.text_document.uri;
        let doc = match self.documents.get(&url) {
            Some(doc) => Arc::clone(doc.value()),
            None => return,
        };
        let result = doc
            .write()
            .await
            .apply_changes(&params.content_changes, params.text_document.version);
        match result {
            Ok(()) if url.scheme() == "file" => {
                self.invalidate_build().await;
                self.set_search_task(None).await;
                // Retire canceled readers before giving new searches a fresh stop token.
                drop(self.stop_build_and_get_project().await);
            }
            Ok(()) => {}
            Err(error) => log(&format!("change ignored for {}: {}", url, error)),
        }
    }

    async fn did_close(&self, params: DidCloseTextDocumentParams) {
        let _lifecycle = self.lifecycle.lock().await;
        let uri = params.text_document.uri;
        if self.documents.remove(&uri).is_none() {
            return;
        }
        let path = match uri.to_file_path() {
            Ok(path) => path,
            Err(_) => return,
        };
        self.invalidate_build().await;
        self.set_search_task(None).await;
        let mut project = self.stop_build_and_get_project().await;
        match project.close_file(path) {
            Ok(()) => {}
            Err(error) => log(&format!("close failed: {:?}", error)),
        }
        drop(project);
        self.spawn_build().await;
    }

    async fn shutdown(&self) -> jsonrpc::Result<()> {
        log("shutdown");
        Ok(())
    }

    async fn completion(
        &self,
        params: CompletionParams,
    ) -> jsonrpc::Result<Option<CompletionResponse>> {
        let _lifecycle = self.lifecycle.lock().await;
        let uri = params.text_document_position.text_document.uri;
        let position = params.text_document_position.position;
        let path = uri.to_file_path().ok();
        let document = match self.documents.get(&uri) {
            Some(document) => document.value().clone(),
            None => return Ok(None),
        };
        // Release the document guard before waiting on the project lock.
        let (prefix, env_line) = {
            let document = document.read().await;
            let prefix = match document.get_prefix(position.line, position.character) {
                Some(prefix) => prefix,
                None => return Ok(None),
            };
            let env_line = document.get_env_line(position.line).or_else(|| {
                // Imports need the target module, but do not require a local proof scope.
                (prefix.split_whitespace().next() == Some("from")).then_some(0)
            });
            (prefix, env_line)
        };
        let env_line = match env_line {
            Some(line) => line,
            None => return Ok(None),
        };
        let project = self.project.read().await;
        Ok(project
            .get_completions(path.as_deref(), env_line, &prefix)
            .map(|items| {
                CompletionResponse::List(CompletionList {
                    is_incomplete: false,
                    items,
                })
            }))
    }

    async fn semantic_tokens_full(
        &self,
        params: SemanticTokensParams,
    ) -> jsonrpc::Result<Option<SemanticTokensResult>> {
        let uri = params.text_document.uri;
        let _lifecycle = self.lifecycle.lock().await;
        let doc = match self.documents.get(&uri) {
            Some(doc) => Arc::clone(doc.value()),
            None => return Ok(None),
        };
        let doc = doc.read().await;
        log_with_doc(&uri, doc.saved_version(), "semantic_tokens_full");
        let tokens = Token::scan(doc.text());

        // Convert tokens to LSP semantic tokens
        let mut semantic_tokens: Vec<SemanticToken> = vec![];
        let mut prev_line = 0;
        let mut prev_start = 0;
        for token in tokens {
            let line = token.line_number as u32;
            // The scanner reports byte offsets; LSP positions count UTF-16 code units.
            let start = token.line[..token.start as usize].encode_utf16().count() as u32;
            let length = token.text().encode_utf16().count() as u32;
            let token_type = match token.lsp_type_u32() {
                Some(t) => t,
                None => continue,
            };
            let token_modifiers_bitset = 0;
            let delta_line = line - prev_line;
            let delta_start = if delta_line == 0 {
                start - prev_start
            } else {
                start
            };
            semantic_tokens.push(SemanticToken {
                delta_line,
                delta_start,
                length,
                token_type,
                token_modifiers_bitset,
            });
            prev_line = line;
            prev_start = start;
        }

        let result = SemanticTokensResult::Tokens(SemanticTokens {
            result_id: None,
            data: semantic_tokens,
        });
        Ok(Some(result))
    }
}

// Connection state can be prepared before the client selects its workspace.
struct LazyBackend {
    client: Client,
    args: Args,
    backend: tokio::sync::OnceCell<Backend>,
}

impl LazyBackend {
    fn new(client: Client, args: Args) -> Self {
        Self {
            client,
            args,
            backend: tokio::sync::OnceCell::new(),
        }
    }

    fn initialized_backend(&self) -> jsonrpc::Result<&Backend> {
        self.backend.get().ok_or_else(|| jsonrpc::Error {
            code: jsonrpc::ErrorCode::ServerError(-32002),
            message: "Server not initialized".into(),
            data: None,
        })
    }

    async fn handle_info_request(&self, params: InfoParams) -> jsonrpc::Result<InfoResponse> {
        self.initialized_backend()?
            .handle_info_request(params)
            .await
    }

    async fn handle_progress_request(
        &self,
        params: ProgressParams,
    ) -> jsonrpc::Result<ProgressResponse> {
        self.initialized_backend()?
            .handle_progress_request(params)
            .await
    }

    async fn handle_search_request(&self, params: SearchParams) -> jsonrpc::Result<SearchResponse> {
        self.initialized_backend()?
            .handle_search_request(params)
            .await
    }
}

#[tower_lsp::async_trait]
impl LanguageServer for LazyBackend {
    async fn initialize(&self, params: InitializeParams) -> jsonrpc::Result<InitializeResult> {
        let root_uri = params
            .workspace_folders
            .as_ref()
            .and_then(|folders| folders.first())
            .map(|folder| &folder.uri)
            .or(params.root_uri.as_ref());
        self.backend
            .get_or_try_init(|| async {
                let library_root = select_library(&self.args, root_uri)?;
                log(&format!("using library at {}", library_root.display()));
                let project = Project::from_library_root(library_root)
                    .map_err(|error| jsonrpc::Error::invalid_params(error.to_string()))?;
                Ok::<_, jsonrpc::Error>(Backend::new(self.client.clone(), project))
            })
            .await?;
        if let Some(path) = &self.args.workspace_root {
            log(&format!(
                "initializing with workspace path {}",
                path.display()
            ));
        } else {
            match root_uri {
                Some(root) => log(&format!("initializing with root {}", root)),
                None => log("initializing with no root"),
            }
        }

        let sync_options = TextDocumentSyncCapability::Options(TextDocumentSyncOptions {
            open_close: Some(true),
            change: Some(TextDocumentSyncKind::INCREMENTAL),
            save: Some(TextDocumentSyncSaveOptions::SaveOptions(SaveOptions {
                include_text: Some(true),
            })),
            ..TextDocumentSyncOptions::default()
        });

        log("initialization ok");
        Ok(InitializeResult {
            server_info: None,
            capabilities: ServerCapabilities {
                text_document_sync: Some(sync_options),
                completion_provider: Some(CompletionOptions {
                    trigger_characters: Some(vec![".".to_string()]),
                    ..CompletionOptions::default()
                }),
                ..ServerCapabilities::default()
            },
        })
    }

    async fn did_save(&self, params: DidSaveTextDocumentParams) {
        if let Some(backend) = self.backend.get() {
            backend.did_save(params).await;
        }
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        if let Some(backend) = self.backend.get() {
            backend.did_open(params).await;
        }
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        if let Some(backend) = self.backend.get() {
            backend.did_change(params).await;
        }
    }

    async fn did_close(&self, params: DidCloseTextDocumentParams) {
        if let Some(backend) = self.backend.get() {
            backend.did_close(params).await;
        }
    }

    async fn shutdown(&self) -> jsonrpc::Result<()> {
        match self.backend.get() {
            Some(backend) => backend.shutdown().await,
            None => Ok(()),
        }
    }

    async fn completion(
        &self,
        params: CompletionParams,
    ) -> jsonrpc::Result<Option<CompletionResponse>> {
        self.initialized_backend()?.completion(params).await
    }

    async fn semantic_tokens_full(
        &self,
        params: SemanticTokensParams,
    ) -> jsonrpc::Result<Option<SemanticTokensResult>> {
        match self.backend.get() {
            Some(backend) => backend.semantic_tokens_full(params).await,
            None => Ok(None),
        }
    }
}

#[tokio::main]
async fn main() -> std::process::ExitCode {
    let args = Args::parse();
    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();

    let (service, socket) = LspService::build(move |client| LazyBackend::new(client, args.clone()))
        .custom_method("acorn/info", LazyBackend::handle_info_request)
        .custom_method("acorn/progress", LazyBackend::handle_progress_request)
        .custom_method("acorn/search", LazyBackend::handle_search_request)
        .finish();

    Server::new(stdin, stdout, socket).serve(service).await;
    std::process::ExitCode::SUCCESS
}
