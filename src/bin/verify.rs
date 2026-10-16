// Modified for Venticorn.
// Verifies a Venticorn file, or the whole project.
//
// This is the CLI equivalent of what the IDE runs when you save.
//
// Try:
//   cargo build --release --bin=verify; time ~/venticorn/target/release/verify

use std::path::Path;
use std::process::ExitCode;

use clap::Parser;
use venticorn::persistent_cache::CachePolicy;
use venticorn::project::Project;

#[derive(Parser)]
struct Args {
    /// Verify one module name or .ac file; omit to verify the library.
    target: Option<String>,

    /// Verify one module (compatible with the positional module argument).
    #[clap(long, conflicts_with = "target")]
    module: Option<String>,

    /// Reuse validated proof results and save completed builds for future runs.
    #[clap(long, conflicts_with = "no_cache")]
    cache: bool,

    /// Verify without cached results (the default; retained for compatibility).
    #[clap(long)]
    no_cache: bool,

    // Create a dataset from the prover logs.
    #[clap(long)]
    dataset: bool,
}

#[tokio::main]
async fn main() -> ExitCode {
    let args = Args::parse();
    let mut project = match Project::new_local() {
        Ok(project) => project,
        Err(error) => {
            eprintln!("error loading library: {}", error);
            return ExitCode::FAILURE;
        }
    };
    project.set_cache_policy(if args.cache {
        CachePolicy::ReadWrite
    } else {
        CachePolicy::Disabled
    });
    if let Some(target) = args.target {
        if target.ends_with(".ac") {
            if let Err(error) = project.add_target_by_path(Path::new(&target)) {
                eprintln!("error loading file: {}", error);
                return ExitCode::FAILURE;
            }
        } else {
            project.add_target_by_name(&target);
        }
    } else if let Some(module_name) = args.module {
        project.add_target_by_name(&module_name);
    } else {
        if let Err(error) = project.add_all_targets() {
            eprintln!("error loading project: {}", error);
            return ExitCode::FAILURE;
        }
    }

    // Set up the builder
    let mut builder = project.builder(|event| {
        if let Some(m) = event.log_message {
            if let Some(diagnostic) = event.diagnostic {
                println!(
                    "{}, line {}: {}",
                    event.module,
                    diagnostic.range.start.line + 1,
                    m
                );
            } else {
                println!("{}", m);
            }
        }
    });
    builder.log_when_slow = true;
    if args.dataset {
        builder.create_dataset();
    }

    // Build
    project.build(&mut builder);
    builder.print_stats();
    let succeeded = builder.status.is_good();
    if let Some(dataset) = builder.dataset {
        dataset.save();
    }
    if succeeded {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}
