// Modified for Venticorn.
// Verifies a Venticorn file, or the whole project.
//
// This is the CLI equivalent of what the IDE runs when you save.
//
// Try:
//   cargo build --release --bin=verify; time ~/venticorn/target/release/verify

use std::process::ExitCode;

use clap::Parser;
use venticorn::builder::Builder;
use venticorn::project::Project;

#[derive(Parser)]
struct Args {
    // Just verify a single module.
    #[clap(long)]
    module: Option<String>,

    // Create a dataset from the prover logs.
    #[clap(long)]
    dataset: bool,
}

#[tokio::main]
async fn main() -> ExitCode {
    let mut project = Project::new("math");

    let args = Args::parse();
    if let Some(module_name) = args.module {
        project.add_target(&module_name);
    } else {
        if let Err(error) = project.add_all_targets() {
            eprintln!("error loading project: {}", error);
            return ExitCode::FAILURE;
        }
    }

    // Set up the builder
    let mut builder = Builder::new(|event| {
        if let Some(m) = event.log_message {
            if let Some((target, diagnostic)) = event.diagnostic {
                if let Some(diagnostic) = diagnostic {
                    println!(
                        "{}, line {}: {}",
                        target,
                        diagnostic.range.start.line + 1,
                        m
                    );
                } else {
                    println!("{}: {}", target, m);
                }
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
