use anyhow::Result;

fn main() -> Result<()> {
    println!(
        "commit: {} {}",
        env!("VERGEN_GIT_COMMIT_DATE"),
        env!("VERGEN_GIT_SHA")
    );
    loam::lurk::cli::run()
}
