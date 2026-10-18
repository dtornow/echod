use clap::{Parser, Subcommand};
use echod_dst::sim::{run, Options};
use echod_dst::store::Faults;

#[derive(Parser)]
#[command(name = "echod-dst", about = "echod-server under deterministic simulation")]
struct Cli {
    #[command(subcommand)]
    cmd: Cmd,
}

#[derive(clap::Args, Clone)]
struct Knobs {
    #[arg(long, default_value_t = 2)]
    servers: u32,
    #[arg(long, default_value_t = 3)]
    clients: u32,
    #[arg(long, default_value_t = 300)]
    operations: u64,
    #[arg(long, default_value_t = 6)]
    origins: u64,
    /// Per store operation: no answer.
    #[arg(long, default_value_t = 2)]
    unavailable: u64,
    /// Per write: done, reported failed.
    #[arg(long, default_value_t = 2)]
    lost_ack: u64,
    /// Per conditional write: refused with nothing moved.
    #[arg(long, default_value_t = 2)]
    conflict: u64,
    /// Store latency, at most, in virtual ms.
    #[arg(long, default_value_t = 20)]
    latency: u64,
    /// Chance per crash tick that a node dies and is replaced.
    #[arg(long, default_value_t = 10)]
    crash: u64,
    #[arg(long, default_value_t = 2_000_000)]
    budget: u64,
}

impl Knobs {
    fn options(&self, seed: u64) -> Options {
        Options {
            seed,
            servers: self.servers,
            clients: self.clients,
            operations: self.operations,
            origins: self.origins,
            faults: Faults { unavailable_percent: self.unavailable, lost_ack_percent: self.lost_ack, conflict_percent: self.conflict, latency_ms: self.latency },
            crash_percent: self.crash,
            budget: self.budget,
            ..Options::default()
        }
    }
}

#[derive(Subcommand)]
enum Cmd {
    /// One run from one seed.
    Run {
        #[arg(long, default_value_t = 1)]
        seed: u64,
        #[command(flatten)]
        knobs: Knobs,
    },
    /// Many runs, one seed after another.
    Soak {
        #[arg(long, default_value_t = 1)]
        from: u64,
        #[arg(long, default_value_t = 50)]
        seeds: u64,
        #[command(flatten)]
        knobs: Knobs,
    },
}

fn main() {
    tracing_subscriber::fmt().with_env_filter(tracing_subscriber::EnvFilter::try_from_default_env().unwrap_or_else(|_| "error".into())).init();
    let cli = Cli::parse();
    match cli.cmd {
        Cmd::Run { seed, knobs } => {
            let r = run(knobs.options(seed));
            println!("{}", serde_json::to_string_pretty(&r).unwrap());
            if !r.ok {
                std::process::exit(1);
            }
        }
        Cmd::Soak { from, seeds, knobs } => {
            let mut failed = 0;
            for seed in from..from + seeds {
                let r = run(knobs.options(seed));
                println!(
                    "seed {seed}: {} entries={} sweeps={} crashes={} overlap={} store={} (unavail {} lost {} conflict {}) msgs={}+{} steps={}{}",
                    if r.ok { "ok" } else { "FAILED" },
                    r.entries, r.sweeps, r.crashes, r.overlapping_pairs, r.store_operations, r.store_unavailable, r.store_lost_acks, r.store_conflicts, r.executes, r.unblocks, r.search_steps,
                    if r.kinds_missing.is_empty() { String::new() } else { format!(" missing={:?}", r.kinds_missing) }
                );
                for f in &r.failures {
                    println!("  {f}");
                }
                if !r.ok {
                    failed += 1;
                }
            }
            if failed > 0 {
                println!("{failed} of {seeds} seeds failed");
                std::process::exit(1);
            }
        }
    }
}
