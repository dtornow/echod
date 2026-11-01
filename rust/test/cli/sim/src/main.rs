use clap::{Parser, Subcommand};
use echod_sim::sim::{run, Options};
use echod_sim::store::Faults;

#[derive(Parser)]
#[command(name = "echod-sim", about = "echod under deterministic simulation")]
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
    /// Clients create, read and delete schedules too.
    #[arg(long, default_value_t = false)]
    schedules: bool,
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
    /// Chance per chaos tick that a node dies and is replaced.
    #[arg(long, default_value_t = 10)]
    crash: u64,
    /// Chance per chaos tick that a node stops cleanly.
    #[arg(long, default_value_t = 5)]
    stop: u64,
    /// Chance per chaos tick that a node joins.
    #[arg(long, default_value_t = 8)]
    join: u64,
    /// Chance per chaos tick that a node loses the store for a while.
    #[arg(long, default_value_t = 10)]
    outage: u64,
    /// Chance per chaos tick that a node's clock jumps, either way. Off, as
    /// is every clock chaos: the checker's model keeps one clock, so a node
    /// on a clock of its own would be reported, not tested.
    #[arg(long, default_value_t = 0)]
    jump: u64,
    /// A node's clock is off by up to this many ms, either way.
    #[arg(long, default_value_t = 0)]
    skew: u64,
    /// A clock jump moves a node's clock by up to this many ms, either way.
    #[arg(long, default_value_t = 300)]
    jump_ms: u64,
    /// A node's clock drifts by up to this many parts per million.
    #[arg(long, default_value_t = 0)]
    drift: u64,
    /// Requests sent to a node other than the origin's owner, in percent:
    /// served there all the same, as a misrouted request is. Off: a read
    /// there may miss a write the owner decided and has not landed, whose
    /// stamp precedes the read, which the model's one clock cannot show.
    #[arg(long, default_value_t = 0)]
    misroute: u64,
    /// The checker's budget: nodes to explore, at most. For a failing seed,
    /// `ECHOD_SIM_DUMP=1` prints the trace up to the event and the steps the
    /// nodes reported; `ECHOD_SIM_PROGRESS=n` a line every n events;
    /// `ECHOD_SIM_WIDTH=n` gives up at a narrower profile and shows it.
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
            schedules: self.schedules,
            faults: Faults { unavailable_percent: self.unavailable, lost_ack_percent: self.lost_ack, conflict_percent: self.conflict, latency_ms: self.latency },
            crash_percent: self.crash,
            stop_percent: self.stop,
            join_percent: self.join,
            outage_percent: self.outage,
            jump_percent: self.jump,
            skew_ms: self.skew,
            jump_ms: self.jump_ms,
            drift_ppm: self.drift,
            misroute_percent: self.misroute,
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
                    "seed {seed}: {} entries={} sweeps={} fires={} crash/stop/join/out/jump={}/{}/{}/{}/{} overlap={} store={} (unavail {} lost {} conflict {}) msgs={}+{} steps={}{}",
                    if r.ok { "ok" } else { "FAILED" },
                    r.entries, r.sweeps, r.fires, r.crashes, r.stops, r.joins, r.outages, r.jumps, r.overlapping_pairs, r.store_operations, r.store_unavailable, r.store_lost_acks, r.store_conflicts, r.executes, r.unblocks, r.search_steps,
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
