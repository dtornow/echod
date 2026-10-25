# Backlog

What is next, in no fixed order. Each item says what it is, why, and
what done looks like. An item leaves this file when it lands.

## CI/CD

No CI runs today. We want one pipeline with two soaks:

- **On every push and pull request**: build, `cargo fmt --check`,
  `cargo clippy`, the unit and end-to-end tests, and a short soak of
  `echod-sim` that stays under about 30 seconds. The default soak
  (`--servers 2 --operations 300`) runs a seed in a second or two, so
  this is in the order of 20 seeds. The seed range should move with the
  commit (for instance from the run number), so that over time CI
  covers new seeds rather than the same twenty.
- **Nightly**: a long, substantial soak. Several hundred seeds with
  three or more servers and 1500 or more operations, run in parallel
  across the runner's cores, with the failing seeds and their JSON
  reports kept as artifacts. A failure opens or updates an issue with
  the seed and the command that reproduces it.

Done: a green check on the branch, and a nightly job whose history is
visible.

## Antithesis

Run echod under Antithesis. Two parts:

- **Instrumentation.** Antithesis-style assertions in the node and
  the simulator: `assert_always` for the invariants the proofs give us
  (one writer per origin, no stale read, every armed deadline fires
  once), `assert_sometimes` for the paths we want reached (a commit
  that races, a configuration change under load, a timer kept because
  the delete failed, a listing that fails and is retried), and
  `assert_reachable` on the request kinds the soaks keep reporting as
  missing. The Antithesis SDK's assertions are no-ops outside the
  platform, so they can live in the code permanently.
- **Workload.** A workload definition: the container image, the
  compose of nodes plus a store, the client driver that issues the
  protocol's requests and checks the answers, and the fault
  configuration (crashes, clock jumps, store outages,
  matching what `echod-sim` inflicts). The checker in `echod-sim`
  should be reusable as the workload's oracle rather than rewritten.

Done: a workload that runs on the platform and a first report.

## Dashboard

A default dashboard an operator can bring up with one command to
inspect a server or a cluster. This is an add-on beside the main
project, not part of it: a `dashboards/` directory with a compose file
that starts Prometheus scraping `/metrics` on every node and Grafana
with a provisioned dashboard. Panels: request rate and latency by kind
and route, store operations by outcome with `conflict` and `failed`
called out, commit fates, cache hit ratio and size against its bounds,
membership epoch and member count, whether each node is fresh and
acting, timer lag, and the wheel.

Done: `docker compose up` in `dashboards/` against a running cluster
shows the panels with data.

## Parity with the reference

`echod-diff` shows what is left between echod and the reference server:

- **Search.** `promise.search`, `task.search` and `schedule.search` are
  refused with 403. A search over documents in a bucket is a listing
  and a scan; whether to serve it at all is a design decision.
- **Preload.** `task.acquire`, `task.suspend` and `task.fence` answer an
  empty `preload`; the reference returns up to a limit of the promises
  the task may read next.
- **Detached creates.** A fence creating a promise in another origin: the
  reference allows a root id alone and checks the fence first; echod allows
  any id and creates first, then checks (DESIGN, "The detached create").
  `echod-diff` does not generate them; `echod-accordant` does.
- **A targeted timer.** The reference runs it as a task; the Lean
  specification and the accordant model refuse it; echod drops the target
  (an SDK's sleep). `echod-accordant` does not send one.
- **Steps when the node gets to them.** A lease is reclaimed, a retry
  dispatched, a schedule's occurrence fired and its run recorded (two
  commits, two documents) by the sweep that gets to the document, not
  at the instant each falls due; a client reading in between sees the
  lease held, the retry not sent, the occurrence without its run. The
  Lean specification's steps are enabled at the instant and fired by a
  fair scheduler, which admits this; the accordant model's are exact
  timers, and `echod-sim` checks against it with `reported`, where the
  node's steps are the model's at the instants the node reports.
  `echod-accordant` and `echod-diff` move the clock with `debug.tick`,
  which lets every due step land before the next request.
- **Stamps are decision instants.** A step's `created_at`, `settled_at`,
  `acquired_at` and the like are the instant the node decided it at, and
  the write lands later; a concurrent read of the document between the
  two sees the promise absent though its `created_at` precedes the read.
  One server with one clock, as the Lean specification has it, cannot
  show that. `echod-sim` places such a read at the stamp of the version
  it saw (DESIGN, "Simulation"); the reference server stamps before it
  commits too.

## Smaller items

- **Checker time on long histories.** Resolved by the move to accordant's
  checker with the node's steps reported: the profile stays at width 1
  and a seed checks in tens of milliseconds. The budget (`--budget`) and
  width limit still turn a blowup into a report rather than a hang.
- **Simulator coverage.** Every soak line reports `task.continue` as
  never exercised, and `task.suspend`, `task.fence` and `task.release`
  are often missing. The client mix in `echod-sim` does not generate
  them, so those handlers are verified but never simulated.
- **Clippy.** The kernel and the system carry clippy's style warnings
  (`&Vec` parameters, `match` on one pattern) that Verus's shape wants;
  decide which to allow in `lib.rs`.
- **README.** Nothing outside DESIGN.md mentions `/metrics` yet.
