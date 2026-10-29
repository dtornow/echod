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
- **A schedule fires when the node gets to it.** A schedule's occurrence
  is created and its run recorded (two commits, two documents) by the
  sweep that gets to the schedule's key, not at `nextRunAt`; a client
  reading in between sees the schedule not yet advanced and the
  occurrence absent. The Lean specification's step is enabled at the
  instant and fired by a fair scheduler, which admits this; the accordant
  model fires it anywhere within `fire_within` of the instant, and
  `echod-sim` gives it two timer buckets. A deadline and a lease's end,
  by contrast, are read as passed the moment they pass (DESIGN,
  "Writing"), and a retry rearms on a grid, so nothing else a client sees
  depends on when a node sweeps. External differential tools observe
  production timer behavior through responses and worker messages.
- **Stamps are decision instants.** A step's `created_at`, `settled_at`,
  `acquired_at` and the like are the instant the node decided it at, and
  the write lands later; a read on another node between the two sees the
  promise absent though its `created_at` precedes the read. One server
  with one clock, as the Lean specification has it, cannot show that.
  Routed to an origin's owner, its requests serialise behind one flight
  and the window closes; `echod-sim` routes that way, and `--misroute`
  sends a share elsewhere to see it. The reference server stamps before
  it commits too.

- **`concrete_refines_abstract`, proved.** Every bounded trace of the store
  machine (the bucket as state, the verified document handlers after a
  sweep as the request step, sweeps as internal work) is a trace of the
  Resonate model: `refine/`, `cargo verus verify -p echod-refine`, no
  admits. The relation (`theorem.rs`): the abstract state is the sweep of
  the concrete one at the clock, translated; the calls the same; the
  abstract has sent what the concrete has plus what the sweep sends; a
  timer on `id` at `t` for every deadline `t` the swept state owes, none
  due; the kernel's invariant, every lease at least its ttl ahead of its
  start, no `resonate:scope` tag, every version within the wire's `u32`.
  The steps: invoke, return, receive as bookkeeping; a sweep as a stutter
  (the swept state sweeps to itself); the tick as the lemma that the
  model's timers due by the new clock drain to the kernel's sweep there
  (`tick.rs`, `drain.rs`: any ready item runs in an order the sweep
  absorbs, `absorb.rs`, `onstep.rs`, `trans.rs`, `canon.rs`); a request as
  one commutation lemma per handler (`handlers.rs`, `hcommon.rs`,
  `hmany.rs`: the kernel's `spec_handle` on the swept bucket against the
  twin on the translated state, then the same drain, `effect.rs`).
  Bounded means (`request_bounded`): the clock and every instant and
  duration a request carries at most `MAX_TIME`, so no kernel sum wraps
  where the model saturates; the request passes the wire's validators
  where the model has no door (ids, process ids and addresses non-empty,
  ttl positive, a heartbeat naming some task, a fenced settle's state one
  that parses); no targeted timer (the wire drops the target, the SDKs'
  sleep; the protocol refuses it); no schedule. Two trusted statements
  beyond the kernel's and the model's own: the model's `origin` is the
  kernel's (both read before the first `:`), and the simulator's worker
  address is a URL. The model's side is now checked code: every handler
  in accordant's `exec.rs` is verified to compute its twin in `spec.rs`,
  and the model's `Model` impl is verified, so the checker's verdicts and
  this theorem speak about the same functions, under the model's own
  axioms (a value is its view; a set's elements come out in one order,
  `pset_seq`). What the proof moved: the kernel refuses an acquire
  at `u32::MAX` (`MAX_VERSION`), as the servers do, where it refused at
  `MAX_TIME`; a task record's resume count saturates as the wire's does;
  the store machine's plan mirrors the validators' doors on a delay, a
  task's target and a heartbeat's origins. Next: echod's own system model
  against the store machine, where the clocks and the stamps live, and
  schedules once the fire's shape is settled.

## Smaller items

- **Checker time on long histories.** The black-box trace leaves the
  checker a choice per open write per clock instant: a settle in flight
  across three instants may have landed at any of them, each a different
  `settled_at`, until its return says. Several open writes on one origin
  multiply, and a seed with many concurrent clients on few origins can
  exceed the profile's width or the budget (`--budget`), which turn the
  blowup into a report rather than a hang. The clock moves only to the
  instants the nodes stamp at, clients back off, the checker is told which
  calls never return and stale schedule work is a no-op, which keeps it
  narrower: eleven of fifteen seeds decide in seconds, the rest give up
  undecided, none refuted. The next lever is a client's knowledge that a
  failed call is over: the node answered unavailable or the connection
  dropped at an instant, after which the call's effect can land only
  within the store's latency; told so, the checker would stop placing it
  at every later instant. Fewer clients per origin or coarser clocks would
  keep it narrower still.
- **Simulator coverage.** Every soak line reports `task.continue` as
  never exercised, and `task.suspend`, `task.fence` and `task.release`
  are often missing. The client mix in `echod-sim` does not generate
  them, so those handlers are verified but never simulated.
- **Clippy.** The kernel and the system carry clippy's style warnings
  (`&Vec` parameters, `match` on one pattern) that Verus's shape wants;
  decide which to allow in `lib.rs`.
- **README.** Nothing outside DESIGN.md mentions `/metrics` yet.
