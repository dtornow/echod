# Backlog

What is next, in no fixed order. Each item says what it is, why, and
what done looks like. An item leaves this file when it lands.

## CI/CD

No CI runs today. We want one pipeline with two soaks:

- **On every push and pull request**: build, `cargo fmt --check`,
  `cargo clippy`, the unit and end-to-end tests, and a short soak of
  `echod-dst` that stays under about 30 seconds. The default soak
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

- **Instrumentation.** Antithesis-style assertions in the server and
  the simulator: `assert_always` for the invariants the proofs give us
  (one writer per origin, no stale read, every armed deadline fires
  once), `assert_sometimes` for the paths we want reached (a commit
  that races, a configuration change under load, a timer kept because
  the delete failed, a forward that comes back unavailable), and
  `assert_reachable` on the request kinds the soaks keep reporting as
  missing. The Antithesis SDK's assertions are no-ops outside the
  platform, so they can live in the code permanently.
- **Workload.** A workload definition: the container image, the
  compose of nodes plus a store, the client driver that issues the
  protocol's requests and checks the answers, and the fault
  configuration (crashes, partitions, clock jumps, store outages,
  matching what `echod-dst` inflicts). The checker in `echod-dst`
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

## Smaller items

- **Checker time on long histories.** Some seeds (5003 with three
  servers and 1500 operations, for one) take about nine minutes in the
  checker, on a history the simulation produced in seconds. Either a
  per-origin budget that reports "not checked" instead of running on,
  or a faster search. The nightly soak needs this bounded.
- **Simulator coverage.** Every soak line reports `task.continue` as
  never exercised, and `task.suspend`, `task.fence` and `task.release`
  are often missing. The client mix in `echod-dst` does not generate
  them, so those handlers are verified but never simulated. Schedules
  are not simulated at all: no `schedule.*` request in the mix, so the
  fire, its two commits and the collection of a stale schedule key run
  only in the end-to-end test. The oracle needs the schedule's document
  beside the origin's for a fire, and the checker a way to place a fire
  on both.
- **Occurrences theorem.** The fleet model orders a fire's two commits,
  origin then schedule, so that an occurrence is never lost; the proof
  does not yet state it. The theorem: every schedule whose last run is
  `t` has the promise its template expands to at `t` in the bucket. It
  needs the expansion as a function in the model and an invariant that a
  pending half's promise is in the origin's document.
- **Clippy.** The server crate has two constructors with more than
  seven arguments (`Applier::new`, `Nodes::new`), two `map_or` that
  should be `is_none_or`, and a large-variant enum in `doc.rs`.
- **README.** Nothing outside DESIGN.md mentions `/metrics` yet.
