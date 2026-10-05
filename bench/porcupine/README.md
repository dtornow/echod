# Porcupine's histories on this checker

Porcupine (github.com/anishathalye/porcupine, MIT) ships two sets of histories
with its tests and benchmarks: 103 etcd Jepsen logs (one register: read, write,
compare-and-set; many `:info` calls that never answer) and 6 key-value logs (get,
put, append on 10 keys, with 1, 10 and 50 clients). `expected_etcd.txt` holds
Porcupine's expected verdicts (etcd_095 has none).

```sh
bench/porcupine/fetch.sh                                   # the Go repo, pinned
cargo run --release --example porcupine_bench -- all       # this checker
(cd bench/porcupine/porcupine && go test -bench 'EtcdJepsen|Kv' -run '^$' -benchtime 2x)
```

`porcupine_rs_timing.rs` times the Rust port, porcupine-rs 0.3.0: unpack the
crate from crates.io into `porcupine-rs/`, add it as `examples/timing.rs` with an
`[[example]]` entry, and run it from the crate directory.

## Results (check only, parsing excluded; one machine, 4 cores)

Verdicts match Porcupine's everywhere except kv c50-bad: there this checker gave
up (the candidate limit, 2.3 million candidates at event 242) rather than
finding the violation. The etcd logs are being rechecked for the same; see the
commit history for the outcome.

| | this checker | porcupine-rs 0.3.0 | Porcupine (Go) |
|---|---|---|---|
| etcd, all 103 logs | 475 s | 0.36 s | 0.31 s |
| etcd, median log | 0.14 ms | 0.03 ms | 0.09 ms |
| etcd_007 (slowest) | 297 s | 89 ms | 79 ms |
| kv, 1 client ok / bad | 0.20 / 0.10 ms | 0.80 / 0.39 ms | 0.10 / 0.04 ms |
| kv, 10 clients ok / bad | 5.7 / 1.2 ms | 0.80 / 0.83 ms | 0.50 / 0.23 ms |
| kv, 50 clients ok / bad | 119 s / 414 s | 284 / 18 ms | 148 / 23 ms |

76 of the 103 etcd logs take under 1 ms here; 16 take over 100 ms.

## Why

The algorithms differ. Porcupine (Wing & Gong / Lowe) searches depth first for
one linearization of a finished history, caches (linearized set, state), and
backtracks when a response contradicts the order it chose. On a valid history it
rarely pays for alternatives.

This checker keeps every explanation that is still possible, event by event,
which is what lets it check a stream online, without backtracking, and with
background work, timers and server-sent messages. Its cost is the number of
explanations alive at once. That is small when responses pin the order down,
and large when many calls overlap and their responses don't say in which order
they took effect: concurrent writes to one register with pending responses
(etcd_002, etcd_007: up to 48,000 candidates), or 50 clients appending to the
same key (c50: over 100,000 per key). Footprints and partitions don't help
within one key, and subsumption can't merge candidates whose futures differ.

`check_history` uses what only a whole history tells: calls that never return
may take effect at any point or never, so they are optional for subsumption. On
these logs it changes nothing measurable; the candidates differ in calls that
do return later.

A depth-first mode for whole histories, which would also produce a certificate
directly, is the obvious next step for this kind of workload.
