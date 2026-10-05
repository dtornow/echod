# Porcupine's histories on this checker

Porcupine (github.com/anishathalye/porcupine, MIT) ships two sets of histories
with its tests and benchmarks: 103 etcd Jepsen logs (one register: read, write,
compare-and-set; many `:info` calls that never answer) and 6 key-value logs (get,
put, append on 10 keys, with 1, 10 and 50 clients). `expected_etcd.txt` holds
Porcupine's expected verdicts (etcd_095 is an empty file and has none).

```sh
bench/porcupine/fetch.sh                                   # the Go repo, pinned
cargo run --release --example porcupine_bench -- all [--dfs] # this checker
(cd bench/porcupine/porcupine && go test -bench 'EtcdJepsen|Kv' -run '^$' -benchtime 2x)
```

`porcupine_rs_timing.rs` times the Rust port, porcupine-rs 0.3.0: unpack the
crate from crates.io into `porcupine-rs/`, add it as `examples/timing.rs` with an
`[[example]]` entry, and run it from the crate directory.

## Results (check only, parsing excluded; one machine, 4 cores, noisy)

`check_history` keeps every explanation alive at once (the online checker);
`check_complete` searches depth first, for complete histories (`--dfs`).

| | check_history | check_complete | porcupine-rs 0.3.0 | Porcupine (Go) |
|---|---|---|---|---|
| etcd, all 103 logs | 674 s | 4.1 s | 0.36 s | 0.31 s |
| etcd, median log | 0.18 ms | 0.14 ms | 0.03 ms | 0.09 ms |
| etcd_002 | 119 s | 3.6 s (1.5 s alone) | 151 ms | 115 ms |
| etcd_007 | 316 s | 0.29 s | 89 ms | 79 ms |
| kv, 1 client ok / bad | 0.20 / 0.10 ms | 0.17 / 0.10 ms | 0.80 / 0.39 ms | 0.10 / 0.04 ms |
| kv, 10 clients ok / bad | 5.7 / 1.2 ms | 2.0 / 0.35 ms | 0.80 / 0.83 ms | 0.50 / 0.23 ms |
| kv, 50 clients ok / bad | 119 s / gave up | 2–6 s / 90 ms | 284 / 18 ms | 148 / 23 ms |

Every verdict matches Porcupine's, in both modes, except `check_history` on kv
c50-bad, which gives up (2.3 million candidates). `check_complete` decides
everything. With certificates (`--dfs --certify`) all etcd verdicts are backed
by a certificate `certify` replays (2.8 s in total); kv with 50 clients runs out
of memory that way, because a certificate needs the whole history in one
search instead of one per key.

Search sizes are now Porcupine's: on etcd_007 this checker explores 49,000
candidates where Porcupine caches 123,000; on etcd_002 147,000 against 179,000;
on kv c50-ok 352,000 against 178,000. What remains is the cost per candidate
(several microseconds, mostly allocation and hashing of generic states and
pending sets, against Porcupine's under one).

## What made the depth-first search fast

1. **One move at a time.** An event is consumed as soon as nothing is owed
   before it; otherwise each single move is a branch, calls in the order they
   were invoked (the call made first most often took effect first).
2. **Known responses prune.** In a complete history every call's response is
   known, so a call takes effect only with an outcome that gives that response.
   Without this, a read placed in the wrong spot is found out only at its
   response, much later.
3. **Reads are ordinary calls.** The online checker's "early answers" (a read
   remembers every answer it could have given) make the same candidate look
   different on every path, which defeats memoization.
4. **Calls that never return and change nothing are never applied.** Jepsen's
   timed-out reads otherwise double the candidates, each.
5. **Partitions are interleaved.** Each key's search is resumed round robin with
   a doubling budget, so one hard key doesn't hold up a refutation another
   finds quickly. Porcupine runs partitions in parallel for the same reason: on
   c50-bad it needs 5.8 million cache entries for key 7 but 3,097 for key 3.

## Why the online checker is slower here

The algorithms differ. Porcupine (Wing & Gong / Lowe) searches depth first for
one linearization of a finished history, caches (linearized set, state), and
backtracks when a response contradicts the order it chose. On a valid history it
rarely pays for alternatives.

`check_history` keeps every explanation that is still possible, event by event,
which is what lets it check a stream online, without backtracking, and with
background work, timers and server-sent messages. Its cost is the number of
explanations alive at once. That is small when responses pin the order down,
and large when many calls overlap and their responses don't say in which order
they took effect: concurrent writes to one register with pending responses
(etcd_002, etcd_007: up to 48,000 candidates), or 50 clients appending to the
same key (c50: over 100,000 per key). For a complete history,
`check_complete` is the better tool.
