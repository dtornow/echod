The goal of this project is an end-to-end formally verified and deterministically simulation tested implementation of Resonate durable execution on S3.

The document-processing implementation and its current verification limits are
described in [DOCUMENT_SEMANTICS.md](DOCUMENT_SEMANTICS.md). The global production
trace-refinement theorem is unfinished; component verification is not an
end-to-end guarantee.

## Cron exhaustion

Schedules store an optional `next_run_at`. After their final occurrence they
retain their history with `None`, have no timer deadline, and do not fire again.
Public schedule responses and snapshots encode this as numeric `nextRunAt: 0`;
clients must interpret zero as “no future run”, not a Unix-epoch deadline.
Existing numeric-only clients can deserialize it; that alone does not mean they
understand the sentinel.

The new reader accepts existing numeric stored deadlines. Retired records store
`null` internally, so older binaries that require a numeric stored deadline
cannot read those records; rolling back after retirement requires a compatible
reader.

Creation rejects expressions without a future occurrence in the supported
calendar. The shared cron engine supports years **1970–2100 inclusive**.
This bound also applies to recurring expressions: exhaustion of that calendar
does not mean an expression is mathematically impossible beyond 2100.
No year remapping or synthetic one-minute fallback is used.

## Timer discovery

`--timer-rediscovery-ms` (or `ECHOD_TIMER_REDISCOVERY`) sets the target interval
between full timer-scan starts, defaulting to **300000 ms**. The interval must be
positive and no greater than the protocol's maximum supported time.

Scans revisit all existing timer bucket prefixes through the next bucket,
including historical buckets. This lets a stable owner discover keys written by
another node without waiting for an ownership change or an hourly bucket to
close. Normal discovery keeps one scan and one bucket read active at a time. Missed intervals
coalesce: a scan that outlasts its interval becomes eligible for another scan
after completion, without an additional full interval of idle time.

The concrete model and executable process both represent prefix scanning,
outstanding bucket reads, key application, and retry continuations. Failed bucket
reads retain the remaining scan and retry that bucket after one second; they do
not advance successful coverage. Debug reset discards the discovery continuation
and schedules a fresh load.

### Work and latency limits

Each event starts with a shared timer-work budget of 64 units. Prefix parsing, listed-key
application, due extraction, and due dispatch consume that same budget, including
reentrant dispatch. A listing step processes at most 32 entries. Remaining work
requests a physical wake; `State::on_event` returns before the runtime performs
effects, releasing the state mutex between events. Known due work can continue
while a scan is waiting on I/O or retry backoff.

The five-minute default is **not a hard discovery or settlement deadline**. A key
written just after its bucket was read can wait for the rest of the current scan
and its position in the next scan. A conservative healthy-I/O discovery bound,
conditional on bounded cycle durations and scheduling delay, is:

```text
D_discover ≤ max(Δ, C_current) + C_next + J
```

Here `Δ` is the configured interval, each `C` includes the scan's I/O and batch
continuations, and `J` is the delay starting the next eligible scan. Outages,
unbounded listings, or unbounded scheduling delays remove any finite bound.
Document processing and commit retries add settlement latency afterward.

The ordered index deduplicates exact `(deadline, key)` pairs, orders extraction
by deadline then key, and preserves distinct retry deadlines for the same key.
Reloads do not clone and filter the entire wheel: ownership is checked when a
slot fires. An unowned far-future slot can therefore remain until its deadline.

These are entry-count bounds, **not byte, memory, or elapsed-time bounds**.
Backends still materialize complete prefix/bucket listings. Key length, index
operations, allocation, and retained unowned slots also affect cost. The
`timer_wheel_bench` example measures isolated ascending insertion performance,
not concurrent HTTP responsiveness or a bound on mutex hold time.
