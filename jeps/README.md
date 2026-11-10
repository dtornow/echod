# jeps

A [Jepsen](https://github.com/jepsen-io/jepsen) test for echod, in the shape of
the [TigerBeetle suite](https://github.com/jepsen-io/tigerbeetle). It talks to
the nodes the way a client does: `POST /` with one Resonate envelope, and it
reads the envelope that comes back. It does not call the process, open the
store, or share the simulator's clock.

A pass of `promise`, `task`, `idempotence`, or `indefinite` means Knossos found
a linearization of every key against the document machine. The history was
produced from outside, so that linearization is the gateway, admission, the
process, the conditional commit, and the codec agreeing with the machine. It
is an outside oracle. It is not a proof, and `:unknown` is not a pass.

## Install

Jepsen's own machines are documented at [jepsen.io](https://jepsen.io/analyses).
For a local run you need a JDK (21 is what this was written against),
Leiningen, and an `echod` binary:

```
cargo build --release -p echod
cargo install s3s-fs --features binary
cd jeps
lein test
```

`lein test` does not start a node. It steps the document machine, runs Knossos
on small histories, and checks the deadline and push rules. `s3s-fs` is the
local bucket a `--local` run starts when `--store` is omitted.

## One test

From `jeps/`, against a binary you just built, two local processes, a shared
file store, and the kill fault:

```
lein run test --local --bin ../target/release/echod \
  --workload promise --nemesis kill \
  --time-limit 60 --key-count 40 --ops-per-key 20 --rate 30 \
  -n n1 -n n2
```

`--local` is one process per node on this machine. They share one bucket.
The store is the network: the nodes do not talk to each other, they find each
other by the announcements in that bucket, and a conditional write is the
only way a document moves. `file://` cannot be that bucket.
`object_store`'s local filesystem does not implement conditional updates, so
a document commit comes back 503 and a pass is impossible. With `--store`
omitted, the test starts `s3s-fs` (`cargo install s3s-fs --features binary`)
on a directory of its own and points the nodes at it. Pass `--store` and
`--endpoint` to use a bucket you already have. Results land in `jeps/store/`.

A remote cluster is the same command without `--local`, with `-n` for each
host and `--store` for the bucket those hosts already share. `--worker-host`
must be an address the hosts can push to. The binary is uploaded to
`/opt/echod`.

`lein run test-all --local --bin ../target/release/echod` runs the standard
suite: `promise`, `task`, `idempotence`, `schedule`, and `deadline`, each with
no fault, with `kill`, and with `pause`.

## Workloads

`promise` creates, reads, settles, and registers a listener. Deadlines are an
hour out, so a `rejected_timedout` read is a bug rather than a clock.

`task` targets the push worker, then acquires, heartbeats, releases, fulfills,
and settles. The lease is an hour, so a lease expiry is not a transition the
model has to guess.

`idempotence` repeats one create and a conflicting create, and one settle and
a conflicting settle, on the same id. The first to land wins, and every later
call returns that record.

`schedule` creates, reads, and deletes a schedule whose cron is yearly.
Admission requires `resonate:target` on the promise the schedule would
create, so the suite points that tag at the push worker. The cron does not
come due, the target is never called, and a fire (`lastRunAt`) fails the test.

`deadline` uses a short timeout and a 400ms timer bucket. A timer must
resolve. Anything else must not resolve with an empty value. The final read,
after the nodes are back, must be terminal. This one is not a Knossos search:
a timeout is a transition nobody invoked.

`indefinite` is the promise workload with a 50ms client timeout. A timeout or
a 503 is `:info`. The call may have committed, and the model tries it both
ways. The final reads use a long timeout. It is not in `test-all`.

Several keys share an origin (`--share`, default 4). The checker still treats
each promise as its own machine, so a conditional write that clobbers a
neighbour shows up as that neighbour's history failing to linearize.

## What the client records

A parsed envelope is `:ok`, including 400, 404, and 409. The model decides
whether that answer was legal. A client that called those `:fail` would hide
a false 400. A 503, a timeout, and a socket error are `:info`: the node may
have committed before the acknowledgement was lost. Final reads retry those.

## Faults

`kill` and `pause` are the faults that move membership and freeze a write.
`heal` resumes everyone and starts anyone who is down, then the test waits
(`--heal-time`) before the final reads.

`partition` cuts one node's path to the bucket and leaves its path to the
client and the worker up. It drops TCP to the store endpoint's port
(`--endpoint`, for example `10.0.3.1:18014`), not every packet to that host.
Nodes never talk to each other, so splitting them from each other tests
nothing. The fault that matters is a node that cannot reach the bucket.

It is not in the standard suite, and `--local` rejects it. Those processes
share the host's network stack, so an iptables rule on the host would also
cut the client. Run it on LXC nodes, each in its own network namespace:

```
bin/lxc-up
```

That brings up `lxcbr0` (`10.0.3.1/24`), DHCP, `n1` and `n2`, root SSH, and
`s3s-fs` on `10.0.3.1:18014`. Then, from this directory:

```
eval "$(ssh-agent -s)"
ssh-add ~/.ssh/jeps_lxc
AWS_ACCESS_KEY_ID=k AWS_SECRET_ACCESS_KEY=s AWS_REGION=us-east-1 \
AWS_EC2_METADATA_DISABLED=true \
lein run test --bin ../target/release/echod \
  --store s3://echod --endpoint http://10.0.3.1:18014 \
  --region us-east-1 --worker-host 10.0.3.1 \
  --nemesis partition -n n1 -n n2
```

`bin/lxc-up` writes that key and installs it for root on each node. Jepsen's
SSH client asks the agent first and throws if no agent is running, so a
password alone never gets a turn.

`--worker-host` is the bridge address. The worker's default, `127.0.0.1`,
is the container's own loopback, which the node cannot call.

Clock jumps are not a fault here. The strict model would call a timeout a
bug, and the deadline model would call a missed timeout a bug. LXC
containers share the host clock.

## Reading a result

`true` is a pass. `false` names the key and the operation that had no legal
linearization, or the invariant that broke: the HTTP status disagreed with
`head.status`, the node header was missing, a promise changed identity, two
terminal states were both observed, a listener was notified twice, a schedule
fired, or a node panicked.

`:unknown` means the search ran out of time (`--checker-timeout`, per key) or
a final read never came back. Run it again, or shorten `--ops-per-key`. Do not
read it as a pass.

An empty history is not a pass. The exercised checker wants a 2xx for each
function the workload exists to draw.

## REPL

`lein repl` opens `jepsen.echod.repl`. `(latest)` is the most recent test in
`store/`, `(history)` its history, `(results)` what the checker said.
