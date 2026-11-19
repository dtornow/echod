# Document processing: implementation and verification boundary

**Component proofs; global theorem open.** The implementation includes executable
adapters, component proofs, and regression tests. It does not establish global
production-to-abstract trace refinement, even with the storage premise below.
The legacy full-refinement target is not a passing verification suite.

## Implemented behavior

A workflow request uses the existing per-document lane and cache/load path,
then performs:

```text
capture finite source workset
  -> project every due object
  -> drain callbacks, in stable source order
  -> drain listeners, in stable source order
  -> raw request handler
  -> add required timer key
  -> conditional document write
  -> await obsolete timer-key deletion reply (failure is allowed)
  -> release collected notifications and reply
```

Different documents may have concurrent flights; each local document lane is
serial. This is not a global exclusive-writer guarantee across nodes. A failed
conditional write discards the candidate notifications, rereads, and retries
within the existing retry policy. A failed timer addition prevents the document
write. An applied write followed by a lost acknowledgement is not rolled back.

The workflow sweep is finite and nonrecursive. It is not an iterative
fixpoint with a request sweep-limit rejection. It runs before the handler,
not again afterward. Work newly enabled by the handler waits for a later sweep.
Collected pre-handler notifications are not reconstructed or cancelled from
the final endpoint state. Source order remains significant. Only distinct
targets within one source have the proved commutation/permutation properties.

Schedule requests remain raw schedule operations: receiving a request does not
fire due schedules or sweep unrelated workflows. Schedule firing remains a
timer/runtime responsibility.

A cross-origin fence create is admitted as destination creation followed by
the source check. Other operations can interleave between those stages.
A failed later check does not undo the committed destination create. Its final
error response does not invent a successful inner-action result.

Three times remain distinct:

- Rover delivery time.
- Saved admission time: the pinned time, or the maximum of offered time and
  the causally observed membership clock floor.
- Evaluation time: the maximum of saved admission time and the loaded
  document's committed time, recomputed after a reread.

A pinned admission time of 7 can therefore evaluate at 20, and at 30 following
a CAS conflict and reread, without changing the saved admission time.

## Boundaries and adapters

Production state/specification definitions are owned by the neutral concrete
specification rather than imported backward from the implementation. The
dependency guard keeps production and concrete crates independent of the
abstract model. Shared production vocabulary lives in `echod-types`.

`ReplayBranch` reconstructs the real `State::on_event` from configuration,
loop policy, and explicit input history. It does not execute effects during
reconstruction. Its equality compares histories, not semantic state
equivalence. This is a bounded exploration/proof adapter, not a replacement
for the normal mutable production/DST path; replay has substantial overhead.

The production Rover bridge retains typed events/effects, configuration,
debug data, operation routing, timer wakes, and before/after-application
store faults. Public requests do not inject fake store replies or wakes.
Internal request identifiers retain the complete call for reply correlation.

The public theorem target is the decoded typed protocol boundary, with actual
routing/admission normalization. It is not a new proof of arbitrary JSON
parsing, unknown methods, payload-codec validation, or the debug control plane.
The public-call adapter no longer accepts a caller-selected document target.
It shares final routing with the runtime decoder. Unroutable typed requests
(including an empty heartbeat) produce a correlated 400 without a core event
or document effects. The raw heartbeat kernel's 200 result is not a public
HTTP-admission guarantee.

## What the proofs establish

- Production and abstract executable components compute their respective
  stated transitions; existing trusted library/codec bindings remain part of
  that boundary.
- Independent abstract timed-request helpers compose the finite workflow
  sweep with the raw request, including detached continuation and saved time.
- Document-level correspondence preserves the response, related document,
  unrelated-document frame, and complete lifted dispatch multiplicities.
  This is not yet a whole production-envelope/global-trace simulation.
- Generic Rover network permutation preserves an exact legal label sequence
  and boundary trace when process states and current time agree. It retains
  full envelopes, multiplicity, timestamps on labels, causal availability,
  and replay/nonconsuming delivery. Observations are not redefined as bags.
  This same-model transport theorem is a component, not the missing
  cross-model controller theorem.
- Independent document-installation specification helpers preserve unrelated
  **live** documents even if the evaluated candidate contains older unrelated
  data. They do not assume a fresh snapshot and are not yet wired into an
  executable delayed abstract controller.

## Explicit conditional storage premise

`document_validator_separation` is an explicit, operation-scoped theorem
precondition. For a document operation whose validator is accepted, the
compared current body must equal the body captured for that operation:

- `GetIfNoneMatch` returning `NotModified`;
- successful `PutIfMatch`;
- successful `AppIfMatch`, including the actual appendability and offset
  checks.

The execution proof must tie the captured body to real read/issue provenance;
it may not freely choose the current body as a witness. Failed comparisons
and unrelated operations impose no condition. `PutIfNoneMatch` success
requires absence independently of this premise. Same-body ABA is allowed;
fresh revision tokens are not required.

Five scoped storage lemmas are proved with that boundary. The premise is
**unproved for the current FNV content-validator model** and is **not a
guarantee supplied by the S3 adapter**. The implementation still uses its
actual validators and comparison semantics. No hash-injectivity axiom,
revision-token substitution, or storage redesign is introduced. This
approval does not authorize additional codec or identifier-freshness premises.

## Read-to-write provenance components

The `refinement_proof::provenance` module adds local obligations on the production
definitions, based on main `40fbe51` (including periodic timer rediscovery and
optional cron deadlines). These are not an inductive invariant of all executions.

| Component | Claim | Remaining connection |
| --- | --- | --- |
| Workflow and schedule reads | A successful matched `spec_apply(Get)` supplies the actual stored bytes and validator; successful decoding produces the exact working snapshot. | Establish that the accepted completion belongs to that invocation and key. |
| Cache revalidation | `NotModified`, the retained decode observation, and operation-scoped validator separation preserve the captured working snapshot. | Maintain the same raw-byte witness through cache history; do not choose current bytes as a fresh witness. |
| Commit initialization | The real commit constructor retains the working snapshot and captures its validator. | Connect the input working snapshot to the matched receipt. |
| Prewrite advancement | Start/key-put stages retain the snapshot and validator; an issued document write uses that key and validator and records the actual flight owner. | Establish the phase relation along the entire controller history and match key-put completions. |
| Write issuance | The emitted operation carries the specified key/validator, preserves the working snapshot, and registers its flight owner. | Registration can overwrite a reused numeric operation ID; no freshness or response-correlation claim is made. |
| Rejected comparison | A failed create/rewrite/append comparison leaves the modeled store unchanged. | Relate the response accepted by the controller to that operation. |
| Fault branches | The fleet store's before-application fault preserves old entries; its lost-ack branch retains exactly the normally applied state despite returning an error. | The existing `(node, op)` replay suppression is not a faithful invocation-lifecycle proof for reused IDs. |

### Trust ledger for this slice

- **New checked content:** the local implications above, over existing production
  transition definitions. Their branch guards and matched-receipt/decode inputs
  are explicit local prerequisites, not assumed global reachable invariants.
- **Approved conditional storage boundary:** only
  `document_validator_separation` for the selected conditional operation and its
  retained captured bytes. No injectivity, unique-revision, or fresh-token law.
- **Inherited realization axiom:** the read proof calls the existing
  `lemma_bytes_realised`, which uses `echod_types::common::axiom_bytes_realised`
  to relate the model's chosen byte vector to its sequence.
- **Inherited native trust:** production decode/encode observations remain the
  four uninterpreted `production_document_spec_*` codec functions and their
  existing native `assume_specification` bindings. No new trusted binding is
  introduced. Decode success is not an encode/decode round-trip theorem and
  does not by itself establish `loaded.bytes == captured.len()`.
- **Unchanged gaps:** byte-codec fidelity, version/count/byte-bound preservation,
  receipt identity, faithful invocation lifecycle, delayed-controller composition,
  and cross-model trace refinement remain open.

The next dependency chain is: retain a ghost receipt from a matched invocation;
preserve it through cache/flight transitions; compose the checked prewrite path
with the operation-scoped storage lemmas; connect encoded bytes to the committed
typed document; then compose timer, admission, detached-stage and observation
transitions. The typed codec-algebra work is independent of the byte bridge.

### Typed codec algebra

The ghost-only `echod_concrete_spec::codec_algebra` module contains 16 authored
proof functions (23 Verus verification obligations), covering snapshot and delta
map reconstruction, checked fold append, snapshot/delta metadata validity, and
change counts. Caller-supplied key order is retained; exact-domain enumeration
and uniqueness are explicit typed prerequisites, not a new serialization policy.
Version and time bounds in `partial_valid` are local lemma prerequisites, not
claims that every runtime transition preserves them.

The schedule specialization proves that a retired row with `next_run_at: None`
still produces one upsert, whereas an absent schedule produces zero. It does not
collapse retirement into deletion. The merged internal-`None`/public-`0` contract
is unchanged.

This algebra operates on `PartialV`/`FoldedV`, not serialized bytes. It introduces
no axiom, uninterpreted function, `assume`, or `external_body`, and does not
strengthen the production codec symbols. Matching native JSON equality, encoding,
parsing, newline provenance, byte lengths and machine-sized counts remains open.
In particular, the current append gate does not establish strict version advance
at saturated document version; that cannot be repaired by assuming a bound here.

Operation identity is a substantive obstruction, not just a solver obligation.
Independent characterization on this baseline bootstraps the actual core, holds
an old read's first completion, seeds the allocator near wrap, and reuses its
numeric operation ID for another key. Delivering each invocation's completion
only once can still send the old absent-read result to the new owner. This is a
seeded boundary countermodel, not a proved reachable `2^64`-operation prefix or
a deployed failure. A ghost invocation identity must retain this collision when
erased to the real bare-ID handler; it must not silently filter the completion.
No no-wrap premise or allocation-policy change is part of these proofs.

## Open global obligations and characterization tests

The full global conditional theorem remains open:

1. Compose the delayed abstract controller, real admission and membership
   clocks, per-document reads/writes, retries, detached stages, timer
   sequencing, and exact public delivery schedules.
2. Bind captured snapshots and issued operations to actual receipt/history
   provenance, including cache revalidation and lost acknowledgements.
3. Prove the production JSONL codec bridge and reachable preconditions:
   kind/id/deadline consistency, version/time progression, canonical rows,
   newline framing, byte/count representability, and actual append guards.
   The production encode/decode functions currently have individual native
   equality bindings, not proved snapshot/append round-trip laws. The old
   bare-JSON `DocumentBodyV` axiom does not apply to `StoredDocumentV` JSONL.
4. Resolve operation-ID reuse and response correlation under the actual
   adapter and Rover delivery models. Allocation wraps `u64`; dispatch removes
   the owner by operation ID. Rover retains messages for replay, while the
   real async adapter emits one completion for each spawned call.
5. Replace or correctly re-scope the legacy raw/public simulation, which does
   not establish the new staged public boundary.

The ordinary native codec tests exercise schedule snapshots, append,
compaction, and partial algebra. Additional characterization tests demonstrate
why stronger universal claims need more work:

- A JSONL snapshot can decode without a final newline, yet fail when a delta
  is concatenated directly. Ordinary encoder outputs include the newline;
  that provenance still needs proof.
- A **seeded** maximum-version delta that does not strictly advance the
  version cannot be folded, although a rewritten snapshot at that version
  decodes. This does not prove that ordinary execution reaches the saturated
  version or always satisfies the delta law's preconditions.
- With a **seeded** near-wrap allocator, an old absent-read reply can be
  accepted for a new read after ID reuse, producing 404 even though the fresh
  read returns a body. The late correct reply is ignored. This characterizes
  native-core dispatch under replay; it is not a reached `2^64`-operation
  prefix or a reproduction of replay by the ordinary async adapter.

None of these tests proves universal correctness, an initially reachable
counterexample, or a deployed production failure. No no-wrap assumption,
protocol-identity change, or extra trusted codec premise is hidden in the
storage condition.

## Validation and reproduction

The draft's passing component evidence before publication includes:

- `cargo check --workspace --locked` and the model-dependency guard.
- 17 abstract executable tests, 32 process tests (including four document
  codec tests and four partial-codec/algebra tests), and 27 runtime logic tests.
- The local short smoke run, seeds 1–5 with 100 operations each. This is
  bounded evidence, not exhaustive protocol coverage or a full soak.
- Verus: 100 abstract-spec, 154 abstract-exec, 185 concrete-spec, and 661
  production/process checks; these are separate package results, not a
  global refinement proof.
- 82 focused refinement checks: work (44), timed handlers (26), network (5),
  conditional storage (5), and document framing (2).

The publication validation reran the full refinement target: 296 checks
verified, with one resource-limit failure in `lemma_request_served`.
That failed run is neither a completed proof nor a demonstrated counterexample.
The broader model gaps above remain independently of that solver limit.

The PR body records publication-head validation and remote CI status.
Earlier results must not be called current-head results if relevant inputs
change. Full refinement failure is listed separately, never counted as a pass.
Lean sources are unchanged and no new Lean verification result is claimed.

```sh
cargo check --workspace --locked
python3 scripts/check-model-dependencies.py
cargo test --locked -p echod-abstract-exec -p echod-process --lib
cargo test --locked -p echod-runtime --test logic -- --test-threads=1
cargo run --release --locked -p echod-sim -- soak --from 1 --seeds 5 --operations 100

cargo verus verify -p echod-abstract-spec -p echod-abstract-exec \
  -p echod-concrete-spec -p echod-process
cargo verus verify -p echod-refinement # global target remains open/failing
```

For a fresh focused run, clean only the selected package's partial artifact:

```sh
cargo clean -p echod-refinement --target-dir target/verus-partial
cargo verus focus -p echod-refinement --target-dir target -- \
  --verify-only-module refinement_proof::work \
  --verify-only-module refinement_proof::timed_handlers \
  --verify-only-module refinement_proof::network \
  --verify-only-module refinement_proof::storage \
  --verify-only-module refinement_proof::frames
```

With the used Verus release, changing focus selectors could reuse a partial
artifact without rerunning proof checks. Require an actual `verification
results` line; a fast cached exit is not a fresh proof result. Full and
partial artifacts remain distinct. No full soak is part of this draft.
