//! What this process keeps: the node, the timers, the document cache, and
//! the steps in progress.
//!
//! The object a step loaded sits with that step. Several documents can be
//! mid-step at once, one each, so there is no single loaded object here.
//! The cache is the documents this process remembers between steps.
//!
//! `StateSpec` is the state as the specification sees it; every method
//! ensures it computes its `spec_*` on it. Theorem 1 is `on_event` in
//! `handler.rs`: the process computes `spec_on_event`.

use vstd::contrib::make_spec_type;
use vstd::prelude::*;

use crate::cache::{Cache, Cached};
use crate::handler_docs::Flights;
use crate::keys::KeySpace;
use crate::state_node::Node;
use crate::state_timers::Timers;
use crate::types::*;
use crate::verified::node::Key;
use crate::verified::text::{concat3, strip_prefix};
use crate::Config;

#[cfg(verus_keep_ghost)]
use crate::cache::CachedSpec;
#[cfg(verus_keep_ghost)]
use crate::config::ConfigSpec;
#[cfg(verus_keep_ghost)]
use crate::keys::*;
#[cfg(verus_keep_ghost)]
use crate::verified::node_spec::*;
#[cfg(verus_keep_ghost)]
use crate::verified::node::AKey;
#[cfg(verus_keep_ghost)]
use echod_concrete::store::StoreReqSpec;

verus! {

/// Who waits for a store call's answer.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Structural)]
pub enum Owner {
    Flight(FlightId),
    Members,
    Timers,
    Debug,
    /// Nobody: a best-effort call whose answer changes nothing.
    Ignored,
}

#[cfg(verus_keep_ghost)]
impl DeepView for Owner {
    type V = Owner;
    open spec fn deep_view(&self) -> Owner {
        *self
    }
}

#[cfg(verus_keep_ghost)]
#[derive(Clone)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct StoreRequestHistory {
    pub inner: Ghost<Map<OpId, StoreReqSpec>>,
}

#[cfg(verus_keep_ghost)]
impl DeepView for StoreRequestHistory {
    type V = Map<OpId, StoreReqSpec>;

    open spec fn deep_view(&self) -> Self::V {
        self.inner@
    }
}

#[cfg(verus_keep_ghost)]
#[derive(Clone)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct StoreCertificateHistory {
    pub inner: Ghost<
        Map<
            OpId,
            crate::global_store_invariants::StoreEffectCertificateV,
        >,
    >,
}

#[cfg(verus_keep_ghost)]
impl DeepView for StoreCertificateHistory {
    type V = Map<
        OpId,
        crate::global_store_invariants::StoreEffectCertificateV,
    >;

    open spec fn deep_view(&self) -> Self::V {
        self.inner@
    }
}

/// The process. Every core transition uses `on_event`.
#[make_spec_type]
#[derive(Clone)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct State {
    pub cfg: Config,
    pub keys: KeySpace,
    /// Membership, the epoch, and the versions of origins this process has seen.
    pub node: Node,
    /// Deadline keys ordered by when they fall due, and a listing filling the wheel.
    pub timers: Timers,
    pub cache: Cache,
    /// The node's clock as the last event read it.
    pub clock: u64,
    pub tokens: u64,
    /// `tokens` has passed `u64::MAX`. No timer arm token can be allocated
    /// again during this process incarnation.
    pub tokens_exhausted: bool,
    pub next_op: OpId,
    /// `next_op` has passed `u64::MAX`. No operation id can be allocated
    /// again during this process incarnation.
    pub ops_exhausted: bool,
    pub next_flight: FlightId,
    /// `next_flight` has passed `u64::MAX`. No flight id can be allocated
    /// again during this process incarnation.
    pub flights_exhausted: bool,
    pub ops: crate::verified::table::Table<OpId, Owner>,
    /// Ghost-only immutable correlation from each active operation id to the
    /// exact Store request issued under it. `on_event` consumes the matching
    /// entry and atomically records every Store effect emitted by the event.
    #[cfg(verus_keep_ghost)]
    pub store_requests: StoreRequestHistory,
    /// The complete immutable certificate captured atomically with each
    /// active Store request and owner.
    #[cfg(verus_keep_ghost)]
    pub store_certificates: StoreCertificateHistory,
    /// One step in progress per document, and the queue behind it.
    pub flights: Flights,
    pub debug: crate::debug::Debug,
    /// Whether the node keeps itself going: heartbeats and timers.
    pub loops: bool,
    pub out: Vec<Effect>,
    /// The wake last asked of the runtime, so the same one is not asked twice.
    pub last_wake: Option<(u64, Armed)>,
}

#[cfg(verus_keep_ghost)]
pub type S = StateSpec;

// ---------------------------------------------------------------------------
// What each step means
// ---------------------------------------------------------------------------

pub open spec fn spec_state_new(cfg: ConfigSpec) -> S {
    S {
        node: crate::state_node::spec_node_new(cfg),
        timers: crate::state_timers::spec_timers_new(),
        cache: crate::cache::spec_new(cfg.cache_entries, cfg.cache_bytes),
        clock: 0,
        tokens: (hash(cfg.url + "/"@ + cfg.node_id) as u64) | 1,
        tokens_exhausted: false,
        next_op: 1,
        ops_exhausted: false,
        next_flight: 1,
        flights_exhausted: false,
        ops: Map::empty(),
        store_requests: Map::empty(),
        store_certificates: Map::empty(),
        flights: crate::handler_docs::spec_flights_new(),
        debug: crate::debug::spec_debug_new(),
        loops: false,
        out: Seq::empty(),
        last_wake: None,
        keys: KeySpaceSpec {
            prefix: spec_normalize_prefix(cfg.prefix),
            bucket_ms: if cfg.timer_bucket_ms < 1 { 1u64 } else { cfg.timer_bucket_ms },
        },
        cfg,
    }
}

/// The fleet's time: this node's clock, or the latest announcement it has
/// listed, whichever is later.
pub open spec fn spec_now(s: S) -> u64 {
    if s.clock > s.node.fleet_at { s.clock } else { s.node.fleet_at }
}

pub open spec fn spec_fresh(s: S) -> bool {
    crate::verified::node_spec::spec_fresh(s.node.core, spec_now(s) as nat)
}

pub open spec fn spec_acting(s: S) -> bool {
    s.node.core.members.len() != 0 && spec_fresh(s)
}

pub open spec fn spec_emit(s: S, e: EffectSpec) -> S {
    S { out: s.out.push(e), ..s }
}

pub open spec fn spec_note(s: S, n: NoteSpec) -> S {
    S { out: s.out.push(EffectSpec::Note(n)), ..s }
}

/// Rebuild the active Store-request correlation from the effects emitted by
/// one atomic core event.  The core may recurse through Members, Timers, and
/// document helpers while producing `effects`; keeping this fold at the event
/// boundary avoids carrying append-only request history through every helper.
pub open spec fn spec_record_store_requests(
    requests: Map<OpId, StoreReqSpec>,
    effects: Seq<EffectSpec>,
) -> Map<OpId, StoreReqSpec>
    decreases effects.len(),
{
    if effects.len() == 0 {
        requests
    } else {
        let prefix = effects.drop_last();
        let requests = spec_record_store_requests(requests, prefix);
        match effects.last() {
            EffectSpec::Store { op, request } =>
                requests.insert(op, request),
            _ => requests,
        }
    }
}

pub proof fn lemma_record_store_requests_contains_effect(
    requests: Map<OpId, StoreReqSpec>,
    effects: Seq<EffectSpec>,
    i: int,
    op: OpId,
    request: StoreReqSpec,
)
    requires
        0 <= i < effects.len(),
        effects[i] == (EffectSpec::Store { op, request }),
        forall|j: int, other: StoreReqSpec|
            0 <= j < effects.len()
                && effects[j] == (EffectSpec::Store {
                        op,
                        request: other,
                    }) ==> j == i && other == request,
    ensures
        spec_record_store_requests(requests, effects)
            .contains_key(op),
        spec_record_store_requests(requests, effects)[op] == request,
    decreases effects.len(),
{
    reveal(spec_record_store_requests);
    if i < effects.len() - 1 {
        lemma_record_store_requests_contains_effect(
            requests,
            effects.drop_last(),
            i,
            op,
            request,
        );
        assert(effects.drop_last()[i] == effects[i]);
        match effects.last() {
            EffectSpec::Store {
                op: last_op,
                request: last_request,
            } => {
                if last_op == op {
                    assert(i == effects.len() - 1);
                    assert(last_request == request);
                }
            },
            _ => {},
        }
    } else {
        assert(i == effects.len() - 1);
        assert(effects[i] == effects.last());
    }
}

pub proof fn lemma_record_store_requests_preserves(
    requests: Map<OpId, StoreReqSpec>,
    effects: Seq<EffectSpec>,
    op: OpId,
)
    requires
        requests.contains_key(op),
        forall|i: int, request: StoreReqSpec|
            0 <= i < effects.len()
                && effects[i]
                    == (EffectSpec::Store { op, request }) ==> false,
    ensures
        spec_record_store_requests(requests, effects)
            .contains_key(op),
        spec_record_store_requests(requests, effects)[op]
            == requests[op],
    decreases effects.len(),
{
    reveal(spec_record_store_requests);
    if effects.len() > 0 {
        let prefix = effects.drop_last();
        assert forall|i: int, request: StoreReqSpec|
            0 <= i < prefix.len()
                && prefix[i]
                    == (EffectSpec::Store { op, request }) implies false by {
            assert(prefix[i] == effects[i]);
        };
        lemma_record_store_requests_preserves(
            requests,
            prefix,
            op,
        );
        match effects.last() {
            EffectSpec::Store { op: last_op, request } => {
                assert(last_op != op);
            },
            _ => {},
        }
    }
}

/// A Store request has an exact executable `StoreReq` carrier. This is the
/// single totalization guard for every core-to-Store boundary: codec outputs
/// and composed keys may be mathematical sequences in the pure model, but
/// an effect is emitted only when all of them fit their Rust carriers.
pub open spec fn spec_store_request_representable(
    request: StoreReqSpec,
) -> bool {
    match request {
        StoreReqSpec::Get { key }
        | StoreReqSpec::Del { key } =>
            key.len() <= usize::MAX as int,
        StoreReqSpec::GetIfNoneMatch { key, etag } =>
            key.len() <= usize::MAX as int
                && etag.0.len() <= usize::MAX as int,
        StoreReqSpec::PutIfMatch { key, body, etag }
        | StoreReqSpec::AppIfMatch { key, body, etag, .. } =>
            key.len() <= usize::MAX as int
                && body.len() <= usize::MAX as int
                && etag.0.len() <= usize::MAX as int,
        StoreReqSpec::PutIfNoneMatch { key, body }
        | StoreReqSpec::Put { key, body } =>
            key.len() <= usize::MAX as int
                && body.len() <= usize::MAX as int,
        StoreReqSpec::List { prefix, .. }
        | StoreReqSpec::ListPrefixes { prefix } =>
            prefix.len() <= usize::MAX as int,
    }
}

pub proof fn lemma_store_request_representable(request: &StoreReq)
    ensures
        spec_store_request_representable(request.deep_view()),
{
    match request {
        StoreReq::Get { key } | StoreReq::Del { key } => {
            crate::verified::text::string_bounded(&key);
        },
        StoreReq::GetIfNoneMatch { key, etag } => {
            crate::verified::text::string_bounded(&key);
            crate::verified::text::string_bounded(&etag.0);
        },
        StoreReq::PutIfMatch { key, body, etag }
        | StoreReq::AppIfMatch { key, body, etag, .. } => {
            crate::verified::text::string_bounded(&key);
            assert(body@.len() == body.len());
            crate::verified::text::string_bounded(&etag.0);
        },
        StoreReq::PutIfNoneMatch { key, body }
        | StoreReq::Put { key, body } => {
            crate::verified::text::string_bounded(&key);
            assert(body@.len() == body.len());
        },
        StoreReq::List { prefix, .. }
        | StoreReq::ListPrefixes { prefix } => {
            crate::verified::text::string_bounded(&prefix);
        },
    }
}

/// Allocate and issue one Store call. `u64::MAX` is allocated once; after
/// that, exhaustion is permanent for this process incarnation and no effect
/// or owner is created. Unrepresentable pure-spec requests take the same safe
/// no-effect path before operation allocation.
pub open spec fn spec_store(
    s: S,
    request: StoreReqSpec,
    owner: Owner,
) -> (S, Option<OpId>) {
    spec_store_raw(
        s,
        request,
        owner,
        crate::global_store_invariants::StoreEffectCertificateV::Other,
    )
}

pub open spec fn spec_store_certified(
    s: S,
    request: StoreReqSpec,
    owner: Owner,
    certificate:
        crate::global_store_invariants::StoreEffectCertificateV,
) -> (S, Option<OpId>) {
    spec_store_raw(s, request, owner, certificate)
}

pub open spec fn spec_store_raw(
    s: S,
    request: StoreReqSpec,
    owner: Owner,
    certificate:
        crate::global_store_invariants::StoreEffectCertificateV,
) -> (S, Option<OpId>) {
    if s.ops_exhausted || !spec_store_request_representable(request) {
        (s, None)
    } else {
        let op = s.next_op;
        (S {
            next_op: if op == u64::MAX { op } else { (op + 1) as u64 },
            ops_exhausted: op == u64::MAX,
            ops: s.ops.insert(op, owner),
            store_requests: s.store_requests.insert(op, request),
            store_certificates:
                s.store_certificates.insert(op, certificate),
            out: s.out.push(EffectSpec::Store { op, request }),
            ..s
        }, Some(op))
    }
}

pub proof fn lemma_spec_store_totalized(
    s: S,
    request: StoreReqSpec,
    owner: Owner,
)
    ensures
        ({
            let (next, op) = spec_store(s, request, owner);
            match op {
                None => next == s,
                Some(op) => {
                    &&& spec_store_request_representable(request)
                    &&& next.store_requests.contains_key(op)
                    &&& next.store_requests[op] == request
                    &&& next.out.len() == s.out.len() + 1
                    &&& next.out.last()
                        == EffectSpec::Store { op, request }
                },
            }
        }),
{
}

pub proof fn lemma_unrepresentable_store_request_stutters(
    s: S,
    request: StoreReqSpec,
    owner: Owner,
)
    requires
        !spec_store_request_representable(request),
    ensures
        spec_store(s, request, owner) == (s, None),
{
}

/// Allocate a timer-arm token. `u64::MAX` is allocated once; exhaustion is
/// then permanent for this process incarnation.
pub open spec fn spec_token(s: S) -> (S, Option<u64>) {
    if s.tokens_exhausted {
        (s, None)
    } else {
        let token = s.tokens;
        (
            S {
                tokens: if token == u64::MAX {
                    token
                } else {
                    (token + 1) as u64
                },
                tokens_exhausted: token == u64::MAX,
                ..s
            },
            Some(token),
        )
    }
}

/// Allocate a flight id. `u64::MAX` is allocated once; exhaustion is then
/// permanent for this process incarnation.
pub open spec fn spec_flight(s: S) -> (S, Option<FlightId>) {
    if s.flights_exhausted {
        (s, None)
    } else {
        let flight = s.next_flight;
        (
            S {
                next_flight: if flight == u64::MAX {
                    flight
                } else {
                    (flight + 1) as u64
                },
                flights_exhausted: flight == u64::MAX,
                ..s
            },
            Some(flight),
        )
    }
}

/// The name of a key in the bucket, armed by `by`.
pub open spec fn spec_key_name(s: S, k: AKey, by: Seq<char>) -> Seq<char> {
    if crate::verified::text::spec_starts_with(k.origin, "s:"@) {
        spec_sched_timer_key(s.keys.prefix, s.keys.bucket_ms, k.origin.skip(2), k.at as u64, k.token as u64, by)
    } else if crate::verified::text::spec_starts_with(k.origin, "w:"@) {
        spec_timer_key(s.keys.prefix, s.keys.bucket_ms, k.origin.skip(2), k.at as u64, k.token as u64, by)
    } else if crate::verified::text::spec_starts_with(k.origin, "sched:"@) {
        spec_sched_timer_key(s.keys.prefix, s.keys.bucket_ms, k.origin.skip(6), k.at as u64, k.token as u64, by)
    } else {
        spec_timer_key(s.keys.prefix, s.keys.bucket_ms, k.origin, k.at as u64, k.token as u64, by)
    }
}

/// Forget every origin the cache evicted, in order.
pub open spec fn spec_forget_all(core: ANode, evicted: Seq<Seq<char>>) -> ANode
    decreases evicted.len(),
{
    if evicted.len() == 0 { core } else { spec_forget_all(spec_forget(core, evicted[0]), evicted.drop_first()) }
}

/// Remember a document and report its version to the core: read or wrote.
pub open spec fn spec_remember(s: S, origin: Seq<char>, c: CachedSpec) -> S {
    let (evicted, cache) = crate::cache::spec_put(s.cache, origin, c);
    let core = spec_forget_all(s.node.core, evicted);
    let core = spec_filled(core, origin, c.etag.0, c.filled_at as nat);
    S { cache, node: crate::state_node::NodeSpec { core, ..s.node }, ..s }
}

pub open spec fn spec_forget_origin(s: S, origin: Seq<char>) -> S {
    S {
        cache: crate::cache::spec_remove(s.cache, origin),
        node: crate::state_node::NodeSpec { core: spec_forget(s.node.core, origin), ..s.node },
        ..s
    }
}

pub open spec fn spec_wake_moved(s: S, next: Option<(u64, Armed)>) -> (S, bool) {
    if next == s.last_wake { (s, false) } else { (S { last_wake: next, ..s }, true) }
}

// ---------------------------------------------------------------------------
// The process, step for step
// ---------------------------------------------------------------------------

proof fn lemma_forget_all_step(core: ANode, evicted: Seq<Seq<char>>, i: int)
    requires
        0 <= i <= evicted.len(),
    ensures
        spec_forget_all(core, evicted) == spec_forget_all(spec_forget_all(core, evicted.take(i)), evicted.skip(i)),
    decreases i,
{
    if i == 0 {
        assert(evicted.take(0) =~= Seq::<Seq<char>>::empty());
        assert(evicted.skip(0) =~= evicted);
    } else {
        lemma_forget_all_step(core, evicted, i - 1);
        let mid = spec_forget_all(core, evicted.take(i - 1));
        assert(evicted.skip(i - 1).drop_first() =~= evicted.skip(i));
        assert(evicted.skip(i - 1)[0] == evicted[i - 1]);
        lemma_forget_all_push(core, evicted.take(i - 1), evicted[i - 1]);
        assert(evicted.take(i - 1).push(evicted[i - 1]) =~= evicted.take(i));
    }
}

proof fn lemma_forget_all_push(core: ANode, evicted: Seq<Seq<char>>, o: Seq<char>)
    ensures
        spec_forget_all(core, evicted.push(o)) == spec_forget(spec_forget_all(core, evicted), o),
    decreases evicted.len(),
{
    reveal_with_fuel(spec_forget_all, 3);
    if evicted.len() == 0 {
        assert(evicted.push(o)[0] == o);
        assert(evicted.push(o).drop_first() =~= Seq::<Seq<char>>::empty());
        assert(spec_forget_all(core, evicted.push(o)) == spec_forget(core, o));
    } else {
        assert(evicted.push(o)[0] == evicted[0]);
        assert(evicted.push(o).drop_first() =~= evicted.drop_first().push(o));
        lemma_forget_all_push(spec_forget(core, evicted[0]), evicted.drop_first(), o);
    }
}

impl State {
    pub fn new(cfg: Config) -> (r: State)
        ensures
            r.deep_view() == spec_state_new(cfg.deep_view()),
    {
        let keys = KeySpace::new(cfg.prefix.as_str(), cfg.timer_bucket_ms);
        let cache = Cache::new(cfg.cache_entries, cfg.cache_bytes);
        let seeded = concat3(cfg.url.as_str(), "/", cfg.node_id.as_str());
        let seed = crate::keys::fnv1a(seeded.as_str()) | 1;
        let r = State {
            node: Node::new(&cfg),
            timers: Timers::new(),
            cache,
            clock: 0,
            tokens: seed,
            tokens_exhausted: false,
            next_op: 1,
            ops_exhausted: false,
            next_flight: 1,
            flights_exhausted: false,
            ops: crate::verified::table::Table::new(),
            #[cfg(verus_keep_ghost)]
            store_requests: StoreRequestHistory {
                inner: Ghost(Map::empty()),
            },
            #[cfg(verus_keep_ghost)]
            store_certificates: StoreCertificateHistory {
                inner: Ghost(Map::empty()),
            },
            flights: Flights::new(),
            debug: crate::debug::Debug::new(),
            loops: false,
            out: Vec::new(),
            last_wake: None,
            keys,
            cfg,
        };
        proof {
            assert(r.out.deep_view() =~= Seq::<EffectSpec>::empty());
        }
        r
    }

    /// The fleet's time: this node's clock, or the latest announcement it
    /// has listed, whichever is later.
    pub fn now(&self) -> (r: u64)
        ensures
            r == spec_now(self.deep_view()),
    {
        if self.clock > self.node.fleet_at { self.clock } else { self.node.fleet_at }
    }

    /// Whether this node's view of the membership is young enough to act on.
    pub fn fresh(&self) -> (r: bool)
        ensures
            r == spec_fresh(self.deep_view()),
    {
        self.node.core.fresh(self.now())
    }

    pub(crate) fn allocate_flight(&mut self) -> (r: Option<FlightId>)
        ensures
            (final(self).deep_view(), r)
                == spec_flight(old(self).deep_view()),
    {
        if self.flights_exhausted {
            None
        } else {
            let flight = self.next_flight;
            if flight == u64::MAX {
                self.flights_exhausted = true;
            } else {
                self.next_flight = flight + 1;
            }
            Some(flight)
        }
    }

    /// Whether this node acts as owner of what the members make it the
    /// owner of: fresh, in a configuration with members.
    pub fn acting(&self) -> (r: bool)
        ensures
            r == spec_acting(self.deep_view()),
    {
        self.node.core.members.len() != 0 && self.fresh()
    }

    pub fn emit(&mut self, e: Effect)
        ensures
            final(self).deep_view() == spec_emit(old(self).deep_view(), e.deep_view()),
    {
        let ghost o = self.out.deep_view();
        let ghost ev = e.deep_view();
        self.out.push(e);
        proof {
            assert(self.out.deep_view() =~= o.push(ev));
        }
    }

    pub fn note(&mut self, n: Note)
        ensures
            final(self).deep_view() == spec_note(old(self).deep_view(), n.deep_view()),
    {
        self.emit(Effect::Note(n));
    }

    /// Issue a store call; `owner` gets its answer.
    pub fn store(&mut self, request: StoreReq, owner: Owner) -> (op: Option<OpId>)
        ensures
            (final(self).deep_view(), op) == spec_store(old(self).deep_view(), request.deep_view(), owner),
    {
        self.store_raw(
            request,
            owner,
            Ghost(
                crate::global_store_invariants::
                    StoreEffectCertificateV::Other,
            ),
        )
    }

    pub fn store_certified(
        &mut self,
        request: StoreReq,
        owner: Owner,
        certificate: Ghost<
            crate::global_store_invariants::StoreEffectCertificateV,
        >,
    ) -> (op: Option<OpId>)
        ensures
            (final(self).deep_view(), op)
                == spec_store_certified(
                    old(self).deep_view(),
                    request.deep_view(),
                    owner,
                    certificate@,
                ),
    {
        self.store_raw(request, owner, certificate)
    }

    fn store_raw(
        &mut self,
        request: StoreReq,
        owner: Owner,
        certificate: Ghost<
            crate::global_store_invariants::StoreEffectCertificateV,
        >,
    ) -> (op: Option<OpId>)
        ensures
            (final(self).deep_view(), op)
                == spec_store_raw(
                    old(self).deep_view(),
                    request.deep_view(),
                    owner,
                    certificate@,
                ),
    {
        proof {
            lemma_store_request_representable(&request);
        }
        if self.ops_exhausted {
            return None;
        }
        let op = self.next_op;
        if op == u64::MAX {
            self.ops_exhausted = true;
        } else {
            self.next_op = op + 1;
        }
        self.ops.insert(op, owner);
        #[cfg(verus_keep_ghost)]
        {
            self.store_requests = StoreRequestHistory {
                inner: Ghost(
                    self.store_requests.deep_view().insert(
                        op,
                        request.deep_view(),
                    ),
                ),
            };
            self.store_certificates = StoreCertificateHistory {
                inner: Ghost(
                    self.store_certificates.deep_view().insert(
                        op,
                        certificate@,
                    ),
                ),
            };
        }
        self.emit(Effect::Store { op, request });
        Some(op)
    }

    /// Allocate a timer-arm token. The maximum token is returned once.
    pub fn token(&mut self) -> (t: Option<u64>)
        ensures
            (final(self).deep_view(), t) == spec_token(old(self).deep_view()),
    {
        if self.tokens_exhausted {
            return None;
        }
        let t = self.tokens;
        if t == u64::MAX {
            self.tokens_exhausted = true;
        } else {
            self.tokens = t + 1;
        }
        Some(t)
    }

    /// The name of a key in the bucket, armed by `by`.
    pub fn key_name(&self, k: &Key, by: &str) -> (r: String)
        ensures
            r@ == spec_key_name(self.deep_view(), k@, by@),
    {
        match strip_prefix(k.origin.as_str(), "s:") {
            Some(id) => {
                proof {
                    reveal_strlit("s:");
                    assert(k.origin@.subrange(0, 2) =~= "s:"@);
                    assert(k.origin@.skip(2) =~= id@);
                }
                self.keys.sched_timer_key(id.as_str(), k.at, k.token, by)
            },
            None => match strip_prefix(k.origin.as_str(), "w:") {
                Some(origin) => {
                    proof {
                        reveal_strlit("s:");
                        reveal_strlit("w:");
                        assert(k.origin@.subrange(0, 2) =~= "w:"@);
                        assert(k.origin@.skip(2) =~= origin@);
                    }
                    self.keys.timer_key(
                        origin.as_str(),
                        k.at,
                        k.token,
                        by,
                    )
                },
                None => match strip_prefix(
                    k.origin.as_str(),
                    "sched:",
                ) {
                    Some(id) => {
                        proof {
                            reveal_strlit("s:");
                            reveal_strlit("w:");
                            reveal_strlit("sched:");
                            assert(k.origin@.subrange(0, 6)
                                =~= "sched:"@);
                            assert(k.origin@.skip(6) =~= id@);
                        }
                        self.keys.sched_timer_key(
                            id.as_str(),
                            k.at,
                            k.token,
                            by,
                        )
                    },
                    None => {
                        proof {
                            reveal_strlit("s:");
                            reveal_strlit("w:");
                            reveal_strlit("sched:");
                        }
                        self.keys.timer_key(
                            k.origin.as_str(),
                            k.at,
                            k.token,
                            by,
                        )
                    },
                },
            },
        }
    }

    /// Remember a document and report its version to the core: read or wrote.
    pub fn remember(&mut self, origin: &str, c: Cached)
        ensures
            final(self).deep_view() == spec_remember(old(self).deep_view(), origin@, c.deep_view()),
    {
        let etag = crate::verified::text::copy_string(&c.etag.0);
        let filled_at = c.filled_at;
        let evicted = self.cache.put(origin, c);
        let ghost ev = evicted.deep_view();
        let ghost core0 = self.node.core@;
        let mut i = 0;
        while i < evicted.len()
            invariant
                i <= evicted.len(),
                ev == evicted.deep_view(),
                self.node.core@ == spec_forget_all(core0, ev.take(i as int)),
                *self == (State { node: Node { core: self.node.core, ..old(self).node }, cache: self.cache, ..*old(self) }),
            decreases evicted.len() - i,
        {
            let ghost before = self.node.core@;
            self.node.core.forget(evicted[i].as_str());
            proof {
                lemma_forget_all_push(core0, ev.take(i as int), ev[i as int]);
                assert(ev.take(i as int).push(ev[i as int]) =~= ev.take(i as int + 1));
            }
            i += 1;
        }
        proof {
            assert(ev.take(i as int) =~= ev);
        }
        self.node.core.filled(origin, etag, filled_at);
    }

    pub fn forget(&mut self, origin: &str)
        ensures
            final(self).deep_view() == spec_forget_origin(old(self).deep_view(), origin@),
    {
        self.cache.forget(origin);
        self.node.core.forget(origin);
    }

    pub fn take_out(&mut self) -> (r: Vec<Effect>)
        ensures
            r.deep_view() == old(self).deep_view().out,
            final(self).deep_view() == (S { out: Seq::empty(), ..old(self).deep_view() }),
    {
        let mut out: Vec<Effect> = Vec::new();
        core::mem::swap(&mut out, &mut self.out);
        proof {
            assert(self.out.deep_view() =~= Seq::<EffectSpec>::empty());
        }
        out
    }

    pub fn set_clock(&mut self, clock: u64)
        ensures
            final(self).deep_view() == (S { clock, ..old(self).deep_view() }),
    {
        self.clock = clock;
    }

    pub fn set_loops(&mut self, loops: bool)
        ensures
            final(self).deep_view() == (S { loops, ..old(self).deep_view() }),
    {
        self.loops = loops;
    }

    pub fn clear_wake(&mut self)
        ensures
            final(self).deep_view() == (S { last_wake: None, ..old(self).deep_view() }),
    {
        self.last_wake = None;
    }

    pub fn wake_moved(&mut self, next: Option<(u64, Armed)>) -> (r: bool)
        ensures
            (final(self).deep_view(), r) == spec_wake_moved(old(self).deep_view(), next),
    {
        let same = match (&next, &self.last_wake) {
            (Some((a, x)), Some((b, y))) => *a == *b && *x == *y,
            (None, None) => true,
            _ => false,
        };
        if same {
            return false;
        }
        self.last_wake = next;
        true
    }
}

} // verus!

/// What an observer reads of the node at a glance.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Snapshot {
    pub cache_entries: u64,
    pub cache_bytes: u64,
    pub cache_evictions: u64,
    pub epoch: u64,
    pub members: u64,
    pub fresh: bool,
    pub acting: bool,
    pub timers_armed: u64,
}

#[cfg(not(verus_keep_ghost))]
impl State {
    pub fn config(&self) -> &Config {
        &self.cfg
    }

    pub fn id(&self) -> &str {
        &self.cfg.node_id
    }

    pub fn url(&self) -> &str {
        &self.cfg.url
    }

    pub fn membership(&self) -> crate::state_node::Membership {
        self.node.members.snapshot(&self.node.core)
    }

    /// The member that owns `target` by the members this node holds.
    pub fn owner(&self, target: &str) -> Option<String> {
        self.node.core.owner(target)
    }

    pub fn snapshot(&self) -> Snapshot {
        let c = self.cache.stats();
        Snapshot {
            cache_entries: c.entries as u64,
            cache_bytes: c.bytes,
            cache_evictions: c.evictions,
            epoch: self.node.core.epoch,
            members: self.node.core.members.len() as u64,
            fresh: self.fresh(),
            acting: self.acting(),
            timers_armed: self.timers.wheel.len() as u64,
        }
    }

    pub fn keys(&self) -> &KeySpace {
        &self.keys
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use echod_concrete::store::{StoreError, StoreReq, StoreRes};
    use echod_types::{Request, Response, TaskGetReq};

    #[test]
    fn operation_id_max_is_issued_once_then_allocation_stutters() {
        let mut state = State::new(Config::memory("node-0"));
        state.next_op = u64::MAX;

        let first = state.store(
            StoreReq::Get { key: "first".to_string() },
            Owner::Ignored,
        );
        assert_eq!(first, Some(u64::MAX));
        assert!(state.ops_exhausted);
        let effects_after_first = state.out.len();
        let owners_after_first = state.ops.entries.len();

        let second = state.store(
            StoreReq::Del { key: "second".to_string() },
            Owner::Ignored,
        );
        assert_eq!(second, None);
        assert_eq!(state.next_op, u64::MAX);
        assert_eq!(state.out.len(), effects_after_first);
        assert_eq!(state.ops.entries.len(), owners_after_first);
    }

    #[test]
    fn flight_id_max_is_issued_once_then_allocation_stutters() {
        let mut state = State::new(Config::memory("node-0"));
        state.next_flight = u64::MAX;

        assert_eq!(state.allocate_flight(), Some(u64::MAX));
        assert!(state.flights_exhausted);
        assert_eq!(state.next_flight, u64::MAX);
        assert_eq!(state.allocate_flight(), None);
        assert_eq!(state.allocate_flight(), None);
        assert_eq!(state.next_flight, u64::MAX);
    }

    #[test]
    fn exhausted_max_response_replay_is_a_strict_stutter() {
        let mut state = State::new(Config::memory("node-0"));
        state.node.members.next_heartbeat = Some(u64::MAX);
        let current = state.store(
            StoreReq::Get { key: "current".to_string() },
            Owner::Ignored,
        ).unwrap();
        state.next_op = u64::MAX;
        let old = state.store(
            StoreReq::Get { key: "last".to_string() },
            Owner::Ignored,
        ).unwrap();
        assert_eq!(old, u64::MAX);
        let _ = state.take_out();

        let response = StoreRes::Get {
            result: Err(StoreError::PreconditionFailed),
        };
        let first = state.on_event(crate::types::Event::Store {
            op: old,
            response: response.clone(),
            clock: 10,
        });
        assert!(first.is_empty());
        assert!(!state.ops.contains(&old));
        assert!(state.ops.contains(&current));

        let owner_count = state.ops.entries.len();
        let replay = state.on_event(crate::types::Event::Store {
            op: old,
            response,
            clock: 99,
        });
        assert!(replay.is_empty());
        assert_eq!(state.clock, 10);
        assert_eq!(state.ops.entries.len(), owner_count);
        assert_eq!(state.ops.get(&current), Some(&Owner::Ignored));
        assert!(state.ops_exhausted);
        assert_eq!(state.next_op, u64::MAX);
    }

    #[test]
    fn exhausted_client_work_returns_409_without_store_effect() {
        let mut state = State::new(Config::memory("node-0"));
        state.next_op = u64::MAX;
        state.ops_exhausted = true;
        state.node.members.next_heartbeat = Some(u64::MAX);
        let event = crate::types::Event::Request {
            clock: 1,
            request: crate::types::RequestEvent::Protocol(
                crate::types::Call {
                    id: 7,
                    kind: String::new(),
                    corr: "client".to_string(),
                    target: crate::target::Target::Origin(
                        "order".to_string(),
                    ),
                    request: Request::TaskGet(TaskGetReq {
                        id: "order:task".to_string(),
                    }),
                    action_kind: None,
                    now: 1,
                    pinned: false,
                },
            ),
        };

        let effects = state.on_event(event);
        assert!(!effects.iter().any(|effect| {
            matches!(effect, crate::types::Effect::Store { .. })
        }));
        assert!(effects.iter().any(|effect| {
            matches!(
                effect,
                crate::types::Effect::Reply {
                    response: Ok(crate::types::Answer::Step {
                        response: Response::TaskGet(response),
                        ..
                    }),
                    ..
                } if response.status == 409
            )
        }));
    }

    #[test]
    fn exhausted_flight_client_work_returns_409_without_store_effect() {
        let mut state = State::new(Config::memory("node-0"));
        state.next_flight = u64::MAX;
        state.flights_exhausted = true;
        state.node.members.next_heartbeat = Some(u64::MAX);
        let effects = state.on_event(crate::types::Event::Request {
            clock: 1,
            request: crate::types::RequestEvent::Protocol(
                crate::types::Call {
                    id: 8,
                    kind: String::new(),
                    corr: "client".to_string(),
                    target: crate::target::Target::Origin(
                        "order".to_string(),
                    ),
                    request: Request::TaskGet(TaskGetReq {
                        id: "order:task".to_string(),
                    }),
                    action_kind: None,
                    now: 1,
                    pinned: false,
                },
            ),
        });

        assert!(!effects.iter().any(|effect| {
            matches!(effect, crate::types::Effect::Store { .. })
        }));
        assert!(effects.iter().any(|effect| {
            matches!(
                effect,
                crate::types::Effect::Reply {
                    response: Ok(crate::types::Answer::Step {
                        response: Response::TaskGet(response),
                        ..
                    }),
                    ..
                } if response.status == 409
            )
        }));
        assert!(state.flights.inflight.entries.is_empty());
    }

    #[test]
    fn exhausted_internal_timer_rearms_without_external_effect() {
        use crate::handler_docs::{Firing, Flight, Phase, Work};
        use crate::target::Target;
        use crate::types::TimerKind;

        let mut state = State::new(Config::memory("node-0"));
        state.ops_exhausted = true;
        state.next_op = u64::MAX;
        state.timers.inflight = 1;
        let flight = Flight {
            id: 1,
            target: Target::Origin("order".to_string()),
            work: Work::Sweep { fired: None, now: 10 },
            attempt: 0,
            phase: Phase::Idle,
            firing: Some(Firing {
                key: "timer-key".to_string(),
                at: 5,
                kind: TimerKind::Origin,
                lag: 5,
            }),
            debug: false,
            idle: false,
        };

        state.op_exhausted(flight);
        let effects = state.take_out();
        assert_eq!(state.timers.inflight, 0);
        assert_eq!(state.timers.wheel.len(), 1);
        assert!(!effects.iter().any(|effect| {
            matches!(
                effect,
                crate::types::Effect::Store { .. }
                    | crate::types::Effect::Reply { .. }
                    | crate::types::Effect::Send { .. }
            )
        }));
    }

    #[test]
    fn timer_token_max_is_allocated_once_without_replay() {
        let mut state = State::new(Config::memory("node-0"));
        state.tokens = u64::MAX;
        state.tokens_exhausted = false;

        assert_eq!(state.token(), Some(u64::MAX));
        assert!(state.tokens_exhausted);
        assert_eq!(state.tokens, u64::MAX);
        assert_eq!(state.token(), None);
        assert_eq!(state.token(), None);
    }

    #[test]
    fn delayed_delete_identity_cannot_alias_after_token_exhaustion() {
        let mut state = State::new(Config::memory("node-0"));
        state.tokens = u64::MAX;
        let old = state.keys.timer_key("order", 42, u64::MAX - 1, "node-0");

        let current_token = state.token().expect("last fresh token");
        let current = state.keys.timer_key("order", 42, current_token, "node-0");
        assert_ne!(old, current);
        assert_eq!(state.token(), None);

        // No subsequent arm can recreate either identity: exhaustion occurs
        // before a timer Put or a document CAS can be issued.
        assert!(state.tokens_exhausted);
    }
}
