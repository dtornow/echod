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
use echod_concrete::store::StoreCallSpec;

verus! {

/// Who waits for a store call's answer.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Structural)]
pub enum Owner {
    Flight(FlightId),
    Members,
    Timers,
    Debug,
    /// The node's announcement being withdrawn: its answer ends the node.
    Leaving,
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

/// The process. `on_event` is the only step.
#[make_spec_type]
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
    pub next_op: OpId,
    pub next_flight: FlightId,
    pub ops: crate::verified::table::Table<OpId, Owner>,
    /// One step in progress per document, and the queue behind it.
    pub flights: Flights,
    pub debug: crate::debug::Debug,
    /// Whether the node keeps itself going: heartbeats and timers.
    pub loops: bool,
    pub stopping: bool,
    pub stopped: bool,
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
        next_op: 1,
        next_flight: 1,
        ops: Map::empty(),
        flights: crate::handler_docs::spec_flights_new(),
        debug: crate::debug::spec_debug_new(),
        loops: false,
        stopping: false,
        stopped: false,
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

/// Issue a store call; `owner` gets its answer.
pub open spec fn spec_store(s: S, call: StoreCallSpec, owner: Owner) -> (S, OpId) {
    let op = s.next_op;
    (S {
        next_op: s.next_op.wrapping_add(1),
        ops: s.ops.insert(op, owner),
        out: s.out.push(EffectSpec::Store { op, call }),
        ..s
    }, op)
}

/// A token no other arm of this node has used.
pub open spec fn spec_token(s: S) -> (S, u64) {
    (S { tokens: s.tokens.wrapping_add(0x9e37_79b9_7f4a_7c15), ..s }, s.tokens)
}

/// The name of a key in the bucket, armed by `by`.
pub open spec fn spec_key_name(s: S, k: AKey, by: Seq<char>) -> Seq<char> {
    if crate::verified::text::spec_starts_with(k.origin, "sched:"@) {
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
            next_op: 1,
            next_flight: 1,
            ops: crate::verified::table::Table::new(),
            flights: Flights::new(),
            debug: crate::debug::Debug::new(),
            loops: false,
            stopping: false,
            stopped: false,
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
    pub fn store(&mut self, call: StoreCall, owner: Owner) -> (op: OpId)
        ensures
            (final(self).deep_view(), op) == spec_store(old(self).deep_view(), call.deep_view(), owner),
    {
        let op = self.next_op;
        self.next_op = self.next_op.wrapping_add(1);
        self.ops.insert(op, owner);
        self.emit(Effect::Store { op, call });
        op
    }

    /// A token no other arm of this node has used.
    pub fn token(&mut self) -> (t: u64)
        ensures
            (final(self).deep_view(), t) == spec_token(old(self).deep_view()),
    {
        let t = self.tokens;
        self.tokens = self.tokens.wrapping_add(0x9e37_79b9_7f4a_7c15);
        t
    }

    /// The name of a key in the bucket, armed by `by`.
    pub fn key_name(&self, k: &Key, by: &str) -> (r: String)
        ensures
            r@ == spec_key_name(self.deep_view(), k@, by@),
    {
        match strip_prefix(k.origin.as_str(), "sched:") {
            Some(id) => {
                proof {
                    reveal_strlit("sched:");
                    assert(k.origin@.subrange(0, 6) =~= "sched:"@);
                    assert(k.origin@.skip(6) =~= id@);
                }
                self.keys.sched_timer_key(id.as_str(), k.at, k.token, by)
            },
            None => {
                proof {
                    reveal_strlit("sched:");
                }
                self.keys.timer_key(k.origin.as_str(), k.at, k.token, by)
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

    pub fn clear_wake(&mut self)
        ensures
            final(self).deep_view() == (S { last_wake: None, ..old(self).deep_view() }),
    {
        self.last_wake = None;
    }

    pub fn mark_stopped(&mut self)
        ensures
            final(self).deep_view() == (S { stopped: true, ..old(self).deep_view() }),
    {
        self.stopped = true;
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

    /// The node has withdrawn its announcement: nothing more to do.
    pub fn stopped(&self) -> bool {
        self.stopped
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
