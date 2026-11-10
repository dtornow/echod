//! A concrete document, read as part of the abstract store.
//!
//! The abstract service holds promises, tasks, and schedules. A concrete
//! node holds documents under keys. A key `o/<origin>` decodes to the objects
//! of that origin, a key `s/<id>` to one schedule. [`doc_rel`] says what one
//! document asserts of the abstract store; `relation::store_interpreted`
//! says it of every key. It is the Lean `StoreRep`: `Same abstract.store
//! physical.toAbstract`. The abstract model does not change; the
//! interpretation lives here, in the proof.
//!
//! [`request_agrees`] is one request against the document it names, on both
//! models: one abstract outcome, the same response, the next document
//! reading as the next store, every other key as before. The Lean
//! `refinement_handlers` proves this per handler. The promise handlers are
//! proved below. Cargo erases these bodies; a Verus run is what checks them.

use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::node::{
    DocV, Held, ObjV, PromV, spec_awaitable, spec_delay as c_delay, spec_fulfill_task, spec_handle,
    spec_held, spec_key, spec_new_obj, spec_offer_at, spec_opened, spec_origin_key, spec_origin_map,
    spec_parse_acc as c_parse_acc, spec_parse_u64 as c_parse_u64, spec_project_obj,
    spec_project_prom, spec_promise_create as c_promise_create, spec_promise_get as c_promise_get,
    spec_promise_res as c_promise_res, spec_promise_settle as c_promise_settle, spec_record,
    spec_schedule_key, spec_tag_is, spec_tag_key, spec_targeted, spec_task_record, spec_timer,
    spec_with_origin, TkV,
};
#[cfg(verus_keep_ghost)]
use crate::store::{spec_sat_add, spec_starts};
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::machine::{
    spec_delay as a_delay, spec_external, spec_first, spec_fulfill, spec_handler, spec_has_key,
    spec_has_target, spec_held as a_held, spec_is_external_tag, spec_is_global, spec_is_timer,
    spec_new_object, spec_out, spec_parse_acc as a_parse_acc, spec_parse_u64 as a_parse_u64,
    spec_project_promise, spec_project_task, spec_promise_create as a_promise_create,
    spec_promise_record, spec_promise_res as a_promise_res, spec_promise_settle as a_promise_settle,
    spec_settle, spec_task_record as a_task_record, SpecHeld, tag_delay, tag_external, tag_global,
    tag_scope, tag_target, tag_timer, tag_true,
};
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::trusted::{axiom_string_ext, axiom_string_realised, axiom_vec_ext};
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::view::{OutV, PromiseV, sat_add, ScheduleV, StoreV as AStore, TaskV};
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::ServerConfig;
#[cfg(verus_keep_ghost)]
use echod_rover::rover::comm::Time;
#[cfg(verus_keep_ghost)]
use echod_types::{
    origin, PromiseState, Request, Response, same_origin_spec, Schedule, Tags, TaskState, Value,
};

verus! {

broadcast use vstd::seq::group_seq_lemmas;

// ---------------------------------------------------------------------------
// Objects
// ---------------------------------------------------------------------------

/// A concrete promise and an abstract promise are the same promise. The
/// concrete model keeps callbacks and listeners in the order they came, each
/// once; the abstract model keeps the set.
pub open spec fn promise_rel(c: PromV, a: PromiseV) -> bool {
    &&& a.state == c.state
    &&& a.value == c.value
    &&& a.param == c.param
    &&& a.timeout_at == c.timeout_at
    &&& a.created_at == c.created_at
    &&& a.settled_at == c.settled_at
    &&& a.tags == c.tags
    &&& a.callbacks == c.callbacks.to_set()
    &&& a.listeners == c.listeners.to_set()
    &&& c.callbacks.no_duplicates()
    &&& c.listeners.no_duplicates()
}

/// The lease. The concrete task records when the lease ends; the abstract
/// task records when it was acquired, and the deadline is `acquired_at + ttl`.
/// An acquired task holds a lease and a ttl; every other task holds neither,
/// and no pid.
pub open spec fn lease_rel(c: TkV, a: TaskV) -> bool {
    &&& (c.lease_timeout_at is Some) == (c.ttl is Some)
    &&& (c.state == TaskState::Acquired) == (c.ttl is Some)
    &&& c.state != TaskState::Acquired ==> c.pid is None
    &&& match c.lease_timeout_at {
        Some(at) => sat_add(a.acquired_at, c.ttl.unwrap()) == at,
        None => true,
    }
}

pub open spec fn task_rel(c: TkV, a: TaskV) -> bool {
    &&& a.state == c.state
    &&& a.version == c.version
    &&& a.pid == c.pid
    &&& a.ttl == c.ttl
    &&& a.retry_timeout_at == c.retry_timeout_at
    &&& a.resumes == c.resumes
    &&& lease_rel(c, a)
}

/// A settled promise's task is fulfilled.
pub open spec fn settled_fulfilled(c: ObjV) -> bool {
    c.promise.state != PromiseState::Pending ==> match c.task {
        Some(t) => t.state == TaskState::Fulfilled,
        None => true,
    }
}

pub open spec fn object_rel(c: ObjV, promise: PromiseV, task: Option<TaskV>) -> bool {
    &&& promise_rel(c.promise, promise)
    &&& match (c.task, task) {
        (None, None) => true,
        (Some(ct), Some(at)) => task_rel(ct, at),
        _ => false,
    }
    &&& settled_fulfilled(c)
}

/// The abstract task of `id`, if the abstract store has one.
pub open spec fn abstract_task(s: AStore, id: Seq<char>) -> Option<TaskV> {
    if s.tasks.contains_key(id) { Some(s.tasks[id]) } else { None }
}

/// Every callback names a promise of the origin.
pub open spec fn callbacks_in(callbacks: Seq<Seq<char>>, origin_chars: Seq<char>) -> bool {
    forall|k: int| 0 <= k < callbacks.len() ==> origin(#[trigger] callbacks[k]) == origin_chars
}

/// The objects of one origin. Every id in the document belongs to the
/// origin, so does every callback, and for every id of the origin the two
/// sides agree on whether it exists and on what it is.
pub open spec fn origin_rel(map: Map<Seq<char>, ObjV>, origin_chars: Seq<char>, s: AStore) -> bool {
    &&& forall|id: Seq<char>| #[trigger] map.contains_key(id) ==> origin(id) == origin_chars
    &&& forall|id: Seq<char>| #[trigger] map.contains_key(id) ==> callbacks_in(map[id].promise.callbacks, origin_chars)
    &&& forall|id: Seq<char>|
        #![trigger origin(id)]
        origin(id) == origin_chars ==> {
            &&& s.promises.contains_key(id) == map.contains_key(id)
            &&& (map.contains_key(id) ==> object_rel(map[id], s.promises[id], abstract_task(s, id)))
            &&& (!map.contains_key(id) ==> !s.tasks.contains_key(id))
        }
}

// ---------------------------------------------------------------------------
// Schedules
// ---------------------------------------------------------------------------

pub open spec fn schedule_rel(c: Schedule, a: ScheduleV) -> bool {
    &&& a.id == c.id@
    &&& a.cron == c.cron@
    &&& a.promise_id == c.promise_id@
    &&& a.promise_timeout == c.promise_timeout
    &&& a.promise_param == c.promise_param
    &&& a.promise_tags == c.promise_tags
    &&& a.created_at == c.created_at
    &&& a.next_run_at == c.next_run_at
    &&& a.last_run_at == c.last_run_at
}

pub open spec fn slot_rel(slot: Option<Schedule>, id: Seq<char>, s: AStore) -> bool {
    &&& s.schedules.contains_key(id) == (slot is Some)
    &&& match slot {
        Some(schedule) => schedule.id@ == id && schedule_rel(schedule, s.schedules[id]),
        None => true,
    }
}

// ---------------------------------------------------------------------------
// Documents and the store
// ---------------------------------------------------------------------------

/// The abstract store holds finitely many objects.
pub open spec fn finite_store(s: AStore) -> bool {
    &&& s.promises.dom().finite()
    &&& s.tasks.dom().finite()
    &&& s.schedules.dom().finite()
}

pub open spec fn schedule_prefix() -> Seq<char> {
    seq!['s', '/']
}

pub open spec fn origin_prefix() -> Seq<char> {
    seq!['o', '/']
}

/// What the document under `key` says about the abstract store. An origin
/// document is a finite map; an empty one is then the empty document.
pub open spec fn doc_rel(key: Seq<char>, doc: DocV, s: AStore) -> bool {
    if spec_starts(key, schedule_prefix()) {
        match doc {
            DocV::Schedule(slot) => slot_rel(slot, key.skip(2), s),
            DocV::Origin(_) => false,
        }
    } else if spec_starts(key, origin_prefix()) {
        match doc {
            DocV::Origin(map) => map.dom().finite() && origin_rel(map, key.skip(2), s),
            DocV::Schedule(_) => false,
        }
    } else {
        match doc {
            DocV::Origin(map) => map.dom().finite() && map.dom().len() == 0,
            DocV::Schedule(slot) => slot is None,
        }
    }
}

// ---------------------------------------------------------------------------
// Handler agreement
// ---------------------------------------------------------------------------

/// What other keys said of `s`, they say of `next`.
pub open spec fn others_kept(key: Seq<char>, s: AStore, next: AStore) -> bool {
    forall|other: Seq<char>, doc: DocV|
        other != key && doc_rel(other, doc, s) ==> #[trigger] doc_rel(other, doc, next)
}

/// One request, on the document it names and on the abstract store. The
/// abstract handler has one outcome, it answers what the node answers, it
/// queues and sends nothing, the next document reads as the next store,
/// every other key reads as before, and the store stays finite.
pub open spec fn request_agrees(
    config: ServerConfig,
    request: Request,
    key: Seq<char>,
    doc: DocV,
    s: AStore,
    now: Time,
) -> bool {
    let (next, response) = spec_handle(doc, request, now);
    let outs = spec_handler(config, request, s, now);
    &&& outs.len() == 1
    &&& outs[0].resp == response
    &&& outs[0].work.len() == 0
    &&& outs[0].send.len() == 0
    &&& doc_rel(key, next, outs[0].next)
    &&& others_kept(key, s, outs[0].next)
    &&& finite_store(outs[0].next)
}

// ---------------------------------------------------------------------------
// Tags: the two lookups are one lookup
// ---------------------------------------------------------------------------

pub proof fn lemma_tag_is(tags: Tags, key: Seq<char>, value: Seq<char>, i: int)
    ensures
        spec_tag_is(tags, key, value, i) == (spec_first(tags, key, i) == Some(value)),
    decreases tags@.len() - i,
{
    if i < 0 || i >= tags@.len() {
    } else if tags@[i].0@ == key {
    } else {
        lemma_tag_is(tags, key, value, i + 1);
    }
}

pub proof fn lemma_tag_key(tags: Tags, key: Seq<char>, i: int)
    ensures
        spec_tag_key(tags, key, i) == (spec_first(tags, key, i) is Some),
    decreases tags@.len() - i,
{
    if i < 0 || i >= tags@.len() {
    } else if tags@[i].0@ == key {
    } else {
        lemma_tag_key(tags, key, i + 1);
    }
}

pub proof fn lemma_timer(tags: Tags)
    ensures
        spec_timer(tags) == spec_is_timer(tags),
{
    lemma_tag_is(tags, tag_timer(), tag_true(), 0);
    assert(seq!['r','e','s','o','n','a','t','e',':','t','i','m','e','r'] =~= tag_timer());
    assert(seq!['t','r','u','e'] =~= tag_true());
}

pub proof fn lemma_targeted(tags: Tags)
    ensures
        spec_targeted(tags) == spec_has_target(tags),
{
    lemma_tag_key(tags, tag_target(), 0);
    assert(seq!['r','e','s','o','n','a','t','e',':','t','a','r','g','e','t'] =~= tag_target());
}

/// `acc * 10 > m` exactly when `acc > m / 10`.
pub proof fn lemma_mul_ten(acc: nat, m: nat)
    ensures
        (acc * 10 > m) == (acc > m / 10),
{
    assert((m / 10) * 10 <= m && m < (m / 10) * 10 + 10) by (nonlinear_arith);
    if acc * 10 > m {
        assert(acc > m / 10) by (nonlinear_arith)
            requires
                acc * 10 > m,
                (m / 10) * 10 <= m,
        ;
    }
    if acc > m / 10 {
        assert(acc * 10 > m) by (nonlinear_arith)
            requires
                acc > m / 10,
                m < (m / 10) * 10 + 10,
        ;
    }
}

/// The two digit loops read the same number. The concrete loop walks an
/// index and checks the sum; the abstract loop drops the head and checks
/// the accumulator against the headroom.
pub proof fn lemma_parse_acc(s: Seq<char>, i: int, acc: nat)
    requires
        0 <= i <= s.len(),
        acc <= u64::MAX as nat,
    ensures
        c_parse_acc(s, i, acc) == a_parse_acc(s.skip(i), acc as u64),
    decreases s.len() - i,
{
    let rest = s.skip(i);
    assert(rest.len() == s.len() - i);
    if i >= s.len() {
        assert(rest.len() == 0);
    } else {
        assert(rest[0] == s[i]);
        if s[i] < '0' || s[i] > '9' {
        } else {
            let d = ((s[i] as u64) - ('0' as u64)) as nat;
            assert(d <= 9);
            let n = acc * 10 + d;
            let m = (u64::MAX - (d as u64)) as nat;
            lemma_mul_ten(acc, m);
            assert((n > u64::MAX as nat) == (acc * 10 > m));
            assert((acc > m / 10) == ((acc as u64) > (u64::MAX - (d as u64)) / 10));
            if n > u64::MAX as nat {
            } else {
                assert(rest.drop_first() =~= s.skip(i + 1));
                lemma_parse_acc(s, i + 1, n);
            }
        }
    }
}

pub proof fn lemma_parse(s: Seq<char>)
    ensures
        c_parse_u64(s) == a_parse_u64(s),
{
    if s.len() == 0 {
    } else {
        assert(s.skip(0) =~= s);
        lemma_parse_acc(s, 0, 0);
    }
}

pub proof fn lemma_delay_from(tags: Tags, i: int)
    ensures
        c_delay(tags, i) == match spec_first(tags, tag_delay(), i) {
            Some(text) => a_parse_u64(text),
            None => None,
        },
    decreases tags@.len() - i,
{
    assert(seq!['r', 'e', 's', 'o', 'n', 'a', 't', 'e', ':', 'd', 'e', 'l', 'a', 'y'] =~= tag_delay());
    if i < 0 || i >= tags@.len() {
    } else if tags@[i].0@ == tag_delay() {
        lemma_parse(tags@[i].1@);
    } else {
        lemma_delay_from(tags, i + 1);
    }
}

pub proof fn lemma_delay(tags: Tags)
    ensures
        c_delay(tags, 0) == a_delay(tags),
{
    lemma_delay_from(tags, 0);
}

pub proof fn lemma_offer(tags: Tags, now: Time)
    ensures
        spec_offer_at(tags, now) == match a_delay(tags) {
            Some(d) => if d > now { d } else { now },
            None => now,
        },
{
    lemma_delay(tags);
}

// ---------------------------------------------------------------------------
// Sequences as sets
// ---------------------------------------------------------------------------

pub proof fn lemma_empty_to_set()
    ensures
        Seq::<Seq<char>>::empty().to_set() == Set::<Seq<char>>::empty(),
{
    let empty = Seq::<Seq<char>>::empty();
    assert forall|y: Seq<char>| !(#[trigger] empty.to_set().contains(y)) by {
        if empty.contains(y) {
            let i = choose|i: int| 0 <= i < empty.len() && empty[i] == y;
            assert(false);
        }
    };
    assert(empty.to_set() =~= Set::<Seq<char>>::empty());
}

pub proof fn lemma_push_to_set(s: Seq<Seq<char>>, x: Seq<char>)
    ensures
        s.push(x).to_set() == s.to_set().insert(x),
{
    let pushed = s.push(x);
    assert forall|y: Seq<char>| pushed.to_set().contains(y) == s.to_set().insert(x).contains(y) by {
        if pushed.contains(y) {
            let i = choose|i: int| 0 <= i < pushed.len() && pushed[i] == y;
            if i < s.len() {
                assert(pushed[i] == s[i]);
                assert(s.contains(y));
            } else {
                assert(i == s.len());
                assert(pushed[i] == x);
                assert(y == x);
            }
        }
        if s.contains(y) {
            let i = choose|i: int| 0 <= i < s.len() && s[i] == y;
            assert(pushed[i] == s[i]);
            assert(pushed.contains(y));
        }
        if y == x {
            assert(pushed[s.len() as int] == x);
            assert(pushed.contains(y));
        }
    };
    assert(pushed.to_set() =~= s.to_set().insert(x));
}

pub proof fn lemma_contains_to_set(s: Seq<Seq<char>>, x: Seq<char>)
    ensures
        s.to_set().contains(x) == s.contains(x),
{
}

// ---------------------------------------------------------------------------
// Values: a value is its view
// ---------------------------------------------------------------------------

pub proof fn lemma_value_ext(a: Value, b: Value)
    requires
        a@ == b@,
    ensures
        a == b,
{
    let ah = a.headers@;
    let bh = b.headers@;
    assert(a@.headers == a.headers.deep_view());
    assert(b@.headers == b.headers.deep_view());
    assert(a.headers.deep_view().len() == ah.len());
    assert(b.headers.deep_view().len() == bh.len());
    assert(ah.len() == bh.len());
    assert forall|i: int| 0 <= i < ah.len() implies #[trigger] ah[i] == bh[i] by {
        assert(a.headers.deep_view()[i] == ah[i].deep_view());
        assert(b.headers.deep_view()[i] == bh[i].deep_view());
        assert(ah[i].deep_view() == bh[i].deep_view());
        assert(ah[i].0@ == bh[i].0@);
        assert(ah[i].1@ == bh[i].1@);
        axiom_string_ext(ah[i].0, bh[i].0);
        axiom_string_ext(ah[i].1, bh[i].1);
    };
    assert(ah =~= bh);
    axiom_vec_ext(a.headers, b.headers);
    match (a.data, b.data) {
        (Some(x), Some(y)) => {
            assert(x@ == y@);
            axiom_string_ext(x, y);
        },
        (None, None) => {},
        _ => {
            assert(false);
        },
    }
}

// ---------------------------------------------------------------------------
// Projection: a settled promise, on both sides
// ---------------------------------------------------------------------------

pub proof fn lemma_project_promise(c: PromV, a: PromiseV, now: Time)
    requires
        promise_rel(c, a),
    ensures
        promise_rel(spec_project_prom(c, now), spec_project_promise(a, now)),
{
    lemma_timer(c.tags);
}

pub proof fn lemma_project_object(c: ObjV, p: PromiseV, t: Option<TaskV>, now: Time)
    requires
        object_rel(c, p, t),
    ensures
        object_rel(
            spec_project_obj(c, now),
            spec_project_promise(p, now),
            match t {
                Some(task) => Some(spec_project_task(task, spec_project_promise(p, now))),
                None => None,
            },
        ),
{
    lemma_project_promise(c.promise, p, now);
    let seen = spec_project_promise(p, now);
    match (c.task, t) {
        (Some(ct), Some(at)) => {
            if seen.state != PromiseState::Pending && ct.state != TaskState::Fulfilled {
                assert(task_rel(spec_fulfill_task(ct), spec_fulfill(at)));
            } else {
                assert(task_rel(ct, at));
            }
        },
        _ => {},
    }
}

pub proof fn lemma_record(id: String, c: PromV, a: PromiseV)
    requires
        promise_rel(c, a),
    ensures
        spec_record(id, c) == spec_promise_record(id, a),
{
}

// ---------------------------------------------------------------------------
// Keys
// ---------------------------------------------------------------------------

pub proof fn lemma_starts_prefix(prefix: Seq<char>, rest: Seq<char>)
    ensures
        spec_starts(prefix + rest, prefix),
        (prefix + rest).skip(prefix.len() as int) == rest,
    decreases prefix.len(),
{
    let whole = prefix + rest;
    assert(whole.len() == prefix.len() + rest.len());
    if prefix.len() == 0 {
        assert(whole =~= rest);
        assert(whole.skip(0) =~= rest);
    } else {
        assert(whole[0] == prefix[0]);
        assert(whole.drop_first() =~= prefix.drop_first() + rest);
        lemma_starts_prefix(prefix.drop_first(), rest);
        assert(whole.skip(prefix.len() as int) =~= rest);
    }
}

/// A key with a prefix is the prefix and the rest.
pub proof fn lemma_starts_split(key: Seq<char>, prefix: Seq<char>)
    requires
        spec_starts(key, prefix),
    ensures
        key == prefix + key.skip(prefix.len() as int),
    decreases prefix.len(),
{
    let n = prefix.len() as int;
    if prefix.len() == 0 {
        assert(key =~= prefix + key.skip(0));
    } else {
        lemma_starts_split(key.drop_first(), prefix.drop_first());
        let whole = prefix + key.skip(n);
        assert(key.len() == whole.len());
        assert forall|i: int| 0 <= i < key.len() implies key[i] == whole[i] by {
            if i == 0 {
            } else if i < n {
                assert(key[i] == key.drop_first()[i - 1]);
                assert(key.drop_first()[i - 1] == (prefix.drop_first() + key.drop_first().skip(n - 1))[i - 1]);
                assert(prefix.drop_first()[i - 1] == prefix[i]);
            } else {
                assert(whole[i] == key.skip(n)[i - n]);
            }
        };
        assert(key =~= whole);
    }
}

pub proof fn lemma_origin_key(origin_chars: Seq<char>)
    ensures
        spec_starts(spec_origin_key(origin_chars), origin_prefix()),
        !spec_starts(spec_origin_key(origin_chars), schedule_prefix()),
        spec_origin_key(origin_chars).skip(2) == origin_chars,
{
    assert(spec_origin_key(origin_chars) == origin_prefix() + origin_chars);
    lemma_starts_prefix(origin_prefix(), origin_chars);
    let key = spec_origin_key(origin_chars);
    assert(key[0] == 'o');
    assert(schedule_prefix()[0] == 's');
}

/// An origin key reads as an origin document, by [`doc_rel`].
pub proof fn lemma_origin_doc(key: Seq<char>, origin_chars: Seq<char>, doc: DocV, s: AStore)
    requires
        key == spec_origin_key(origin_chars),
        doc_rel(key, doc, s),
    ensures
        doc is Origin,
        origin_rel(spec_origin_map(doc), origin_chars, s),
        spec_opened(doc) == doc,
{
    lemma_origin_key(origin_chars);
    match doc {
        DocV::Origin(map) => {
            assert(spec_opened(doc) == DocV::Origin(map));
        },
        DocV::Schedule(_) => {
            assert(false);
        },
    }
}

// ---------------------------------------------------------------------------
// The abstract store, changed at one origin
// ---------------------------------------------------------------------------

/// `next` agrees with `s` on every id of `origin_chars`.
pub open spec fn same_at_origin(s: AStore, next: AStore, origin_chars: Seq<char>) -> bool {
    forall|id: Seq<char>|
        #![trigger origin(id)]
        origin(id) == origin_chars ==> {
            &&& s.promises.contains_key(id) == next.promises.contains_key(id)
            &&& (s.promises.contains_key(id) ==> s.promises[id] == next.promises[id])
            &&& s.tasks.contains_key(id) == next.tasks.contains_key(id)
            &&& (s.tasks.contains_key(id) ==> s.tasks[id] == next.tasks[id])
        }
}

pub proof fn lemma_origin_rel_same(map: Map<Seq<char>, ObjV>, origin_chars: Seq<char>, s: AStore, next: AStore)
    requires
        origin_rel(map, origin_chars, s),
        same_at_origin(s, next, origin_chars),
    ensures
        origin_rel(map, origin_chars, next),
{
    assert forall|id: Seq<char>| #![trigger origin(id)] origin(id) == origin_chars implies {
        &&& next.promises.contains_key(id) == map.contains_key(id)
        &&& (map.contains_key(id) ==> object_rel(map[id], next.promises[id], abstract_task(next, id)))
        &&& (!map.contains_key(id) ==> !next.tasks.contains_key(id))
    } by {
        assert(abstract_task(next, id) == abstract_task(s, id));
    };
}

/// A store that changed only at ids of `changed` reads the same under every
/// key that is not that origin's key.
pub proof fn lemma_others_kept(s: AStore, next: AStore, changed: Seq<char>)
    requires
        next.schedules == s.schedules,
        forall|other: Seq<char>| other != changed ==> #[trigger] same_at_origin(s, next, other),
    ensures
        others_kept(spec_origin_key(changed), s, next),
{
    assert forall|other: Seq<char>, doc: DocV|
        other != spec_origin_key(changed) && doc_rel(other, doc, s) implies #[trigger] doc_rel(
        other,
        doc,
        next,
    ) by {
        if spec_starts(other, schedule_prefix()) {
        } else if spec_starts(other, origin_prefix()) {
            match doc {
                DocV::Origin(map) => {
                    let o = other.skip(2);
                    lemma_starts_split(other, origin_prefix());
                    assert(o != changed);
                    assert(same_at_origin(s, next, o));
                    lemma_origin_rel_same(map, o, s, next);
                },
                DocV::Schedule(_) => {},
            }
        } else {
        }
    };
}

/// A store that did not change reads as before under every key.
pub proof fn lemma_others_same(key: Seq<char>, s: AStore)
    ensures
        others_kept(key, s, s),
{
}

// ---------------------------------------------------------------------------
// Strings, records, tags: the two sides name the same things
// ---------------------------------------------------------------------------

/// The chosen string of some characters is the string of those characters.
pub proof fn lemma_string_view(chars: Seq<char>)
    ensures
        crate::model::spec_string(chars)@ == chars,
        echod_abstract_spec::machine::spec_string(chars)@ == chars,
        crate::model::spec_string(chars) == echod_abstract_spec::machine::spec_string(chars),
{
    reveal(crate::model::spec_string);
    reveal(echod_abstract_spec::machine::spec_string);
    axiom_string_realised(chars);
    axiom_string_ext(crate::model::spec_string(chars), echod_abstract_spec::machine::spec_string(chars));
}

/// A string is the chosen string of its characters.
pub proof fn lemma_string_of(s: String)
    ensures
        crate::model::spec_string(s@) == s,
        echod_abstract_spec::machine::spec_string(s@) == s,
{
    lemma_string_view(s@);
    axiom_string_ext(crate::model::spec_string(s@), s);
}

pub proof fn lemma_task_record(id: String, c: TkV, a: TaskV)
    requires
        task_rel(c, a),
    ensures
        spec_task_record(id, c) == a_task_record(id, a),
{
    match c.pid {
        Some(chars) => lemma_string_view(chars),
        None => {},
    }
}

pub proof fn lemma_external_tag(tags: Tags)
    ensures
        spec_tag_is(tags, seq!['r','e','s','o','n','a','t','e',':','e','x','t','e','r','n','a','l'], seq!['t','r','u','e'], 0)
            == spec_is_external_tag(tags),
{
    lemma_tag_is(tags, tag_external(), tag_true(), 0);
    assert(seq!['r','e','s','o','n','a','t','e',':','e','x','t','e','r','n','a','l'] =~= tag_external());
    assert(seq!['t','r','u','e'] =~= tag_true());
}

pub proof fn lemma_global_tag(tags: Tags)
    ensures
        spec_tag_is(tags, seq!['r','e','s','o','n','a','t','e',':','s','c','o','p','e'], seq!['g','l','o','b','a','l'], 0)
            == spec_is_global(tags),
{
    lemma_tag_is(tags, tag_scope(), tag_global(), 0);
    assert(seq!['r','e','s','o','n','a','t','e',':','s','c','o','p','e'] =~= tag_scope());
    assert(seq!['g','l','o','b','a','l'] =~= tag_global());
}

/// Awaitable on the node is external on the service.
pub proof fn lemma_awaitable(c: PromV, a: PromiseV)
    requires
        promise_rel(c, a),
    ensures
        spec_awaitable(c.tags) == spec_external(a),
{
    lemma_targeted(c.tags);
    lemma_timer(c.tags);
    lemma_external_tag(c.tags);
    lemma_global_tag(c.tags);
}

/// The two saturating additions are one.
pub proof fn lemma_sat_add(a: u64, b: u64)
    ensures
        spec_sat_add(a, b) == sat_add(a, b),
{
}

/// Two ids of one origin.
pub proof fn lemma_same_origin(a: Seq<char>, b: Seq<char>)
    ensures
        same_origin_spec(a, b) == (origin(a) == origin(b)),
{
}

// ---------------------------------------------------------------------------
// The held task, on both sides
// ---------------------------------------------------------------------------

/// `spec_held` on the document and on the store answer alike. An `Ok` is the
/// stored object, pending and acquired, related to the stored task.
pub proof fn lemma_held(
    map: Map<Seq<char>, ObjV>,
    origin_chars: Seq<char>,
    s: AStore,
    id: Seq<char>,
    version: u64,
    now: Time,
)
    requires
        origin_rel(map, origin_chars, s),
        origin(id) == origin_chars,
    ensures
        ({
            let (_, held) = spec_held(map, id, version, now);
            let a = a_held(s, id, version, now);
            &&& spec_held(map, id, version, now).0 == map
            &&& (held is Missing) == (a is Missing)
            &&& (held is Stale) == (a is Stale)
            &&& (held is Ok) == (a is Ok)
            &&& held is Ok ==> {
                &&& map.contains_key(id)
                &&& held->Ok_0 == map[id]
                &&& spec_project_obj(map[id], now) == map[id]
                &&& map[id].task is Some
                &&& map[id].task.unwrap().state == TaskState::Acquired
                &&& map[id].promise.state == PromiseState::Pending
                &&& s.tasks.contains_key(id)
                &&& s.promises.contains_key(id)
                &&& a->Ok_0 == s.tasks[id]
                &&& task_rel(map[id].task.unwrap(), s.tasks[id])
                &&& promise_rel(map[id].promise, s.promises[id])
                &&& spec_project_promise(s.promises[id], now) == s.promises[id]
            }
        }),
{
    if !map.contains_key(id) {
        assert(!s.promises.contains_key(id));
        assert(!s.tasks.contains_key(id));
    } else {
        let obj = map[id];
        let p = s.promises[id];
        let t = abstract_task(s, id);
        assert(object_rel(obj, p, t));
        lemma_project_object(obj, p, t, now);
        let seen = spec_project_obj(obj, now);
        let q = spec_project_promise(p, now);
        assert(promise_rel(seen.promise, q));
        match (obj.task, t) {
            (None, None) => {
                assert(!s.tasks.contains_key(id));
            },
            (Some(ct), Some(at)) => {
                assert(s.tasks.contains_key(id));
                assert(s.tasks[id] == at);
                let seen_c = seen.task.unwrap();
                let seen_a = spec_project_task(at, q);
                assert(task_rel(seen_c, seen_a));
                if seen_c.state == TaskState::Acquired && seen_c.version == version && seen.promise.state == PromiseState::Pending {
                    assert(q.state == PromiseState::Pending);
                    assert(p.state == PromiseState::Pending);
                    assert(obj.promise.state == PromiseState::Pending);
                    assert(seen.promise == obj.promise);
                    assert(seen.task == obj.task);
                    assert(seen == obj);
                    assert(q == p);
                    assert(seen_a == at);
                } else {
                }
            },
            _ => {
                assert(false);
            },
        }
    }
}

// ---------------------------------------------------------------------------
// Keys of schedules; stores changed within one origin
// ---------------------------------------------------------------------------

pub proof fn lemma_schedule_key(id: Seq<char>)
    ensures
        spec_starts(spec_schedule_key(id), schedule_prefix()),
        spec_schedule_key(id).skip(2) == id,
{
    assert(spec_schedule_key(id) == schedule_prefix() + id);
    lemma_starts_prefix(schedule_prefix(), id);
}

/// A schedule key reads as a schedule slot, by [`doc_rel`].
pub proof fn lemma_schedule_doc(key: Seq<char>, id: Seq<char>, doc: DocV, s: AStore)
    requires
        key == spec_schedule_key(id),
        doc_rel(key, doc, s),
    ensures
        doc is Schedule,
        slot_rel(doc->Schedule_0, id, s),
{
    lemma_schedule_key(id);
}

/// A store that changed only at one schedule reads the same under every
/// other key.
pub proof fn lemma_others_kept_schedule(s: AStore, next: AStore, changed: Seq<char>)
    requires
        next.promises == s.promises,
        next.tasks == s.tasks,
        forall|other: Seq<char>|
            other != changed ==> #[trigger] next.schedules.contains_key(other) == s.schedules.contains_key(other)
                && (s.schedules.contains_key(other) ==> next.schedules[other] == s.schedules[other]),
    ensures
        others_kept(spec_schedule_key(changed), s, next),
{
    lemma_schedule_key(changed);
    assert forall|other: Seq<char>, doc: DocV|
        other != spec_schedule_key(changed) && doc_rel(other, doc, s) implies #[trigger] doc_rel(
        other,
        doc,
        next,
    ) by {
        if spec_starts(other, schedule_prefix()) {
            let id = other.skip(2);
            lemma_starts_split(other, schedule_prefix());
            assert(id != changed);
            assert(next.schedules.contains_key(id) == s.schedules.contains_key(id));
        } else if spec_starts(other, origin_prefix()) {
            match doc {
                DocV::Origin(map) => {
                    let o = other.skip(2);
                    assert forall|id: Seq<char>| #![trigger origin(id)] origin(id) == o implies {
                        &&& s.promises.contains_key(id) == next.promises.contains_key(id)
                        &&& (s.promises.contains_key(id) ==> s.promises[id] == next.promises[id])
                        &&& s.tasks.contains_key(id) == next.tasks.contains_key(id)
                        &&& (s.tasks.contains_key(id) ==> s.tasks[id] == next.tasks[id])
                    } by {};
                    lemma_origin_rel_same(map, o, s, next);
                },
                DocV::Schedule(_) => {},
            }
        } else {
        }
    };
}

/// `next` agrees with `s` on every id outside `origin_chars`.
pub open spec fn changed_within(s: AStore, next: AStore, origin_chars: Seq<char>) -> bool {
    forall|id: Seq<char>|
        #![trigger origin(id)]
        origin(id) != origin_chars ==> {
            &&& s.promises.contains_key(id) == next.promises.contains_key(id)
            &&& (s.promises.contains_key(id) ==> s.promises[id] == next.promises[id])
            &&& s.tasks.contains_key(id) == next.tasks.contains_key(id)
            &&& (s.tasks.contains_key(id) ==> s.tasks[id] == next.tasks[id])
        }
}

/// A store changed within one origin reads the same under every other key.
pub proof fn lemma_others_kept_within(s: AStore, next: AStore, origin_chars: Seq<char>)
    requires
        next.schedules == s.schedules,
        changed_within(s, next, origin_chars),
    ensures
        others_kept(spec_origin_key(origin_chars), s, next),
{
    assert forall|other: Seq<char>| other != origin_chars implies #[trigger] same_at_origin(s, next, other) by {
        assert forall|id: Seq<char>| #![trigger origin(id)] origin(id) == other implies {
            &&& s.promises.contains_key(id) == next.promises.contains_key(id)
            &&& (s.promises.contains_key(id) ==> s.promises[id] == next.promises[id])
            &&& s.tasks.contains_key(id) == next.tasks.contains_key(id)
            &&& (s.tasks.contains_key(id) ==> s.tasks[id] == next.tasks[id])
        } by {
            assert(origin(id) != origin_chars);
        };
    };
    lemma_others_kept(s, next, origin_chars);
}

/// An origin document whose map is related reads as the store.
pub proof fn lemma_origin_reads(key: Seq<char>, origin_chars: Seq<char>, map: Map<Seq<char>, ObjV>, s: AStore)
    requires
        key == spec_origin_key(origin_chars),
        map.dom().finite(),
        origin_rel(map, origin_chars, s),
    ensures
        doc_rel(key, DocV::Origin(map), s),
{
    lemma_origin_key(origin_chars);
}

/// Replacing one object on both sides, with the abstract task kept, removed,
/// or inserted as the concrete task says.
pub proof fn lemma_origin_update(
    map: Map<Seq<char>, ObjV>,
    origin_chars: Seq<char>,
    s: AStore,
    id: Seq<char>,
    obj: ObjV,
    p: PromiseV,
    t: Option<TaskV>,
    next: AStore,
)
    requires
        origin_rel(map, origin_chars, s),
        origin(id) == origin_chars,
        object_rel(obj, p, t),
        callbacks_in(obj.promise.callbacks, origin_chars),
        next.promises == s.promises.insert(id, p),
        next.tasks == match t {
            Some(task) => s.tasks.insert(id, task),
            None => s.tasks.remove(id),
        },
    ensures
        origin_rel(map.insert(id, obj), origin_chars, next),
{
    lemma_origin_insert(map, origin_chars, s, id, obj, p, t);
    let built = AStore {
        promises: s.promises.insert(id, p),
        tasks: match t {
            Some(task) => s.tasks.insert(id, task),
            None => s.tasks.remove(id),
        },
        ..s
    };
    assert(origin_rel(map.insert(id, obj), origin_chars, built));
    assert forall|other: Seq<char>| #![trigger origin(other)] origin(other) == origin_chars implies {
        &&& next.promises.contains_key(other) == map.insert(id, obj).contains_key(other)
        &&& (map.insert(id, obj).contains_key(other) ==> object_rel(
            map.insert(id, obj)[other],
            next.promises[other],
            abstract_task(next, other),
        ))
        &&& (!map.insert(id, obj).contains_key(other) ==> !next.tasks.contains_key(other))
    } by {
        assert(abstract_task(next, other) == abstract_task(built, other));
    };
}

// ---------------------------------------------------------------------------
// The promise handlers
// ---------------------------------------------------------------------------

pub proof fn lemma_new_object(timeout_at: u64, now: Time, param: Value, tags: Tags, runnable: bool)
    ensures
        ({
            let (p, t) = spec_new_object(timeout_at, now, now, param, tags, runnable);
            object_rel(spec_new_obj(timeout_at, now, param, tags, runnable), p, t)
        }),
{
    lemma_timer(tags);
    lemma_offer(tags, now);
    lemma_empty_to_set();
    let c = spec_new_obj(timeout_at, now, param, tags, runnable);
    let (p, t) = spec_new_object(timeout_at, now, now, param, tags, runnable);
    assert(promise_rel(c.promise, p));
    if runnable {
        assert(c.task is Some);
        assert(t is Some);
        assert(task_rel(c.task.unwrap(), t.unwrap()));
    }
}

/// Inserting the same object on both sides keeps the origin related.
pub proof fn lemma_origin_insert(
    map: Map<Seq<char>, ObjV>,
    origin_chars: Seq<char>,
    s: AStore,
    id: Seq<char>,
    obj: ObjV,
    p: PromiseV,
    t: Option<TaskV>,
)
    requires
        origin_rel(map, origin_chars, s),
        origin(id) == origin_chars,
        object_rel(obj, p, t),
        callbacks_in(obj.promise.callbacks, origin_chars),
    ensures
        ({
            let next = AStore {
                promises: s.promises.insert(id, p),
                tasks: match t {
                    Some(task) => s.tasks.insert(id, task),
                    None => s.tasks.remove(id),
                },
                ..s
            };
            origin_rel(map.insert(id, obj), origin_chars, next)
        }),
{
    let next = AStore {
        promises: s.promises.insert(id, p),
        tasks: match t {
            Some(task) => s.tasks.insert(id, task),
            None => s.tasks.remove(id),
        },
        ..s
    };
    let inserted = map.insert(id, obj);
    assert forall|other: Seq<char>| #[trigger] inserted.contains_key(other) implies origin(other)
        == origin_chars by {
        if other != id {
            assert(map.contains_key(other));
        }
    };
    assert forall|other: Seq<char>| #[trigger] inserted.contains_key(other) implies callbacks_in(
        inserted[other].promise.callbacks,
        origin_chars,
    ) by {
        if other != id {
            assert(map.contains_key(other));
            assert(inserted[other] == map[other]);
        }
    };
    assert forall|other: Seq<char>| #![trigger origin(other)] origin(other) == origin_chars implies {
        &&& next.promises.contains_key(other) == inserted.contains_key(other)
        &&& (inserted.contains_key(other) ==> object_rel(
            inserted[other],
            next.promises[other],
            abstract_task(next, other),
        ))
        &&& (!inserted.contains_key(other) ==> !next.tasks.contains_key(other))
    } by {
        if other == id {
            assert(inserted[id] == obj);
            assert(next.promises[id] == p);
            assert(abstract_task(next, id) == t);
        } else {
            assert(inserted.contains_key(other) == map.contains_key(other));
            assert(next.promises.contains_key(other) == s.promises.contains_key(other));
            assert(abstract_task(next, other) == abstract_task(s, other));
            if map.contains_key(other) {
                assert(inserted[other] == map[other]);
                assert(next.promises[other] == s.promises[other]);
            }
        }
    };
}

pub proof fn lemma_promise_get_agrees(
    config: ServerConfig,
    id: String,
    doc: DocV,
    s: AStore,
    now: Time,
)
    requires
        doc_rel(spec_origin_key(origin(id@)), doc, s),
        finite_store(s),
    ensures
        request_agrees(
            config,
            Request::PromiseGet(echod_types::PromiseGetReq { id }),
            spec_origin_key(origin(id@)),
            doc,
            s,
            now,
        ),
{
    let request = Request::PromiseGet(echod_types::PromiseGetReq { id });
    let o = origin(id@);
    let key = spec_origin_key(o);
    lemma_origin_doc(key, o, doc, s);
    let map = spec_origin_map(doc);
    assert(spec_handle(doc, request, now) == c_promise_get(doc, id, now));
    let outs = spec_handler(config, request, s, now);
    assert(origin_rel(map, o, s));
    assert(s.promises.contains_key(id@) == map.contains_key(id@));
    if !map.contains_key(id@) {
        assert(outs == spec_out(a_promise_res(404, None), s));
        assert(c_promise_get(doc, id, now) == (doc, c_promise_res(404, None)));
    } else {
        lemma_project_object(map[id@], s.promises[id@], abstract_task(s, id@), now);
        let seen = spec_project_obj(map[id@], now);
        let p = spec_project_promise(s.promises[id@], now);
        lemma_record(id, seen.promise, p);
        assert(outs == spec_out(a_promise_res(200, Some(spec_promise_record(id, p))), s));
        assert(c_promise_get(doc, id, now) == (doc, c_promise_res(200, Some(spec_record(id, seen.promise)))));
    }
    assert(outs[0].next == s);
    assert(doc_rel(key, doc, s));
    lemma_others_same(key, s);
}

pub proof fn lemma_promise_create_agrees(
    config: ServerConfig,
    req: echod_types::PromiseCreateReq,
    doc: DocV,
    s: AStore,
    now: Time,
)
    requires
        doc_rel(spec_origin_key(origin(req.id@)), doc, s),
        finite_store(s),
    ensures
        request_agrees(
            config,
            Request::PromiseCreate(req),
            spec_origin_key(origin(req.id@)),
            doc,
            s,
            now,
        ),
{
    let request = Request::PromiseCreate(req);
    let o = origin(req.id@);
    let key = spec_origin_key(o);
    lemma_origin_doc(key, o, doc, s);
    let map = spec_origin_map(doc);
    assert(spec_handle(doc, request, now) == c_promise_create(doc, req, now));
    let outs = spec_handler(config, request, s, now);
    assert(outs == a_promise_create(req, s, now));
    lemma_timer(req.tags);
    lemma_targeted(req.tags);
    if spec_timer(req.tags) && spec_targeted(req.tags) {
        assert(outs[0].next == s);
        assert(c_promise_create(doc, req, now) == (doc, c_promise_res(400, None)));
        lemma_others_same(key, s);
    } else if map.contains_key(req.id@) {
        assert(s.promises.contains_key(req.id@));
        lemma_project_object(map[req.id@], s.promises[req.id@], abstract_task(s, req.id@), now);
        let seen = spec_project_obj(map[req.id@], now);
        let p = spec_project_promise(s.promises[req.id@], now);
        lemma_record(req.id, seen.promise, p);
        assert(outs[0].next == s);
        assert(outs[0].resp == c_promise_create(doc, req, now).1);
        lemma_others_same(key, s);
    } else {
        assert(!s.promises.contains_key(req.id@));
        assert(!s.tasks.contains_key(req.id@));
        lemma_new_object(req.timeout_at, now, req.param, req.tags, spec_targeted(req.tags));
        let obj = spec_new_obj(req.timeout_at, now, req.param, req.tags, spec_targeted(req.tags));
        let (p, t) = spec_new_object(req.timeout_at, now, now, req.param, req.tags, spec_has_target(req.tags));
        lemma_record(req.id, obj.promise, p);
        let next = outs[0].next;
        assert(next.promises == s.promises.insert(req.id@, p));
        assert(next.schedules == s.schedules);
        let tasks = match t {
            Some(task) => s.tasks.insert(req.id@, task),
            None => s.tasks.remove(req.id@),
        };
        match t {
            Some(task) => {
                assert(next.tasks == s.tasks.insert(req.id@, task));
            },
            None => {
                assert(next.tasks == s.tasks);
                assert(s.tasks.remove(req.id@) =~= s.tasks);
            },
        }
        assert(next.tasks =~= tasks);
        assert(next == AStore { promises: s.promises.insert(req.id@, p), tasks, ..s });
        assert(callbacks_in(obj.promise.callbacks, o));
        lemma_origin_insert(map, o, s, req.id@, obj, p, t);
        assert(next.promises.dom() == s.promises.dom().insert(req.id@));
        assert(finite_store(next));
        assert(spec_with_origin(doc, map.insert(req.id@, obj)) == DocV::Origin(map.insert(req.id@, obj)));
        assert(map.insert(req.id@, obj).dom() == map.dom().insert(req.id@));
        lemma_origin_key(o);
        assert(origin_rel(map.insert(req.id@, obj), key.skip(2), next));
        assert(doc_rel(key, DocV::Origin(map.insert(req.id@, obj)), next));
        assert forall|other: Seq<char>| other != o implies #[trigger] same_at_origin(s, next, other) by {
            assert forall|id: Seq<char>| #![trigger origin(id)] origin(id) == other implies {
                &&& s.promises.contains_key(id) == next.promises.contains_key(id)
                &&& (s.promises.contains_key(id) ==> s.promises[id] == next.promises[id])
                &&& s.tasks.contains_key(id) == next.tasks.contains_key(id)
                &&& (s.tasks.contains_key(id) ==> s.tasks[id] == next.tasks[id])
            } by {
                assert(id != req.id@);
            };
        };
        lemma_others_kept(s, next, o);
    }
}

pub proof fn lemma_promise_settle_agrees(
    config: ServerConfig,
    req: echod_types::PromiseSettleReq,
    doc: DocV,
    s: AStore,
    now: Time,
)
    requires
        doc_rel(spec_origin_key(origin(req.id@)), doc, s),
        finite_store(s),
    ensures
        request_agrees(
            config,
            Request::PromiseSettle(req),
            spec_origin_key(origin(req.id@)),
            doc,
            s,
            now,
        ),
{
    let request = Request::PromiseSettle(req);
    let o = origin(req.id@);
    let key = spec_origin_key(o);
    lemma_origin_doc(key, o, doc, s);
    let map = spec_origin_map(doc);
    assert(spec_handle(doc, request, now) == c_promise_settle(doc, req, now));
    let outs = spec_handler(config, request, s, now);
    assert(outs == a_promise_settle(req, s, now));
    if !req.state.spec_settable() || !map.contains_key(req.id@) {
        assert(outs[0].next == s);
        if req.state.spec_settable() {
            assert(!s.promises.contains_key(req.id@));
            assert(outs[0].resp == a_promise_res(404, None));
            assert(c_promise_settle(doc, req, now) == (doc, c_promise_res(404, None)));
        } else {
            assert(outs[0].resp == a_promise_res(400, None));
            assert(c_promise_settle(doc, req, now) == (doc, c_promise_res(400, None)));
        }
        lemma_others_same(key, s);
    } else {
        assert(s.promises.contains_key(req.id@));
        let stored = s.promises[req.id@];
        let task = abstract_task(s, req.id@);
        lemma_project_object(map[req.id@], stored, task, now);
        let seen = spec_project_obj(map[req.id@], now);
        let p = spec_project_promise(stored, now);
        assert(promise_rel(seen.promise, p));
        if p.state != PromiseState::Pending {
            lemma_record(req.id, seen.promise, p);
            assert(outs[0].next == s);
            assert(outs[0].resp == c_promise_settle(doc, req, now).1);
            lemma_others_same(key, s);
        } else {
            // A pending projection is the stored promise itself.
            assert(seen.promise == map[req.id@].promise);
            assert(p == stored);
            assert(seen.task == map[req.id@].task);
            let promise = PromV {
                state: req.state,
                value: req.value,
                settled_at: Some(now),
                ..seen.promise
            };
            let c_task = match seen.task {
                Some(t) if t.state != TaskState::Fulfilled => Some(spec_fulfill_task(t)),
                other => other,
            };
            let obj = ObjV { promise, task: c_task };
            let n = spec_settle(s, req.id@, req.state, req.value, now);
            let q = PromiseV { state: req.state, value: req.value, settled_at: Some(now), ..stored };
            assert(promise_rel(promise, q));
            let a_task = match task {
                Some(t) => if t.state != TaskState::Fulfilled { Some(spec_fulfill(t)) } else { Some(t) },
                None => None,
            };
            assert(object_rel(obj, q, a_task));
            assert(n.promises == s.promises.insert(req.id@, q));
            assert(n.schedules == s.schedules);
            let tasks = match a_task {
                Some(t) => s.tasks.insert(req.id@, t),
                None => s.tasks.remove(req.id@),
            };
            match a_task {
                Some(t) => {
                    assert(s.tasks.contains_key(req.id@));
                    if s.tasks[req.id@].state != TaskState::Fulfilled {
                        assert(n.tasks == s.tasks.insert(req.id@, spec_fulfill(s.tasks[req.id@])));
                    } else {
                        assert(t == s.tasks[req.id@]);
                        assert(s.tasks.insert(req.id@, t) =~= s.tasks);
                    }
                },
                None => {
                    assert(!s.tasks.contains_key(req.id@));
                    assert(s.tasks.remove(req.id@) =~= s.tasks);
                },
            }
            assert(n.tasks =~= tasks);
            assert(n == AStore { promises: s.promises.insert(req.id@, q), tasks, ..s });
            assert(obj.promise.callbacks == map[req.id@].promise.callbacks);
            assert(callbacks_in(obj.promise.callbacks, o));
            lemma_origin_insert(map, o, s, req.id@, obj, q, a_task);
            assert(n.promises.dom() == s.promises.dom().insert(req.id@));
            assert(finite_store(n));
            lemma_record(req.id, obj.promise, q);
            assert(n.promises.contains_key(req.id@));
            assert(n.promises[req.id@] == q);
            assert(outs[0].resp == a_promise_res(200, Some(spec_promise_record(req.id, q))));
            assert(c_promise_settle(doc, req, now).1 == c_promise_res(200, Some(spec_record(req.id, obj.promise))));
            assert(outs[0].next == n);
            assert(c_promise_settle(doc, req, now).0 == spec_with_origin(doc, map.insert(req.id@, obj)));
            assert(map.insert(req.id@, obj).dom() == map.dom().insert(req.id@));
            assert(doc_rel(key, DocV::Origin(map.insert(req.id@, obj)), n));
            assert forall|other: Seq<char>| other != o implies #[trigger] same_at_origin(s, n, other) by {
                assert forall|id: Seq<char>| #![trigger origin(id)] origin(id) == other implies {
                    &&& s.promises.contains_key(id) == n.promises.contains_key(id)
                    &&& (s.promises.contains_key(id) ==> s.promises[id] == n.promises[id])
                    &&& s.tasks.contains_key(id) == n.tasks.contains_key(id)
                    &&& (s.tasks.contains_key(id) ==> s.tasks[id] == n.tasks[id])
                } by {
                    assert(id != req.id@);
                };
            };
            lemma_others_kept(s, n, o);
        }
    }
}

/// The three promise handlers agree, each on its own key.
pub proof fn lemma_promise_handlers_agree(
    config: ServerConfig,
    request: Request,
    doc: DocV,
    s: AStore,
    now: Time,
)
    requires
        spec_key(request) is Some,
        doc_rel(spec_key(request).unwrap(), doc, s),
        finite_store(s),
        match request {
            Request::PromiseGet(_) | Request::PromiseCreate(_) | Request::PromiseSettle(_) => true,
            _ => false,
        },
    ensures
        request_agrees(config, request, spec_key(request).unwrap(), doc, s, now),
{
    match request {
        Request::PromiseGet(q) => lemma_promise_get_agrees(config, q.id, doc, s, now),
        Request::PromiseCreate(q) => lemma_promise_create_agrees(config, q, doc, s, now),
        Request::PromiseSettle(q) => lemma_promise_settle_agrees(config, q, doc, s, now),
        _ => {},
    }
}

} // verus!
