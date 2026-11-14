//! Proof of Echod concrete-to-abstract trace refinement.
//!
//! All interpretation, handler-agreement, work-agreement, relation, and
//! forward-simulation machinery is private to this module.

use vstd::prelude::*;
use echod_types::{MAX_TIME, MAX_VERSION};
#[cfg(verus_keep_ghost)]
use echod_types::spec_deadline_bounded;

#[cfg(verus_keep_ghost)]
use echod_concrete_spec::Config as ConcreteConfig;

mod interpretation {
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
//! models: one abstract response, the same response, the next document
//! reading as the next store, every other key as before. The Lean
//! `refinement_handlers` proves this per handler. The promise handlers are
//! proved below. Cargo erases these bodies; a Verus run is what checks them.

use vstd::prelude::*;
use echod_types::{MAX_TIME, MAX_VERSION};
#[cfg(verus_keep_ghost)]
use echod_types::spec_deadline_bounded;

#[cfg(verus_keep_ghost)]
use echod_concrete_spec::state::{
    DocumentBodyV, Held, ObjV, PromV, spec_awaitable, spec_delay as c_delay, spec_fulfill_task, spec_handle,
    spec_held, spec_key, spec_new_obj, spec_offer_at, spec_opened, spec_origin_key, spec_workflow_map,
    spec_parse_acc as c_parse_acc, spec_parse_u64 as c_parse_u64, spec_project_obj,
    spec_project_prom, spec_promise_create as c_promise_create, spec_promise_get as c_promise_get,
    spec_promise_res as c_promise_res, spec_promise_settle as c_promise_settle, spec_record,
    spec_schedule_key, spec_tag_is, spec_tag_key, spec_targeted, spec_task_record, spec_timer,
    spec_with_workflow, TkV,
};
#[cfg(verus_keep_ghost)]
use echod_concrete_spec::state::{spec_sat_add, spec_starts};
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::state::{
    spec_delay as a_delay, spec_external, spec_first, spec_fulfill, spec_has_key, spec_has_target, spec_is_external_tag, spec_is_global, spec_is_timer, spec_new_object, spec_out, spec_parse_acc as a_parse_acc, spec_parse_u64 as a_parse_u64, spec_project_promise, spec_project_task, spec_promise_record, spec_promise_res as a_promise_res, spec_settle, spec_task_record as a_task_record, tag_delay, tag_external, tag_global, tag_scope, tag_target, tag_timer, tag_true,
};
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::state::{
    spec_handler, spec_held as a_held, spec_promise_create as a_promise_create, spec_promise_settle as a_promise_settle, SpecHeld,
};
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::axioms::{axiom_string_ext, axiom_string_realised, axiom_vec_ext};
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::state::{OutV, PromiseV, sat_add, ScheduleV, StoreV as AStore, TaskV};
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::Config as AbstractConfig;
#[cfg(verus_keep_ghost)]
use rover_spec::rover::comm::Time;
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
pub(crate) open spec fn promise_rel(c: PromV, a: PromiseV) -> bool {
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
pub(crate) open spec fn lease_rel(c: TkV, a: TaskV) -> bool {
    &&& (c.lease_timeout_at is Some) == (c.ttl is Some)
    &&& (c.state == TaskState::Acquired) == (c.ttl is Some)
    &&& c.state != TaskState::Acquired ==> c.pid is None
    &&& match c.lease_timeout_at {
        Some(at) => sat_add(a.acquired_at, c.ttl.unwrap()) == at,
        None => true,
    }
}

pub(crate) open spec fn task_rel(c: TkV, a: TaskV) -> bool {
    &&& a.state == c.state
    &&& a.version == c.version
    &&& a.pid == c.pid
    &&& a.ttl == c.ttl
    &&& a.retry_timeout_at == c.retry_timeout_at
    &&& a.resumes == c.resumes
    &&& lease_rel(c, a)
}

/// A settled promise's task is fulfilled.
pub(crate) open spec fn settled_fulfilled(c: ObjV) -> bool {
    c.promise.state != PromiseState::Pending ==> match c.task {
        Some(t) => t.state == TaskState::Fulfilled,
        None => true,
    }
}

pub(crate) open spec fn object_rel(c: ObjV, promise: PromiseV, task: Option<TaskV>) -> bool {
    &&& promise_rel(c.promise, promise)
    &&& match (c.task, task) {
        (None, None) => true,
        (Some(ct), Some(at)) => task_rel(ct, at),
        _ => false,
    }
    &&& settled_fulfilled(c)
}

/// The abstract task of `id`, if the abstract store has one.
pub(crate) open spec fn abstract_task(s: AStore, id: Seq<char>) -> Option<TaskV> {
    if s.tasks.contains_key(id) { Some(s.tasks[id]) } else { None }
}

/// Every callback names a promise of the origin.
pub(crate) open spec fn callbacks_in(callbacks: Seq<Seq<char>>, origin_chars: Seq<char>) -> bool {
    forall|k: int| 0 <= k < callbacks.len() ==> origin(#[trigger] callbacks[k]) == origin_chars
}

/// The objects of one origin. Every id in the document belongs to the
/// origin, so does every callback, and for every id of the origin the two
/// sides agree on whether it exists and on what it is.
pub(crate) open spec fn origin_rel(map: Map<Seq<char>, ObjV>, origin_chars: Seq<char>, s: AStore) -> bool {
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

pub(crate) open spec fn schedule_rel(c: Schedule, a: ScheduleV) -> bool {
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

pub(crate) open spec fn slot_rel(slot: Option<Schedule>, id: Seq<char>, s: AStore) -> bool {
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
pub(crate) open spec fn finite_store(s: AStore) -> bool {
    &&& s.promises.dom().finite()
    &&& s.tasks.dom().finite()
    &&& s.schedules.dom().finite()
}

pub(crate) open spec fn schedule_prefix() -> Seq<char> {
    seq!['s', '/']
}

pub(crate) open spec fn origin_prefix() -> Seq<char> {
    seq!['o', '/']
}

/// What the document under `key` says about the abstract store. An origin
/// document is a finite map; an empty one is then the empty document.
pub(crate) open spec fn doc_rel(key: Seq<char>, doc: DocumentBodyV, s: AStore) -> bool {
    if spec_starts(key, schedule_prefix()) {
        match doc {
            DocumentBodyV::Schedule(slot) => slot_rel(slot, key.skip(2), s),
            DocumentBodyV::Workflow(_) => false,
        }
    } else if spec_starts(key, origin_prefix()) {
        match doc {
            DocumentBodyV::Workflow(map) => map.dom().finite() && origin_rel(map, key.skip(2), s),
            DocumentBodyV::Schedule(_) => false,
        }
    } else {
        match doc {
            DocumentBodyV::Workflow(map) => map.dom().finite() && map.dom().len() == 0,
            DocumentBodyV::Schedule(slot) => slot is None,
        }
    }
}

// ---------------------------------------------------------------------------
// Handler agreement
// ---------------------------------------------------------------------------

/// What other keys said of `s`, they say of `next`.
pub(crate) open spec fn others_kept(key: Seq<char>, s: AStore, next: AStore) -> bool {
    forall|other: Seq<char>, doc: DocumentBodyV|
        other != key && doc_rel(other, doc, s) ==> #[trigger] doc_rel(other, doc, next)
}

/// One request, on the document it names and on the abstract store. The
/// abstract handler has one response, it answers what the node answers, it
/// queues and sends nothing, the next document reads as the next store,
/// every other key reads as before, and the store stays finite.
pub(crate) open spec fn request_agrees(
    config: AbstractConfig,
    request: Request,
    key: Seq<char>,
    doc: DocumentBodyV,
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

pub(crate) proof fn lemma_tag_is(tags: Tags, key: Seq<char>, value: Seq<char>, i: int)
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

pub(crate) proof fn lemma_tag_key(tags: Tags, key: Seq<char>, i: int)
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

pub(crate) proof fn lemma_timer(tags: Tags)
    ensures
        spec_timer(tags) == spec_is_timer(tags),
{
    lemma_tag_is(tags, tag_timer(), tag_true(), 0);
    assert(seq!['r','e','s','o','n','a','t','e',':','t','i','m','e','r'] =~= tag_timer());
    assert(seq!['t','r','u','e'] =~= tag_true());
}

pub(crate) proof fn lemma_targeted(tags: Tags)
    ensures
        spec_targeted(tags) == spec_has_target(tags),
{
    lemma_tag_key(tags, tag_target(), 0);
    assert(seq!['r','e','s','o','n','a','t','e',':','t','a','r','g','e','t'] =~= tag_target());
}

/// `acc * 10 > m` exactly when `acc > m / 10`.
pub(crate) proof fn lemma_mul_ten(acc: nat, m: nat)
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
pub(crate) proof fn lemma_parse_acc(s: Seq<char>, i: int, acc: nat)
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

pub(crate) proof fn lemma_parse(s: Seq<char>)
    ensures
        c_parse_u64(s) == a_parse_u64(s),
{
    if s.len() == 0 {
    } else {
        assert(s.skip(0) =~= s);
        lemma_parse_acc(s, 0, 0);
    }
}

pub(crate) proof fn lemma_delay_from(tags: Tags, i: int)
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

pub(crate) proof fn lemma_delay(tags: Tags)
    ensures
        c_delay(tags, 0) == a_delay(tags),
{
    lemma_delay_from(tags, 0);
}

pub(crate) proof fn lemma_offer(tags: Tags, now: Time)
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

pub(crate) proof fn lemma_empty_to_set()
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

pub(crate) proof fn lemma_push_to_set(s: Seq<Seq<char>>, x: Seq<char>)
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

pub(crate) proof fn lemma_contains_to_set(s: Seq<Seq<char>>, x: Seq<char>)
    ensures
        s.to_set().contains(x) == s.contains(x),
{
}

// ---------------------------------------------------------------------------
// Values: a value is its view
// ---------------------------------------------------------------------------

pub(crate) proof fn lemma_value_ext(a: Value, b: Value)
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

pub(crate) proof fn lemma_project_promise(c: PromV, a: PromiseV, now: Time)
    requires
        promise_rel(c, a),
    ensures
        promise_rel(spec_project_prom(c, now), spec_project_promise(a, now)),
{
    lemma_timer(c.tags);
}

pub(crate) proof fn lemma_project_object(c: ObjV, p: PromiseV, t: Option<TaskV>, now: Time)
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

pub(crate) proof fn lemma_record(id: String, c: PromV, a: PromiseV)
    requires
        promise_rel(c, a),
    ensures
        spec_record(id, c) == spec_promise_record(id, a),
{
}

// ---------------------------------------------------------------------------
// Keys
// ---------------------------------------------------------------------------

pub(crate) proof fn lemma_starts_prefix(prefix: Seq<char>, rest: Seq<char>)
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
pub(crate) proof fn lemma_starts_split(key: Seq<char>, prefix: Seq<char>)
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

pub(crate) proof fn lemma_origin_key(origin_chars: Seq<char>)
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
pub(crate) proof fn lemma_origin_doc(key: Seq<char>, origin_chars: Seq<char>, doc: DocumentBodyV, s: AStore)
    requires
        key == spec_origin_key(origin_chars),
        doc_rel(key, doc, s),
    ensures
        doc is Workflow,
        origin_rel(spec_workflow_map(doc), origin_chars, s),
        spec_opened(doc) == doc,
{
    lemma_origin_key(origin_chars);
    match doc {
        DocumentBodyV::Workflow(map) => {
            assert(spec_opened(doc) == DocumentBodyV::Workflow(map));
        },
        DocumentBodyV::Schedule(_) => {
            assert(false);
        },
    }
}

// ---------------------------------------------------------------------------
// The abstract store, changed at one origin
// ---------------------------------------------------------------------------

/// `next` agrees with `s` on every id of `origin_chars`.
pub(crate) open spec fn same_at_origin(s: AStore, next: AStore, origin_chars: Seq<char>) -> bool {
    forall|id: Seq<char>|
        #![trigger origin(id)]
        origin(id) == origin_chars ==> {
            &&& s.promises.contains_key(id) == next.promises.contains_key(id)
            &&& (s.promises.contains_key(id) ==> s.promises[id] == next.promises[id])
            &&& s.tasks.contains_key(id) == next.tasks.contains_key(id)
            &&& (s.tasks.contains_key(id) ==> s.tasks[id] == next.tasks[id])
        }
}

pub(crate) proof fn lemma_origin_rel_same(map: Map<Seq<char>, ObjV>, origin_chars: Seq<char>, s: AStore, next: AStore)
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
pub(crate) proof fn lemma_others_kept(s: AStore, next: AStore, changed: Seq<char>)
    requires
        next.schedules == s.schedules,
        forall|other: Seq<char>| other != changed ==> #[trigger] same_at_origin(s, next, other),
    ensures
        others_kept(spec_origin_key(changed), s, next),
{
    assert forall|other: Seq<char>, doc: DocumentBodyV|
        other != spec_origin_key(changed) && doc_rel(other, doc, s) implies #[trigger] doc_rel(
        other,
        doc,
        next,
    ) by {
        if spec_starts(other, schedule_prefix()) {
        } else if spec_starts(other, origin_prefix()) {
            match doc {
                DocumentBodyV::Workflow(map) => {
                    let o = other.skip(2);
                    lemma_starts_split(other, origin_prefix());
                    assert(o != changed);
                    assert(same_at_origin(s, next, o));
                    lemma_origin_rel_same(map, o, s, next);
                },
                DocumentBodyV::Schedule(_) => {},
            }
        } else {
        }
    };
}

/// A store that did not change reads as before under every key.
pub(crate) proof fn lemma_others_same(key: Seq<char>, s: AStore)
    ensures
        others_kept(key, s, s),
{
}

// ---------------------------------------------------------------------------
// Strings, records, tags: the two sides name the same things
// ---------------------------------------------------------------------------

/// The chosen string of some characters is the string of those characters.
pub(crate) proof fn lemma_string_view(chars: Seq<char>)
    ensures
        echod_concrete_spec::rover::spec_string(chars)@ == chars,
        echod_abstract_spec::state::spec_string(chars)@ == chars,
        echod_concrete_spec::rover::spec_string(chars) == echod_abstract_spec::state::spec_string(chars),
{
    reveal(echod_concrete_spec::rover::spec_string);
    reveal(echod_abstract_spec::state::spec_string);
    axiom_string_realised(chars);
    axiom_string_ext(echod_concrete_spec::rover::spec_string(chars), echod_abstract_spec::state::spec_string(chars));
}

/// A string is the chosen string of its characters.
pub(crate) proof fn lemma_string_of(s: String)
    ensures
        echod_concrete_spec::rover::spec_string(s@) == s,
        echod_abstract_spec::state::spec_string(s@) == s,
{
    lemma_string_view(s@);
    axiom_string_ext(echod_concrete_spec::rover::spec_string(s@), s);
}

pub(crate) proof fn lemma_task_record(id: String, c: TkV, a: TaskV)
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

pub(crate) proof fn lemma_external_tag(tags: Tags)
    ensures
        spec_tag_is(tags, seq!['r','e','s','o','n','a','t','e',':','e','x','t','e','r','n','a','l'], seq!['t','r','u','e'], 0)
            == spec_is_external_tag(tags),
{
    lemma_tag_is(tags, tag_external(), tag_true(), 0);
    assert(seq!['r','e','s','o','n','a','t','e',':','e','x','t','e','r','n','a','l'] =~= tag_external());
    assert(seq!['t','r','u','e'] =~= tag_true());
}

pub(crate) proof fn lemma_global_tag(tags: Tags)
    ensures
        spec_tag_is(tags, seq!['r','e','s','o','n','a','t','e',':','s','c','o','p','e'], seq!['g','l','o','b','a','l'], 0)
            == spec_is_global(tags),
{
    lemma_tag_is(tags, tag_scope(), tag_global(), 0);
    assert(seq!['r','e','s','o','n','a','t','e',':','s','c','o','p','e'] =~= tag_scope());
    assert(seq!['g','l','o','b','a','l'] =~= tag_global());
}

/// Awaitable on the node is external on the service.
pub(crate) proof fn lemma_awaitable(c: PromV, a: PromiseV)
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
pub(crate) proof fn lemma_sat_add(a: u64, b: u64)
    ensures
        spec_sat_add(a, b) == sat_add(a, b),
{
}

/// Two ids of one origin.
pub(crate) proof fn lemma_same_origin(a: Seq<char>, b: Seq<char>)
    ensures
        same_origin_spec(a, b) == (origin(a) == origin(b)),
{
}

// ---------------------------------------------------------------------------
// The held task, on both sides
// ---------------------------------------------------------------------------

/// `spec_held` on the document and on the store answer alike. An `Ok` is the
/// stored object, pending and acquired, related to the stored task.
pub(crate) proof fn lemma_held(
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

pub(crate) proof fn lemma_schedule_key(id: Seq<char>)
    ensures
        spec_starts(spec_schedule_key(id), schedule_prefix()),
        spec_schedule_key(id).skip(2) == id,
{
    assert(spec_schedule_key(id) == schedule_prefix() + id);
    lemma_starts_prefix(schedule_prefix(), id);
}

/// A schedule key reads as a schedule slot, by [`doc_rel`].
pub(crate) proof fn lemma_schedule_doc(key: Seq<char>, id: Seq<char>, doc: DocumentBodyV, s: AStore)
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
pub(crate) proof fn lemma_others_kept_schedule(s: AStore, next: AStore, changed: Seq<char>)
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
    assert forall|other: Seq<char>, doc: DocumentBodyV|
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
                DocumentBodyV::Workflow(map) => {
                    let o = other.skip(2);
                    assert forall|id: Seq<char>| #![trigger origin(id)] origin(id) == o implies {
                        &&& s.promises.contains_key(id) == next.promises.contains_key(id)
                        &&& (s.promises.contains_key(id) ==> s.promises[id] == next.promises[id])
                        &&& s.tasks.contains_key(id) == next.tasks.contains_key(id)
                        &&& (s.tasks.contains_key(id) ==> s.tasks[id] == next.tasks[id])
                    } by {};
                    lemma_origin_rel_same(map, o, s, next);
                },
                DocumentBodyV::Schedule(_) => {},
            }
        } else {
        }
    };
}

/// `next` agrees with `s` on every id outside `origin_chars`.
pub(crate) open spec fn changed_within(s: AStore, next: AStore, origin_chars: Seq<char>) -> bool {
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
pub(crate) proof fn lemma_others_kept_within(s: AStore, next: AStore, origin_chars: Seq<char>)
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
pub(crate) proof fn lemma_origin_reads(key: Seq<char>, origin_chars: Seq<char>, map: Map<Seq<char>, ObjV>, s: AStore)
    requires
        key == spec_origin_key(origin_chars),
        map.dom().finite(),
        origin_rel(map, origin_chars, s),
    ensures
        doc_rel(key, DocumentBodyV::Workflow(map), s),
{
    lemma_origin_key(origin_chars);
}

/// Replacing one object on both sides, with the abstract task kept, removed,
/// or inserted as the concrete task says.
pub(crate) proof fn lemma_origin_update(
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

pub(crate) proof fn lemma_new_object(timeout_at: u64, now: Time, param: Value, tags: Tags, runnable: bool)
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
pub(crate) proof fn lemma_origin_insert(
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

pub(crate) proof fn lemma_promise_get_agrees(
    config: AbstractConfig,
    id: String,
    doc: DocumentBodyV,
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
    let map = spec_workflow_map(doc);
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

pub(crate) proof fn lemma_promise_create_agrees(
    config: AbstractConfig,
    req: echod_types::PromiseCreateReq,
    doc: DocumentBodyV,
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
    let map = spec_workflow_map(doc);
    assert(spec_handle(doc, request, now) == c_promise_create(doc, req, now));
    let outs = spec_handler(config, request, s, now);
    assert(outs == a_promise_create(req, s, now));
    lemma_timer(req.tags);
    lemma_targeted(req.tags);
    if req.timeout_at > MAX_TIME || (spec_timer(req.tags) && spec_targeted(req.tags)) {
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
        assert(spec_with_workflow(doc, map.insert(req.id@, obj)) == DocumentBodyV::Workflow(map.insert(req.id@, obj)));
        assert(map.insert(req.id@, obj).dom() == map.dom().insert(req.id@));
        lemma_origin_key(o);
        assert(origin_rel(map.insert(req.id@, obj), key.skip(2), next));
        assert(doc_rel(key, DocumentBodyV::Workflow(map.insert(req.id@, obj)), next));
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

pub(crate) proof fn lemma_promise_settle_agrees(
    config: AbstractConfig,
    req: echod_types::PromiseSettleReq,
    doc: DocumentBodyV,
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
    let map = spec_workflow_map(doc);
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
            assert(c_promise_settle(doc, req, now).0 == spec_with_workflow(doc, map.insert(req.id@, obj)));
            assert(map.insert(req.id@, obj).dom() == map.dom().insert(req.id@));
            assert(doc_rel(key, DocumentBodyV::Workflow(map.insert(req.id@, obj)), n));
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
pub(crate) proof fn lemma_promise_handlers_agree(
    config: AbstractConfig,
    request: Request,
    doc: DocumentBodyV,
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

}

mod relation {
//! The simulation relation, in full.
//!
//! The abstract service holds one store. Each concrete node holds the
//! documents of the keys it owns, and one flight. The abstract store is
//! what the owners hold: under a key, the document its owner has cached, or
//! the empty document; and while the owner's flight is on that key, the
//! document that flight decides. A node decides from its cache, or from a
//! read of a key it has never written, which the store still holds absent.
//! So the decision is fixed the moment the flight begins, at the time the
//! handler runs with, and the abstract step is taken there. The store's
//! write, and the node's reply when the write lands, change nothing the
//! relation reads: the reply was put on the abstract network when the
//! flight began. [`related`] is that coupling, with the facts about caches,
//! flights, and store traffic that keep it.
//!
//! [`agreement`] is what remains of the handlers: one request, one due
//! step, or one occurrence, on a document and on the abstract store it
//! reads as, do the same thing. `interpretation` proves it for the promise
//! handlers. Cargo erases these bodies; a Verus run is what checks them.

use vstd::prelude::*;
use echod_types::{MAX_TIME, MAX_VERSION};
#[cfg(verus_keep_ghost)]
use echod_types::spec_deadline_bounded;

#[cfg(verus_keep_ghost)]
use super::interpretation::{doc_rel, finite_store, others_kept, request_agrees};
#[cfg(verus_keep_ghost)]
use echod_concrete_spec::{Config as ConcreteConfig, Spec as CModel};
#[cfg(verus_keep_ghost)]
use echod_concrete_spec::rover::{
    Message as CMessage, NodeV, Pid as CPid, spec_string, StoreV as CStore,
};
#[cfg(verus_keep_ghost)]
use echod_concrete_spec::state::{
    CachedV, DocumentBodyV, FlightV, JobV, NoteV, PendingV, spec_cached, spec_empty_body, spec_encode_body,
    spec_handle, spec_key, spec_occurrence, spec_origin_key, spec_owns, spec_read, spec_run_due,
};
#[cfg(verus_keep_ghost)]
use echod_concrete_spec::state::{
    Etag, spec_etag, spec_etag_chars, spec_find, spec_fnv, StoreReq, StoreRes,
};
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::state::{
    spec_handler,
};
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::state::{
    spec_create_if_absent,
};
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::rover::{Pid as APid, spec_run_timeout};
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::protocol::Message as AMessage;
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::state::{InternalV, StoreV as AStore};
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::{
    Config as AbstractConfig, Dispatch, Output, Proc as AProc, Spec as AModel,
};
#[cfg(verus_keep_ghost)]
use rover_spec::rover::comm::Envelope;
#[cfg(verus_keep_ghost)]
use rover_spec::rover::RoverSpec::{is_process, Spec, State};
#[cfg(verus_keep_ghost)]
use rover_spec::rover::comm::Sched;
#[cfg(verus_keep_ghost)]
use echod_types::{origin, Request, Response};

verus! {

// ---------------------------------------------------------------------------
// Shape
// ---------------------------------------------------------------------------

/// The node in slot `i`.
pub(crate) open spec fn node_at(world: State<CModel>, i: int) -> NodeV {
    world.process[i].1->Node_0
}

/// The store, in the slot after the nodes.
pub(crate) open spec fn store_at(fleet: ConcreteConfig, world: State<CModel>) -> CStore {
    world.process[fleet.nodes as int].1->Store_0
}

/// Slots `0 .. nodes` are the nodes, each at its own address; the last slot
/// is the store. The world `initial` builds has this shape and a step keeps it.
pub(crate) open spec fn shaped(fleet: ConcreteConfig, world: State<CModel>) -> bool {
    &&& world.process.len() == fleet.nodes + 1
    &&& forall|i: int|
        0 <= i < fleet.nodes ==> {
            &&& #[trigger] world.process[i].0 == CPid::Node(i as u64)
            &&& world.process[i].1 is Node
            &&& node_at(world, i).address == i
            &&& node_at(world, i).nodes == fleet.nodes
            &&& node_at(world, i).retry_timeout == fleet.retry_timeout
        }
    &&& world.process[fleet.nodes as int].0 == CPid::Store
    &&& world.process[fleet.nodes as int].1 is Store
}

/// The abstract world has the one service slot.
pub(crate) open spec fn single(world: State<AModel>) -> bool {
    world.process.len() == 1 && world.process[0].0 == APid::Service
}

pub(crate) open spec fn astate(world: State<AModel>) -> AProc {
    world.process[0].1
}

pub(crate) proof fn lemma_single_present(world: State<AModel>)
    requires
        single(world),
    ensures
        is_process(AModel, world, APid::Service),
{
    assert(AModel.outside() == APid::Outside);
    assert(world.process[0].0 == APid::Service);
}

// ---------------------------------------------------------------------------
// What a node holds, and what its flight decides
// ---------------------------------------------------------------------------

/// The document a node decides from: its cache, or the empty document.
pub(crate) open spec fn loaded(node: NodeV, key: Seq<char>) -> DocumentBodyV {
    match spec_cached(node, key) {
        Some(cached) => spec_read(key, cached.body),
        None => spec_empty_body(key),
    }
}

/// What `spec_decide` computes from a flight and the document it loaded,
/// at the node's retry timeout: the next document, the reply, the
/// occurrences born, the dispatches.
/// Opaque: it holds the whole handler semantics, read where a proof needs it.
#[verifier::opaque]
pub(crate) open spec fn decision(flight: FlightV, doc: DocumentBodyV, retry_timeout: u64) -> (
    DocumentBodyV,
    Option<Response>,
    Seq<PendingV>,
    Seq<NoteV>,
) {
    match flight.job {
        JobV::External(request) => {
            let (next, response) = spec_handle(doc, request, flight.now);
            (next, Some(response), Seq::empty(), Seq::empty())
        },
        JobV::Due => spec_run_due(doc, flight.now, retry_timeout),
        JobV::Occurrence(pending) => (
            spec_occurrence(doc, pending, flight.now),
            None,
            Seq::empty(),
            Seq::empty(),
        ),
    }
}

/// The document a node stands for under `key`: what its flight on that key
/// decides, else what it holds.
pub(crate) open spec fn intended(node: NodeV, key: Seq<char>) -> DocumentBodyV {
    match node.flight {
        Some(flight) if flight.key == key => decision(flight, loaded(node, key), node.retry_timeout).0,
        _ => loaded(node, key),
    }
}

/// The slot of the node that owns `key`.
pub(crate) open spec fn owner(fleet: ConcreteConfig, key: Seq<char>) -> int {
    (spec_fnv(key) % fleet.nodes) as int
}

/// The document the concrete world stands for under `key`.
pub(crate) open spec fn effective(fleet: ConcreteConfig, world: State<CModel>, key: Seq<char>) -> DocumentBodyV {
    if fleet.nodes == 0 {
        spec_empty_body(key)
    } else {
        intended(node_at(world, owner(fleet, key)), key)
    }
}

/// Lean's `StoreRep`: under every key, the concrete world reads as the
/// abstract store.
pub(crate) open spec fn store_interpreted(fleet: ConcreteConfig, world: State<CModel>, s: AStore) -> bool {
    forall|key: Seq<char>| #[trigger] doc_rel(key, effective(fleet, world, key), s)
}

// ---------------------------------------------------------------------------
// Occurrences
// ---------------------------------------------------------------------------

/// The occurrences a node's flight will append when its write lands.
pub(crate) open spec fn born_of(node: NodeV) -> Seq<PendingV> {
    match node.flight {
        Some(flight) => decision(flight, loaded(node, flight.key), node.retry_timeout).2,
        None => Seq::empty(),
    }
}

/// The occurrences a node owes: queued, or born in its flight.
pub(crate) open spec fn occurrences(node: NodeV) -> Seq<PendingV> {
    node.pending + born_of(node)
}

/// A concrete occurrence, as the abstract queue holds it.
pub(crate) open spec fn as_item(p: PendingV) -> Sched<InternalV> {
    Sched::Timer(
        p.at,
        InternalV::Occurrence {
            promise: p.promise,
            at: p.at,
            timeout: p.timeout,
            param: p.param,
            tags: p.tags,
        },
    )
}

pub(crate) open spec fn items(occurrences: Seq<PendingV>) -> Seq<Sched<InternalV>> {
    occurrences.map_values(|p: PendingV| as_item(p))
}

/// How many times `item` is owed by the nodes from slot `i` on.
pub(crate) open spec fn owed(fleet: ConcreteConfig, world: State<CModel>, item: Sched<InternalV>, i: int) -> nat
    decreases fleet.nodes - i,
{
    if i < 0 || i >= fleet.nodes {
        0
    } else {
        items(occurrences(node_at(world, i))).to_multiset().count(item) + owed(
            fleet,
            world,
            item,
            i + 1,
        )
    }
}

/// Every occurrence a node owes is queued at the service. The service may
/// hold more: an occurrence a node dropped stays queued there.
pub(crate) open spec fn pending_covered(fleet: ConcreteConfig, world: State<CModel>, state: AProc) -> bool {
    forall|item: Sched<InternalV>|
        #[trigger] owed(fleet, world, item, 0) <= state.pending.to_multiset().count(item)
}

// ---------------------------------------------------------------------------
// Flights
// ---------------------------------------------------------------------------

pub(crate) open spec fn reply_output(client: Seq<char>, id: u64, response: Response) -> Output {
    Output::Response { client: spec_string(client), id, response }
}

pub(crate) open spec fn note_output(note: NoteV) -> Output {
    match note {
        NoteV::Execute { id, version } => Output::Dispatch(Dispatch::Execute {
            id: spec_string(id),
            version,
        }),
        NoteV::Unblock { address, promise } => Output::Dispatch(Dispatch::Unblock {
            address: spec_string(address),
            promise,
        }),
    }
}

/// `output` was sent by the service to the outside.
pub(crate) open spec fn service_output(network: Seq<Envelope<APid, AMessage>>, output: Output) -> bool {
    exists|j: int|
        #![trigger network[j]]
        0 <= j < network.len() && network[j] == Envelope {
            sender: APid::Service,
            recipient: APid::Outside,
            message: AMessage::Output(output),
        }
}

/// The reply a flight will send, if it answers a caller.
pub(crate) open spec fn flight_reply(flight: FlightV, reply: Option<Response>) -> Option<
    (Seq<char>, u64, Response),
> {
    match (flight.caller, reply) {
        (Some((client, id)), Some(response)) => Some((client, id, response)),
        _ => None,
    }
}

/// What a node's flight will send is already on the abstract network.
pub(crate) open spec fn flight_outputs_covered(
    node: NodeV,
    network: Seq<Envelope<APid, AMessage>>,
) -> bool {
    match node.flight {
        None => true,
        Some(flight) => {
            let (_, reply, _, notes) = decision(flight, loaded(node, flight.key), node.retry_timeout);
            &&& match flight_reply(flight, reply) {
                Some((client, id, response)) => service_output(
                    network,
                    reply_output(client, id, response),
                ),
                None => true,
            }
            &&& forall|k: int|
                0 <= k < notes.len() ==> service_output(network, note_output(#[trigger] notes[k]))
        },
    }
}

/// The key a flight is on is the key its job names.
pub(crate) open spec fn job_keyed(flight: FlightV) -> bool {
    match flight.job {
        JobV::External(request) => flight.caller is Some && spec_key(request) == Some(flight.key),
        JobV::Due => flight.caller is None,
        JobV::Occurrence(pending) => flight.caller is None && flight.key == spec_origin_key(
            origin(pending.promise),
        ),
    }
}

pub(crate) open spec fn cached_etag(node: NodeV, key: Seq<char>) -> Option<Seq<char>> {
    match spec_cached(node, key) {
        Some(cached) => cached.etag,
        None => None,
    }
}

/// A flight is on a key the node owns, carries an op the node has issued,
/// and, once writing, carries what `spec_decide` computed from what the
/// node holds. A reading flight is on a key the node does not hold.
pub(crate) open spec fn flight_ok(node: NodeV) -> bool {
    match node.flight {
        None => true,
        Some(flight) => {
            let (next, reply, born, notes) = decision(flight, loaded(node, flight.key), node.retry_timeout);
            &&& spec_owns(node, flight.key)
            &&& flight.op < node.next_op
            &&& job_keyed(flight)
            &&& if !flight.writing {
                &&& flight.etag is None
                &&& spec_cached(node, flight.key) is None
            } else {
                &&& flight.etag == cached_etag(node, flight.key)
                &&& flight.decided == Some(spec_encode_body(next))
                &&& flight.born == born
                &&& flight.notify == notes
                &&& flight.reply == flight_reply(flight, reply)
            }
        },
    }
}

// ---------------------------------------------------------------------------
// Caches and the store
// ---------------------------------------------------------------------------

/// The bytes the store holds under `key`.
pub(crate) open spec fn physical(store: CStore, key: Seq<char>) -> Option<Seq<u8>> {
    match spec_find(store.entries, key, 0) {
        Some(i) => Some(store.entries[i].body),
        None => None,
    }
}

/// Node `i`'s write on `key` has landed and the node has not yet heard.
pub(crate) open spec fn applied_write(i: int, node: NodeV, store: CStore, key: Seq<char>) -> bool {
    match node.flight {
        Some(flight) => {
            &&& flight.key == key
            &&& flight.writing
            &&& store.seen.contains((CPid::Node(i as u64), flight.op))
        },
        None => false,
    }
}

/// A cached document is encoded, and the store holds the same bytes under
/// the etag the cache quotes. A cache entry without an etag is a key the
/// store holds absent.
pub(crate) open spec fn cache_entry_ok(key: Seq<char>, cached: CachedV, store: CStore) -> bool {
    &&& cached.body == spec_encode_body(spec_read(key, cached.body))
    &&& match cached.etag {
        Some(etag) => physical(store, key) == Some(cached.body) && etag == spec_etag_chars(
            cached.body,
        ),
        None => physical(store, key) is None,
    }
}

/// On every key node `i` owns, the store holds the write the node is
/// waiting to hear about, else agrees with the node's cache.
pub(crate) open spec fn cache_ok(i: int, node: NodeV, store: CStore) -> bool {
    forall|key: Seq<char>|
        spec_owns(node, key) ==> if applied_write(i, node, store, key) {
            physical(store, key) == node.flight.unwrap().decided
        } else {
            match #[trigger] spec_cached(node, key) {
                Some(cached) => cache_entry_ok(key, cached, store),
                None => physical(store, key) is None,
            }
        }
}

/// A node caches only keys it owns, each once.
pub(crate) open spec fn cache_owned(node: NodeV) -> bool {
    &&& forall|k: int|
        0 <= k < node.documents.len() ==> spec_owns(
            node,
            #[trigger] node.documents[k].key,
        )
    &&& forall|j: int, k: int|
        0 <= j < k < node.documents.len() ==> #[trigger] node.documents[j].key
            != #[trigger] node.documents[k].key
}

/// The store's entries name each key once.
pub(crate) open spec fn entries_distinct(store: CStore) -> bool {
    forall|j: int, k: int|
        0 <= j < k < store.entries.len() ==> #[trigger] store.entries[j].key
            != #[trigger] store.entries[k].key
}

pub(crate) open spec fn node_ok(i: int, node: NodeV, store: CStore) -> bool {
    &&& flight_ok(node)
    &&& cache_owned(node)
    &&& cache_ok(i, node, store)
}

// ---------------------------------------------------------------------------
// Store traffic
// ---------------------------------------------------------------------------

pub(crate) open spec fn flight_op(node: NodeV) -> Option<u64> {
    match node.flight {
        Some(flight) => Some(flight.op),
        None => None,
    }
}

/// The request a flight sent: a read of its key, or the conditional write of
/// what it decided.
pub(crate) open spec fn request_of(flight: FlightV) -> StoreReq {
    if !flight.writing {
        StoreReq::Get { key: spec_string(flight.key) }
    } else {
        match flight.etag {
            Some(chars) => StoreReq::PutIfMatch {
                key: spec_string(flight.key),
                body: echod_concrete_spec::rover::spec_bytes(flight.decided.unwrap()),
                etag: Etag(spec_string(chars)),
            },
            None => StoreReq::PutIfNoneMatch {
                key: spec_string(flight.key),
                body: echod_concrete_spec::rover::spec_bytes(flight.decided.unwrap()),
            },
        }
    }
}

/// The reply the store gives a flight's request, once the caches agree with
/// the store.
pub(crate) open spec fn outcome_of(flight: FlightV) -> StoreRes {
    if flight.writing {
        if flight.etag is Some { StoreRes::PutIfMatch { result: Ok(spec_etag(flight.decided.unwrap())) } } else { StoreRes::PutIfNoneMatch { result: Ok(spec_etag(flight.decided.unwrap())) } }
    } else {
        StoreRes::Get { result: Ok(None) }
    }
}

/// Every store request on the network is from a node, under an op that
/// node has issued. One the store has not answered is the node's open
/// flight's request. One under the open flight's op is that flight's request.
pub(crate) open spec fn requests_ok(fleet: ConcreteConfig, world: State<CModel>) -> bool {
    forall|k: int|
        0 <= k < world.network.len() ==> match (#[trigger] world.network[k]).message {
            CMessage::StoreReq { op, request } => {
                let env = world.network[k];
                &&& env.recipient == CPid::Store
                &&& env.sender is Node
                &&& {
                    let i = env.sender->Node_0 as int;
                    let node = node_at(world, i);
                    &&& 0 <= i < fleet.nodes
                    &&& op < node.next_op
                    &&& (flight_op(node) == Some(op) ==> request == request_of(node.flight.unwrap()))
                    &&& (!store_at(fleet, world).seen.contains((env.sender, op)) ==> flight_op(node)
                        == Some(op))
                }
            },
            _ => true,
        }
}

/// Every store reply on the network answers a node under an op the store
/// has executed. One under the node's open flight's op is the reply
/// [`outcome_of`] says.
pub(crate) open spec fn replies_ok(fleet: ConcreteConfig, world: State<CModel>) -> bool {
    forall|k: int|
        0 <= k < world.network.len() ==> match (#[trigger] world.network[k]).message {
            CMessage::StoreRes { op, response } => {
                let env = world.network[k];
                &&& env.sender == CPid::Store
                &&& env.recipient is Node
                &&& {
                    let i = env.recipient->Node_0 as int;
                    let node = node_at(world, i);
                    &&& 0 <= i < fleet.nodes
                    &&& store_at(fleet, world).seen.contains((env.recipient, op))
                    &&& (flight_op(node) == Some(op) ==> response == response_of(
                        node.flight.unwrap(),
                    ))
                }
            },
            _ => true,
        }
}

/// A request envelope under `(sender, op)` is on the network.
pub(crate) open spec fn requested(world: State<CModel>, sender: CPid, op: u64) -> bool {
    exists|k: int|
        #![trigger world.network[k]]
        0 <= k < world.network.len() && world.network[k].sender == sender
            && world.network[k].recipient == CPid::Store && world.network[k].message is StoreReq
            && world.network[k].message->StoreReq_op == op
}

/// Every op the store has executed was requested.
pub(crate) open spec fn seen_ok(fleet: ConcreteConfig, world: State<CModel>) -> bool {
    forall|pair: (CPid, u64)|
        #[trigger] store_at(fleet, world).seen.contains(pair) ==> requested(world, pair.0, pair.1)
}

/// The facts of the concrete world alone.
pub(crate) open spec fn inv(fleet: ConcreteConfig, world: State<CModel>) -> bool {
    &&& shaped(fleet, world)
    &&& entries_distinct(store_at(fleet, world))
    &&& forall|i: int|
        0 <= i < fleet.nodes ==> #[trigger] node_ok(i, node_at(world, i), store_at(fleet, world))
    &&& requests_ok(fleet, world)
    &&& replies_ok(fleet, world)
    &&& seen_ok(fleet, world)
}

// ---------------------------------------------------------------------------
// The boundary
// ---------------------------------------------------------------------------

/// `request` was injected at the service.
pub(crate) open spec fn service_request(
    network: Seq<Envelope<APid, AMessage>>,
    request: echod_abstract_spec::Call,
) -> bool {
    exists|j: int|
        #![trigger network[j]]
        0 <= j < network.len() && network[j] == Envelope {
            sender: APid::Outside,
            recipient: APid::Service,
            message: AMessage::Request(request),
        }
}

/// A client request on the concrete network has the same request on the service.
pub(crate) open spec fn carried_request(
    env: Envelope<CPid, CMessage>,
    network: Seq<Envelope<APid, AMessage>>,
) -> bool {
    match env.message {
        CMessage::Request(request) => env.sender != CPid::Outside || service_request(network, request),
        _ => true,
    }
}

/// An output addressed to the concrete outside was sent by the service.
pub(crate) open spec fn carried_output(
    env: Envelope<CPid, CMessage>,
    network: Seq<Envelope<APid, AMessage>>,
) -> bool {
    match env.message {
        CMessage::Output(output) => {
            env.recipient != CPid::Outside || service_output(network, output)
        },
        _ => true,
    }
}

pub(crate) open spec fn requests_covered(
    concrete: Seq<Envelope<CPid, CMessage>>,
    abstract_network: Seq<Envelope<APid, AMessage>>,
) -> bool {
    forall|i: int|
        #![trigger concrete[i]]
        0 <= i < concrete.len() ==> carried_request(concrete[i], abstract_network)
}

pub(crate) open spec fn outputs_covered(
    concrete: Seq<Envelope<CPid, CMessage>>,
    abstract_network: Seq<Envelope<APid, AMessage>>,
) -> bool {
    forall|i: int|
        #![trigger concrete[i]]
        0 <= i < concrete.len() ==> carried_output(concrete[i], abstract_network)
}

/// Clock, requests, and outputs: what an injected request and an observed
/// output need.
pub(crate) open spec fn coupled(concrete: State<CModel>, abstract_world: State<AModel>) -> bool {
    &&& abstract_world.now <= concrete.now
    &&& requests_covered(concrete.network, abstract_world.network)
    &&& outputs_covered(concrete.network, abstract_world.network)
}

/// The relation.
pub(crate) open spec fn related(fleet: ConcreteConfig, concrete: State<CModel>, abstract_world: State<AModel>) -> bool {
    &&& coupled(concrete, abstract_world)
    &&& single(abstract_world)
    &&& inv(fleet, concrete)
    &&& finite_store(astate(abstract_world).store)
    &&& store_interpreted(fleet, concrete, astate(abstract_world).store)
    &&& pending_covered(fleet, concrete, astate(abstract_world))
    &&& forall|i: int|
        0 <= i < fleet.nodes ==> flight_outputs_covered(
            #[trigger] node_at(concrete, i),
            abstract_world.network,
        )
}

// ---------------------------------------------------------------------------
// Agreement: the handlers, on a document and on the abstract store
// ---------------------------------------------------------------------------

/// Every request on the document it names, by `interpretation::request_agrees`.
pub(crate) open spec fn requests_agree(config: AbstractConfig) -> bool {
    forall|request: Request, key: Seq<char>, doc: DocumentBodyV, s: AStore, now: u64|
        spec_key(request) == Some(key) && doc_rel(key, doc, s) && finite_store(s) ==> #[trigger] request_agrees(
            config,
            request,
            key,
            doc,
            s,
            now,
        )
}

pub(crate) open spec fn note_sends(notes: Seq<NoteV>) -> Seq<(APid, AMessage)> {
    notes.map_values(|note: NoteV| (APid::Outside, AMessage::Output(note_output(note))))
}

/// The due step of one document: nothing is due, or one abstract timeout
/// result does the same, sends the same dispatches, queues the same
/// occurrences, and keeps the store finite.
pub(crate) open spec fn due_agrees(
    config: AbstractConfig,
    key: Seq<char>,
    doc: DocumentBodyV,
    state: AProc,
    now: u64,
) -> bool {
    let (next, _, born, notes) = spec_run_due(doc, now, config.retry_timeout);
    ||| next == doc && born.len() == 0 && notes.len() == 0
    ||| exists|j: int|
        #![trigger spec_run_timeout(config, state, now)[j]]
        {
            let results = spec_run_timeout(config, state, now);
            &&& 0 <= j < results.len()
            &&& results[j].send == note_sends(notes)
            &&& results[j].state.pending == state.pending + items(born)
            &&& doc_rel(key, next, results[j].state.store)
            &&& others_kept(key, state.store, results[j].state.store)
            &&& finite_store(results[j].state.store)
        }
}

pub(crate) open spec fn dues_agree(config: AbstractConfig) -> bool {
    forall|key: Seq<char>, doc: DocumentBodyV, state: AProc, now: u64|
        doc_rel(key, doc, state.store) && finite_store(state.store) ==> #[trigger] due_agrees(
            config,
            key,
            doc,
            state,
            now,
        )
}

/// One occurrence on its origin document: nothing happens, or the abstract
/// occurrence step does the same.
pub(crate) open spec fn occurrence_agrees(pending: PendingV, doc: DocumentBodyV, s: AStore, now: u64) -> bool {
    let key = spec_origin_key(origin(pending.promise));
    let next = spec_occurrence(doc, pending, now);
    ||| next == doc
    ||| {
        let out = spec_create_if_absent(
            s,
            pending.promise,
            pending.at,
            pending.timeout,
            pending.param,
            pending.tags,
            now,
        );
        &&& !out.not_due
        &&& out.work.len() == 0
        &&& out.send.len() == 0
        &&& doc_rel(key, next, out.next)
        &&& others_kept(key, s, out.next)
        &&& finite_store(out.next)
    }
}

pub(crate) open spec fn occurrences_agree() -> bool {
    forall|pending: PendingV, doc: DocumentBodyV, s: AStore, now: u64|
        doc_rel(spec_origin_key(origin(pending.promise)), doc, s) && finite_store(s)
            ==> #[trigger] occurrence_agrees(pending, doc, s, now)
}

/// Lean's `refinement_handlers`, as one statement.
pub(crate) open spec fn agreement(config: AbstractConfig) -> bool {
    requests_agree(config) && dues_agree(config) && occurrences_agree()
}

/// The abstract server's configuration a fleet implements: the service it
/// refines retries as the nodes do.
pub(crate) open spec fn abstract_config(concrete_config: ConcreteConfig) -> AbstractConfig {
    AbstractConfig { retry_timeout: concrete_config.retry_timeout }
}

pub open spec fn response_of(flight: FlightV) -> StoreRes {
    if flight.writing {
        match flight.etag {
            Some(_) => StoreRes::PutIfMatch {
                result: Ok(spec_etag(flight.decided.unwrap())),
            },
            None => StoreRes::PutIfNoneMatch {
                result: Ok(spec_etag(flight.decided.unwrap())),
            },
        }
    } else {
        StoreRes::Get { result: Ok(None) }
    }
}
} // verus!

}

mod requests {
//! The remaining request handlers agree, each on the document it names.
//!
//! `interpretation` proves promise get, create, and settle. This module proves
//! the callbacks and listeners, the task handlers, the heartbeat, the
//! suspend, the fence, and the schedule handlers, and gathers them into
//! [`lemma_requests_agree`]: every request with a key agrees on every
//! related, finite store. Cargo erases these bodies; a Verus run is what
//! checks them.

use vstd::prelude::*;
use echod_types::{MAX_TIME, MAX_VERSION};
#[cfg(verus_keep_ghost)]
use echod_types::spec_deadline_bounded;

#[cfg(verus_keep_ghost)]
use super::interpretation::{
    abstract_task, callbacks_in, changed_within, doc_rel, finite_store, lemma_awaitable,
    lemma_contains_to_set, lemma_empty_to_set, lemma_held, lemma_origin_doc, lemma_origin_reads,
    lemma_origin_update, lemma_others_kept_schedule, lemma_others_kept_within, lemma_others_same,
    lemma_project_object, lemma_promise_create_agrees, lemma_promise_handlers_agree,
    lemma_promise_settle_agrees, lemma_push_to_set, lemma_record, lemma_sat_add, lemma_schedule_doc,
    lemma_schedule_key, lemma_string_of, lemma_targeted, lemma_task_record, lemma_timer, object_rel,
    origin_rel, promise_rel, request_agrees, schedule_rel, slot_rel, task_rel,
};
#[cfg(verus_keep_ghost)]
use echod_concrete_spec::state::{
    DocumentBodyV, Held, ObjV, PromV, spec_acquire as c_acquire, spec_add_callbacks,
    spec_any_settled as c_any_settled, spec_awaitable, spec_bad_suspend, spec_distinct_awaited,
    spec_extend as c_extend, spec_fence as c_fence, spec_fence_check as c_fence_check,
    spec_fulfill_task, spec_handle, spec_heartbeat as c_heartbeat, spec_held, spec_key,
    spec_missing_awaited, spec_new_obj, spec_one_origin, spec_opened, spec_origin_key,
    spec_workflow_map, spec_project_obj, spec_promise_create as c_promise_create,
    spec_promise_res as c_promise_res, spec_promise_settle as c_promise_settle,
    spec_register_callback as c_register_callback, spec_register_listener as c_register_listener,
    spec_schedule_create as c_schedule_create, spec_schedule_delete as c_schedule_delete,
    spec_schedule_get as c_schedule_get, spec_schedule_key, spec_seen, spec_suspend as c_suspend,
    spec_targeted, spec_task_acquire as c_task_acquire, spec_task_continue as c_task_continue,
    spec_task_create as c_task_create, spec_task_fulfill as c_task_fulfill,
    spec_task_get as c_task_get, spec_task_halt as c_task_halt, spec_task_release as c_task_release,
    spec_timer, spec_unawaitable, spec_unlease as c_unlease, spec_with_workflow, TkV,
};
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::state::{
    spec_acquire as a_acquire, spec_claim_res, spec_external, spec_fence_res, spec_fulfill, spec_has_target, spec_is_timer, spec_out, spec_project_promise, spec_project_task, spec_promise_record, spec_promise_res as a_promise_res, spec_schedule_res, spec_schedule_value, spec_settle, spec_status_res, spec_task_get_res, spec_task_record as a_task_record, spec_unlease as a_unlease,
};
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::state::{
    spec_any_settled as a_any_settled, spec_awaited, spec_callbacks as a_callbacks, spec_extend as a_extend, spec_fence as a_fence, spec_handler, spec_heartbeat as a_heartbeat, spec_held as a_held, spec_promise_create as a_promise_create, spec_promise_settle as a_promise_settle, spec_refs_one_origin, spec_register_callback as a_register_callback, spec_register_listener as a_register_listener, spec_schedule_create as a_schedule_create, spec_suspend as a_suspend, spec_task_acquire as a_task_acquire, spec_task_continue as a_task_continue, spec_task_create as a_task_create, spec_task_fulfill as a_task_fulfill, spec_task_halt as a_task_halt, spec_task_release as a_task_release, spec_wrap_fence, SpecHeld,
};
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::axioms::axiom_string_ext;
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::state::{
    all_in_origin, distinct, OutV, PromiseV, sat_add, ScheduleV, StoreV as AStore, TaskV,
};
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::Config as AbstractConfig;
#[cfg(verus_keep_ghost)]
use rover_spec::rover::comm::Time;
#[cfg(verus_keep_ghost)]
use echod_types::{
    origin, PromiseRegisterCallbackReq, PromiseRes, PromiseState, Request, Response,
    same_origin_spec, Schedule, ScheduleCreateReq, ScheduleRes, StatusRes, TaskClaimRes,
    TaskFenceAction, TaskFenceInnerRes, TaskFenceRes, TaskGetRes, TaskRef, TaskState,
};

verus! {

broadcast use vstd::seq::group_seq_lemmas;

// ---------------------------------------------------------------------------
// Sequences
// ---------------------------------------------------------------------------

/// Pushing an absent element keeps a sequence free of duplicates.
pub(crate) proof fn lemma_push_no_duplicates(s: Seq<Seq<char>>, x: Seq<char>)
    requires
        s.no_duplicates(),
        !s.contains(x),
    ensures
        s.push(x).no_duplicates(),
{
    let pushed = s.push(x);
    assert forall|i: int, j: int| 0 <= i < pushed.len() && 0 <= j < pushed.len() && i != j implies pushed[i]
        != pushed[j] by {
        if i < s.len() && j < s.len() {
            assert(pushed[i] == s[i]);
            assert(pushed[j] == s[j]);
        } else if i < s.len() {
            assert(pushed[j] == x);
            assert(pushed[i] == s[i]);
            assert(s.contains(s[i]));
        } else {
            assert(pushed[i] == x);
            assert(pushed[j] == s[j]);
            assert(s.contains(s[j]));
        }
    };
}

/// Dropping the head keeps a sequence free of duplicates.
pub(crate) proof fn lemma_skip_no_duplicates(s: Seq<Seq<char>>)
    requires
        s.no_duplicates(),
        s.len() > 0,
    ensures
        s.skip(1).no_duplicates(),
        s.skip(1).to_set() == s.to_set().remove(s[0]),
        !s.skip(1).contains(s[0]),
{
    let rest = s.skip(1);
    assert forall|i: int, j: int| 0 <= i < rest.len() && 0 <= j < rest.len() && i != j implies rest[i]
        != rest[j] by {
        assert(rest[i] == s[i + 1]);
        assert(rest[j] == s[j + 1]);
    };
    assert forall|y: Seq<char>| rest.to_set().contains(y) == s.to_set().remove(s[0]).contains(y) by {
        if rest.contains(y) {
            let i = choose|i: int| 0 <= i < rest.len() && rest[i] == y;
            assert(s[i + 1] == y);
            assert(s.contains(y));
            assert(y != s[0]);
        }
        if s.contains(y) && y != s[0] {
            let i = choose|i: int| 0 <= i < s.len() && s[i] == y;
            assert(i != 0);
            assert(rest[i - 1] == y);
            assert(rest.contains(y));
        }
    };
    assert(rest.to_set() =~= s.to_set().remove(s[0]));
    if rest.contains(s[0]) {
        let i = choose|i: int| 0 <= i < rest.len() && rest[i] == s[0];
        assert(s[i + 1] == s[0]);
        assert(false);
    }
}

/// Adding a callback on both sides: a push when absent, a set insert.
pub(crate) proof fn lemma_add_callback(callbacks: Seq<Seq<char>>, set: Set<Seq<char>>, x: Seq<char>)
    requires
        callbacks.no_duplicates(),
        set == callbacks.to_set(),
    ensures
        ({
            let added = if callbacks.contains(x) { callbacks } else { callbacks.push(x) };
            &&& added.to_set() == set.insert(x)
            &&& added.no_duplicates()
        }),
{
    lemma_contains_to_set(callbacks, x);
    if callbacks.contains(x) {
        assert(set.insert(x) =~= set);
    } else {
        lemma_push_to_set(callbacks, x);
        lemma_push_no_duplicates(callbacks, x);
    }
}

// ---------------------------------------------------------------------------
// Stores kept at an id
// ---------------------------------------------------------------------------

/// Re-inserting what is stored changes nothing.
pub(crate) proof fn lemma_tasks_kept(s: AStore, id: Seq<char>)
    ensures
        s.tasks == match abstract_task(s, id) {
            Some(task) => s.tasks.insert(id, task),
            None => s.tasks.remove(id),
        },
{
    match abstract_task(s, id) {
        Some(task) => {
            assert(s.tasks.insert(id, task) =~= s.tasks);
        },
        None => {
            assert(s.tasks.remove(id) =~= s.tasks);
        },
    }
}

pub(crate) proof fn lemma_promises_kept(s: AStore, id: Seq<char>)
    requires
        s.promises.contains_key(id),
    ensures
        s.promises.insert(id, s.promises[id]) == s.promises,
{
    assert(s.promises.insert(id, s.promises[id]) =~= s.promises);
}

/// A store changed at one id of the origin is changed within the origin.
pub(crate) proof fn lemma_within_one(s: AStore, next: AStore, id: Seq<char>)
    requires
        forall|other: Seq<char>|
            other != id ==> #[trigger] next.promises.contains_key(other) == s.promises.contains_key(other)
                && (s.promises.contains_key(other) ==> next.promises[other] == s.promises[other]),
        forall|other: Seq<char>|
            other != id ==> #[trigger] next.tasks.contains_key(other) == s.tasks.contains_key(other)
                && (s.tasks.contains_key(other) ==> next.tasks[other] == s.tasks[other]),
    ensures
        changed_within(s, next, origin(id)),
{
    assert forall|other: Seq<char>| #![trigger origin(other)] origin(other) != origin(id) implies {
        &&& s.promises.contains_key(other) == next.promises.contains_key(other)
        &&& (s.promises.contains_key(other) ==> s.promises[other] == next.promises[other])
        &&& s.tasks.contains_key(other) == next.tasks.contains_key(other)
        &&& (s.tasks.contains_key(other) ==> s.tasks[other] == next.tasks[other])
    } by {
        assert(other != id);
    };
}

/// The finiteness of a store changed at one id.
pub(crate) proof fn lemma_finite_at(s: AStore, next: AStore, id: Seq<char>)
    requires
        finite_store(s),
        next.schedules == s.schedules,
        next.promises == s.promises || next.promises.dom() == s.promises.dom().insert(id),
        next.tasks == s.tasks || next.tasks.dom() == s.tasks.dom().insert(id),
    ensures
        finite_store(next),
{
}

// ---------------------------------------------------------------------------
// Callbacks and listeners
// ---------------------------------------------------------------------------

pub(crate) proof fn lemma_register_callback_agrees(
    config: AbstractConfig,
    req: PromiseRegisterCallbackReq,
    doc: DocumentBodyV,
    s: AStore,
    now: Time,
)
    requires
        doc_rel(spec_origin_key(origin(req.awaited@)), doc, s),
        finite_store(s),
    ensures
        request_agrees(
            config,
            Request::PromiseRegisterCallback(req),
            spec_origin_key(origin(req.awaited@)),
            doc,
            s,
            now,
        ),
{
    let request = Request::PromiseRegisterCallback(req);
    let awaited = req.awaited;
    let awaiter = req.awaiter;
    let o = origin(awaited@);
    let key = spec_origin_key(o);
    assert(spec_handle(doc, request, now) == c_register_callback(doc, awaited, awaiter, now));
    let outs = spec_handler(config, request, s, now);
    assert(outs == a_register_callback(awaited, awaiter, s, now));
    if awaited@ == awaiter@ || !same_origin_spec(awaited@, awaiter@) {
        assert(outs == spec_out(a_promise_res(400, None), s));
        assert(c_register_callback(doc, awaited, awaiter, now) == (doc, c_promise_res(400, None)));
        lemma_others_same(key, s);
    } else {
        assert(origin(awaiter@) == o);
        lemma_origin_doc(key, o, doc, s);
        let map = spec_workflow_map(doc);
        assert(doc == DocumentBodyV::Workflow(map));
        if !map.contains_key(awaited@) {
            assert(!s.promises.contains_key(awaited@));
            assert(outs == spec_out(a_promise_res(404, None), s));
            lemma_others_same(key, s);
        } else if !map.contains_key(awaiter@) {
            assert(s.promises.contains_key(awaited@));
            assert(!s.promises.contains_key(awaiter@));
            assert(outs == spec_out(a_promise_res(422, None), s));
            lemma_others_same(key, s);
        } else {
            let p0 = s.promises[awaited@];
            let w0 = s.promises[awaiter@];
            let ta = abstract_task(s, awaited@);
            lemma_project_object(map[awaited@], p0, ta, now);
            lemma_project_object(map[awaiter@], w0, abstract_task(s, awaiter@), now);
            let ao = spec_project_obj(map[awaited@], now);
            let wo = spec_project_obj(map[awaiter@], now);
            let p = spec_project_promise(p0, now);
            let w = spec_project_promise(w0, now);
            assert(promise_rel(ao.promise, p));
            assert(promise_rel(wo.promise, w));
            lemma_targeted(wo.promise.tags);
            lemma_awaitable(ao.promise, p);
            if !spec_targeted(wo.promise.tags) || !spec_awaitable(ao.promise.tags) {
                assert(outs == spec_out(a_promise_res(422, None), s));
                lemma_others_same(key, s);
            } else {
                lemma_record(awaited, ao.promise, p);
                let res = a_promise_res(200, Some(spec_promise_record(awaited, p)));
                assert(c_promise_res(200, Some(echod_concrete_spec::state::spec_record(awaited, ao.promise))) == res);
                if ao.promise.state == PromiseState::Pending && wo.promise.state == PromiseState::Pending {
                    assert(ao == map[awaited@]);
                    assert(p == p0);
                    let callbacks = if ao.promise.callbacks.contains(awaiter@) {
                        ao.promise.callbacks
                    } else {
                        ao.promise.callbacks.push(awaiter@)
                    };
                    lemma_add_callback(ao.promise.callbacks, p.callbacks, awaiter@);
                    let obj2 = ObjV { promise: PromV { callbacks, ..ao.promise }, ..ao };
                    let q = PromiseV { callbacks: p.callbacks.insert(awaiter@), ..p };
                    assert(promise_rel(obj2.promise, q));
                    assert(object_rel(obj2, q, ta));
                    assert forall|k: int| 0 <= k < callbacks.len() implies origin(#[trigger] callbacks[k]) == o by {
                        if k < ao.promise.callbacks.len() {
                            assert(callbacks[k] == ao.promise.callbacks[k]);
                        } else {
                            assert(callbacks[k] == awaiter@);
                        }
                    };
                    let next = AStore { promises: s.promises.insert(awaited@, q), ..s };
                    assert(outs == spec_out(res, next));
                    lemma_tasks_kept(s, awaited@);
                    lemma_origin_update(map, o, s, awaited@, obj2, q, ta, next);
                    assert(map.insert(awaited@, obj2).dom() == map.dom().insert(awaited@));
                    lemma_origin_reads(key, o, map.insert(awaited@, obj2), next);
                    assert(c_register_callback(doc, awaited, awaiter, now).0 == DocumentBodyV::Workflow(map.insert(awaited@, obj2)));
                    lemma_within_one(s, next, awaited@);
                    lemma_others_kept_within(s, next, o);
                    assert(next.promises.dom() == s.promises.dom().insert(awaited@));
                    lemma_finite_at(s, next, awaited@);
                } else {
                    assert(outs == spec_out(res, s));
                    lemma_others_same(key, s);
                }
            }
        }
    }
}

pub(crate) proof fn lemma_register_listener_agrees(
    config: AbstractConfig,
    req: echod_types::PromiseRegisterListenerReq,
    doc: DocumentBodyV,
    s: AStore,
    now: Time,
)
    requires
        doc_rel(spec_origin_key(origin(req.awaited@)), doc, s),
        finite_store(s),
    ensures
        request_agrees(
            config,
            Request::PromiseRegisterListener(req),
            spec_origin_key(origin(req.awaited@)),
            doc,
            s,
            now,
        ),
{
    let request = Request::PromiseRegisterListener(req);
    let awaited = req.awaited;
    let address = req.address;
    let o = origin(awaited@);
    let key = spec_origin_key(o);
    assert(spec_handle(doc, request, now) == c_register_listener(doc, awaited, address, now));
    let outs = spec_handler(config, request, s, now);
    assert(outs == a_register_listener(awaited, address, s, now));
    lemma_origin_doc(key, o, doc, s);
    let map = spec_workflow_map(doc);
    assert(doc == DocumentBodyV::Workflow(map));
    if !map.contains_key(awaited@) {
        assert(!s.promises.contains_key(awaited@));
        assert(outs == spec_out(a_promise_res(404, None), s));
        lemma_others_same(key, s);
    } else {
        let p0 = s.promises[awaited@];
        let ta = abstract_task(s, awaited@);
        lemma_project_object(map[awaited@], p0, ta, now);
        let ao = spec_project_obj(map[awaited@], now);
        let p = spec_project_promise(p0, now);
        assert(promise_rel(ao.promise, p));
        lemma_awaitable(ao.promise, p);
        if !spec_awaitable(ao.promise.tags) {
            assert(outs == spec_out(a_promise_res(422, None), s));
            lemma_others_same(key, s);
        } else {
            lemma_record(awaited, ao.promise, p);
            let res = a_promise_res(200, Some(spec_promise_record(awaited, p)));
            if ao.promise.state == PromiseState::Pending {
                assert(ao == map[awaited@]);
                assert(p == p0);
                let listeners = if ao.promise.listeners.contains(address@) {
                    ao.promise.listeners
                } else {
                    ao.promise.listeners.push(address@)
                };
                lemma_add_callback(ao.promise.listeners, p.listeners, address@);
                let obj2 = ObjV { promise: PromV { listeners, ..ao.promise }, ..ao };
                let q = PromiseV { listeners: p.listeners.insert(address@), ..p };
                assert(promise_rel(obj2.promise, q));
                assert(object_rel(obj2, q, ta));
                assert(obj2.promise.callbacks == map[awaited@].promise.callbacks);
                let next = AStore { promises: s.promises.insert(awaited@, q), ..s };
                assert(outs == spec_out(res, next));
                lemma_tasks_kept(s, awaited@);
                lemma_origin_update(map, o, s, awaited@, obj2, q, ta, next);
                assert(map.insert(awaited@, obj2).dom() == map.dom().insert(awaited@));
                lemma_origin_reads(key, o, map.insert(awaited@, obj2), next);
                assert(c_register_listener(doc, awaited, address, now).0 == DocumentBodyV::Workflow(map.insert(awaited@, obj2)));
                lemma_within_one(s, next, awaited@);
                lemma_others_kept_within(s, next, o);
                assert(next.promises.dom() == s.promises.dom().insert(awaited@));
                lemma_finite_at(s, next, awaited@);
            } else {
                assert(outs == spec_out(res, s));
                lemma_others_same(key, s);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Tasks
// ---------------------------------------------------------------------------

/// A projected object whose task is not fulfilled is the stored object: its
/// promise is pending, and so is the abstract projection.
pub(crate) proof fn lemma_unfulfilled_is_stored(obj: ObjV, p: PromiseV, t: Option<TaskV>, now: Time)
    requires
        object_rel(obj, p, t),
        obj.task is Some,
        spec_project_obj(obj, now).task.unwrap().state != TaskState::Fulfilled,
    ensures
        spec_project_obj(obj, now) == obj,
        obj.promise.state == PromiseState::Pending,
        spec_project_promise(p, now) == p,
        t is Some,
        spec_project_task(t.unwrap(), spec_project_promise(p, now)) == t.unwrap(),
{
    let seen = spec_project_obj(obj, now);
    let ct = obj.task.unwrap();
    if seen.promise.state != PromiseState::Pending {
        if ct.state != TaskState::Fulfilled {
            assert(seen.task == Some(spec_fulfill_task(ct)));
            assert(false);
        } else {
            assert(seen.task == obj.task);
            assert(false);
        }
    }
    assert(seen.promise.state == PromiseState::Pending);
    assert(obj.promise.state == PromiseState::Pending);
    assert(seen.promise == obj.promise);
    assert(seen.task == obj.task);
}

/// Acquiring on both sides relates.
pub(crate) proof fn lemma_acquire_rel(ct: TkV, at: TaskV, pid: Seq<char>, ttl: u64, now: Time)
    requires
        task_rel(ct, at),
    ensures
        task_rel(c_acquire(ct, pid, ttl, now), a_acquire(at, sat_add(at.version, 1), pid, ttl, now)),
{
    lemma_sat_add(ct.version, 1);
    lemma_sat_add(now, ttl);
}

pub(crate) proof fn lemma_task_get_agrees(config: AbstractConfig, id: String, doc: DocumentBodyV, s: AStore, now: Time)
    requires
        doc_rel(spec_origin_key(origin(id@)), doc, s),
        finite_store(s),
    ensures
        request_agrees(
            config,
            Request::TaskGet(echod_types::TaskGetReq { id }),
            spec_origin_key(origin(id@)),
            doc,
            s,
            now,
        ),
{
    let request = Request::TaskGet(echod_types::TaskGetReq { id });
    let o = origin(id@);
    let key = spec_origin_key(o);
    assert(spec_handle(doc, request, now) == c_task_get(doc, id, now));
    let outs = spec_handler(config, request, s, now);
    lemma_origin_doc(key, o, doc, s);
    let map = spec_workflow_map(doc);
    assert(doc == DocumentBodyV::Workflow(map));
    if !map.contains_key(id@) {
        assert(!s.promises.contains_key(id@));
        assert(!s.tasks.contains_key(id@));
        assert(outs == spec_out(spec_task_get_res(404, None), s));
    } else {
        let p = s.promises[id@];
        let ta = abstract_task(s, id@);
        lemma_project_object(map[id@], p, ta, now);
        let seen = spec_project_obj(map[id@], now);
        match (map[id@].task, ta) {
            (None, None) => {
                assert(!s.tasks.contains_key(id@));
                assert(outs == spec_out(spec_task_get_res(404, None), s));
            },
            (Some(ct), Some(at)) => {
                assert(s.tasks.contains_key(id@));
                let seen_c = seen.task.unwrap();
                let seen_a = spec_project_task(at, spec_project_promise(p, now));
                assert(task_rel(seen_c, seen_a));
                lemma_task_record(id, seen_c, seen_a);
                assert(outs == spec_out(spec_task_get_res(200, Some(a_task_record(id, seen_a))), s));
            },
            _ => {
                assert(false);
            },
        }
    }
    assert(outs[0].next == s);
    lemma_others_same(key, s);
}

pub(crate) proof fn lemma_task_create_agrees(
    config: AbstractConfig,
    req: echod_types::TaskCreateReq,
    doc: DocumentBodyV,
    s: AStore,
    now: Time,
)
    requires
        doc_rel(spec_origin_key(origin(req.action.id@)), doc, s),
        finite_store(s),
    ensures
        request_agrees(
            config,
            Request::TaskCreate(req),
            spec_origin_key(origin(req.action.id@)),
            doc,
            s,
            now,
        ),
{
    let request = Request::TaskCreate(req);
    let action = req.action;
    let x = action.id@;
    let o = origin(x);
    let key = spec_origin_key(o);
    let pid = req.pid;
    let ttl = req.ttl;
    assert(spec_handle(doc, request, now) == c_task_create(doc, pid, ttl, action, now));
    let outs = spec_handler(config, request, s, now);
    assert(outs == a_task_create(pid, ttl, action, s, now));
    lemma_targeted(action.tags);
    lemma_timer(action.tags);
    if ttl == 0 || ttl > MAX_TIME || action.timeout_at > MAX_TIME
        || !spec_targeted(action.tags) || spec_timer(action.tags) {
        assert(outs == spec_out(spec_claim_res(400, None, None), s));
        assert(c_task_create(doc, pid, ttl, action, now) == (doc, Response::TaskClaim(TaskClaimRes { status: 400, task: None, promise: None })));
        lemma_others_same(key, s);
    } else {
        lemma_origin_doc(key, o, doc, s);
        let map = spec_workflow_map(doc);
        assert(doc == DocumentBodyV::Workflow(map));
        let (doc1, created) = c_promise_create(doc, action, now);
        if map.contains_key(x) {
            assert(doc1 == doc);
            assert(s.promises.contains_key(x));
            let p = s.promises[x];
            let ta = abstract_task(s, x);
            lemma_project_object(map[x], p, ta, now);
            let seen = spec_project_obj(map[x], now);
            let seen_p = spec_project_promise(p, now);
            assert(promise_rel(seen.promise, seen_p));
            assert(seen.promise.tags == p.tags);
            lemma_targeted(seen.promise.tags);
            if !spec_targeted(seen.promise.tags) {
                assert(outs == spec_out(spec_claim_res(422, None, None), s));
                lemma_others_same(key, s);
            } else {
                match (map[x].task, ta) {
                    (None, None) => {
                        assert(!s.tasks.contains_key(x));
                        assert(seen.task is None);
                        assert(outs == spec_out(spec_claim_res(409, None, None), s));
                        lemma_others_same(key, s);
                    },
                    (Some(ct), Some(stored)) => {
                        assert(s.tasks.contains_key(x));
                        assert(s.tasks[x] == stored);
                        let t = seen.task.unwrap();
                        let seen_t = spec_project_task(stored, seen_p);
                        assert(task_rel(t, seen_t));
                        if t.state == TaskState::Fulfilled {
                            lemma_task_record(action.id, t, seen_t);
                            lemma_record(action.id, seen.promise, seen_p);
                            assert(outs[0].next == s);
                            lemma_others_same(key, s);
                        } else if t.state == TaskState::Pending && t.version >= MAX_VERSION {
                            assert(stored.version >= MAX_VERSION);
                            assert(outs == spec_out(spec_claim_res(409, None, None), s));
                            lemma_others_same(key, s);
                        } else if t.state == TaskState::Pending {
                            lemma_unfulfilled_is_stored(map[x], p, ta, now);
                            assert(seen == map[x]);
                            assert(seen_p == p);
                            assert(seen_t == stored);
                            let u_c = c_acquire(t, pid@, ttl, now);
                            let u_a = a_acquire(stored, sat_add(stored.version, 1), pid@, ttl, now);
                            lemma_acquire_rel(t, stored, pid@, ttl, now);
                            let obj2 = ObjV { task: Some(u_c), ..seen };
                            let n = AStore { tasks: s.tasks.insert(x, u_a), ..s };
                            assert(object_rel(obj2, p, Some(u_a)));
                            assert(obj2.promise.callbacks == map[x].promise.callbacks);
                            lemma_promises_kept(s, x);
                            lemma_origin_update(map, o, s, x, obj2, p, Some(u_a), n);
                            assert(map.insert(x, obj2).dom() == map.dom().insert(x));
                            lemma_origin_reads(key, o, map.insert(x, obj2), n);
                            lemma_task_record(action.id, u_c, u_a);
                            lemma_record(action.id, obj2.promise, seen_p);
                            assert(outs == spec_out(
                                spec_claim_res(200, Some(a_task_record(action.id, u_a)), Some(spec_promise_record(action.id, seen_p))),
                                n,
                            ));
                            assert(c_task_create(doc, pid, ttl, action, now).0 == DocumentBodyV::Workflow(map.insert(x, obj2)));
                            lemma_within_one(s, n, x);
                            lemma_others_kept_within(s, n, o);
                            assert(n.tasks.dom() == s.tasks.dom().insert(x));
                            lemma_finite_at(s, n, x);
                        } else {
                            assert(outs == spec_out(spec_claim_res(409, None, None), s));
                            lemma_others_same(key, s);
                        }
                    },
                    _ => {
                        assert(false);
                    },
                }
            }
        } else {
            assert(!s.promises.contains_key(x));
            assert(!s.tasks.contains_key(x));
            let obj = spec_new_obj(action.timeout_at, now, action.param, action.tags, true);
            assert(spec_targeted(action.tags));
            assert(doc1 == spec_with_workflow(doc, map.insert(x, obj)));
            assert(doc1 == DocumentBodyV::Workflow(map.insert(x, obj)));
            let map1 = map.insert(x, obj);
            assert(map1.contains_key(x));
            assert(map1[x] == obj);
            let seen = spec_project_obj(obj, now);
            assert(seen.promise.tags == action.tags);
            lemma_targeted(seen.promise.tags);
            assert(obj.task is Some);
            lemma_empty_to_set();
            let live = action.timeout_at > now;
            let p_a = PromiseV {
                state: if live { PromiseState::Pending } else { PromiseState::RejectedTimedout },
                value: echod_abstract_spec::state::spec_empty_value(),
                param: action.param,
                timeout_at: action.timeout_at,
                created_at: if live { now } else { action.timeout_at },
                settled_at: if live { None } else { Some(action.timeout_at) },
                tags: action.tags,
                callbacks: Set::empty(),
                listeners: Set::empty(),
            };
            let born = TaskV {
                state: TaskState::Fulfilled,
                version: 0,
                pid: None,
                ttl: None,
                acquired_at: 0,
                retry_timeout_at: None,
                resumes: Seq::empty(),
            };
            assert(promise_rel(obj.promise, p_a));
            assert forall|k: int| 0 <= k < obj.promise.callbacks.len() implies origin(#[trigger] obj.promise.callbacks[k]) == o by {};
            if live {
                let t = obj.task.unwrap();
                assert(t.state == TaskState::Pending);
                assert(seen == obj);
                assert(seen.task.unwrap() == t);
                let u_c = c_acquire(t, pid@, ttl, now);
                let t_a = a_acquire(born, 1, pid@, ttl, now);
                lemma_sat_add(0, 1);
                lemma_sat_add(now, ttl);
                assert(task_rel(u_c, t_a));
                let obj2 = ObjV { task: Some(u_c), ..seen };
                assert(object_rel(obj2, p_a, Some(t_a)));
                let n = AStore { promises: s.promises.insert(x, p_a), tasks: s.tasks.insert(x, t_a), ..s };
                assert(outs == spec_out(
                    spec_claim_res(200, Some(a_task_record(action.id, t_a)), Some(spec_promise_record(action.id, p_a))),
                    n,
                ));
                lemma_task_record(action.id, u_c, t_a);
                lemma_record(action.id, obj2.promise, p_a);
                lemma_origin_update(map, o, s, x, obj2, p_a, Some(t_a), n);
                assert(map1.insert(x, obj2) =~= map.insert(x, obj2));
                assert(c_task_create(doc, pid, ttl, action, now).0 == DocumentBodyV::Workflow(map.insert(x, obj2)));
                assert(map.insert(x, obj2).dom() == map.dom().insert(x));
                lemma_origin_reads(key, o, map.insert(x, obj2), n);
                lemma_within_one(s, n, x);
                lemma_others_kept_within(s, n, o);
                assert(n.promises.dom() == s.promises.dom().insert(x));
                assert(n.tasks.dom() == s.tasks.dom().insert(x));
                lemma_finite_at(s, n, x);
            } else {
                let t = obj.task.unwrap();
                assert(t.state == TaskState::Fulfilled);
                assert(obj.promise.state == PromiseState::RejectedTimedout);
                assert(seen == obj);
                assert(task_rel(t, born));
                assert(object_rel(obj, p_a, Some(born)));
                let n = AStore { promises: s.promises.insert(x, p_a), tasks: s.tasks.insert(x, born), ..s };
                assert(outs == spec_out(
                    spec_claim_res(200, Some(a_task_record(action.id, born)), Some(spec_promise_record(action.id, p_a))),
                    n,
                ));
                lemma_task_record(action.id, t, born);
                lemma_record(action.id, obj.promise, p_a);
                lemma_origin_update(map, o, s, x, obj, p_a, Some(born), n);
                assert(c_task_create(doc, pid, ttl, action, now).0 == doc1);
                assert(map1.dom() == map.dom().insert(x));
                lemma_origin_reads(key, o, map1, n);
                lemma_within_one(s, n, x);
                lemma_others_kept_within(s, n, o);
                assert(n.promises.dom() == s.promises.dom().insert(x));
                assert(n.tasks.dom() == s.tasks.dom().insert(x));
                lemma_finite_at(s, n, x);
            }
        }
    }
}

pub(crate) proof fn lemma_task_acquire_agrees(
    config: AbstractConfig,
    req: echod_types::TaskAcquireReq,
    doc: DocumentBodyV,
    s: AStore,
    now: Time,
)
    requires
        doc_rel(spec_origin_key(origin(req.id@)), doc, s),
        finite_store(s),
    ensures
        request_agrees(config, Request::TaskAcquire(req), spec_origin_key(origin(req.id@)), doc, s, now),
{
    let request = Request::TaskAcquire(req);
    let x = req.id@;
    let o = origin(x);
    let key = spec_origin_key(o);
    assert(spec_handle(doc, request, now) == c_task_acquire(doc, req.id, req.version, req.pid, req.ttl, now));
    let outs = spec_handler(config, request, s, now);
    assert(outs == a_task_acquire(req.id, req.version, req.pid, req.ttl, s, now));
    if req.ttl == 0 || req.ttl > MAX_TIME {
        assert(outs == spec_out(spec_claim_res(400, None, None), s));
        lemma_others_same(key, s);
        return;
    }
    lemma_origin_doc(key, o, doc, s);
    let map = spec_workflow_map(doc);
    assert(doc == DocumentBodyV::Workflow(map));
    if !map.contains_key(x) {
        assert(!s.promises.contains_key(x));
        assert(!s.tasks.contains_key(x));
        assert(outs == spec_out(spec_claim_res(404, None, None), s));
        lemma_others_same(key, s);
    } else {
        let p = s.promises[x];
        let ta = abstract_task(s, x);
        lemma_project_object(map[x], p, ta, now);
        let seen = spec_project_obj(map[x], now);
        let seen_p = spec_project_promise(p, now);
        match (map[x].task, ta) {
            (None, None) => {
                assert(!s.tasks.contains_key(x));
                assert(outs == spec_out(spec_claim_res(404, None, None), s));
                lemma_others_same(key, s);
            },
            (Some(ct), Some(stored)) => {
                assert(s.tasks.contains_key(x));
                let t = seen.task.unwrap();
                let seen_t = spec_project_task(stored, seen_p);
                assert(task_rel(t, seen_t));
                assert(seen_t.version == stored.version);
                if t.state != TaskState::Pending || t.version != req.version
                    || seen.promise.state != PromiseState::Pending || t.version >= MAX_VERSION {
                    assert(outs == spec_out(spec_claim_res(409, None, None), s));
                    lemma_others_same(key, s);
                } else {
                    lemma_unfulfilled_is_stored(map[x], p, ta, now);
                    assert(seen == map[x]);
                    assert(seen_p == p);
                    assert(seen_t == stored);
                    let u_c = c_acquire(t, req.pid@, req.ttl, now);
                    let u_a = a_acquire(stored, sat_add(stored.version, 1), req.pid@, req.ttl, now);
                    lemma_acquire_rel(t, stored, req.pid@, req.ttl, now);
                    let obj2 = ObjV { task: Some(u_c), ..seen };
                    let n = AStore { tasks: s.tasks.insert(x, u_a), ..s };
                    assert(object_rel(obj2, p, Some(u_a)));
                    assert(obj2.promise.callbacks == map[x].promise.callbacks);
                    lemma_promises_kept(s, x);
                    lemma_origin_update(map, o, s, x, obj2, p, Some(u_a), n);
                    assert(map.insert(x, obj2).dom() == map.dom().insert(x));
                    lemma_origin_reads(key, o, map.insert(x, obj2), n);
                    lemma_task_record(req.id, u_c, u_a);
                    lemma_record(req.id, obj2.promise, p);
                    assert(outs == spec_out(
                        spec_claim_res(200, Some(a_task_record(req.id, u_a)), Some(spec_promise_record(req.id, p))),
                        n,
                    ));
                    assert(c_task_acquire(doc, req.id, req.version, req.pid, req.ttl, now).0 == DocumentBodyV::Workflow(map.insert(x, obj2)));
                    lemma_within_one(s, n, x);
                    lemma_others_kept_within(s, n, o);
                    assert(n.tasks.dom() == s.tasks.dom().insert(x));
                    lemma_finite_at(s, n, x);
                }
            },
            _ => {
                assert(false);
            },
        }
    }
}

/// The held object, released, fulfilled, or kept: one object replaced.
pub(crate) proof fn lemma_held_update(
    key: Seq<char>,
    o: Seq<char>,
    map: Map<Seq<char>, ObjV>,
    s: AStore,
    x: Seq<char>,
    obj2: ObjV,
    q: PromiseV,
    u: TaskV,
)
    requires
        key == spec_origin_key(o),
        map.dom().finite(),
        finite_store(s),
        origin_rel(map, o, s),
        origin(x) == o,
        map.contains_key(x),
        s.promises.contains_key(x),
        s.tasks.contains_key(x),
        object_rel(obj2, q, Some(u)),
        callbacks_in(obj2.promise.callbacks, o),
    ensures
        ({
            let n = AStore { promises: s.promises.insert(x, q), tasks: s.tasks.insert(x, u), ..s };
            &&& doc_rel(key, DocumentBodyV::Workflow(map.insert(x, obj2)), n)
            &&& super::interpretation::others_kept(key, s, n)
            &&& finite_store(n)
        }),
{
    let n = AStore { promises: s.promises.insert(x, q), tasks: s.tasks.insert(x, u), ..s };
    lemma_origin_update(map, o, s, x, obj2, q, Some(u), n);
    assert(map.insert(x, obj2).dom() == map.dom().insert(x));
    lemma_origin_reads(key, o, map.insert(x, obj2), n);
    lemma_within_one(s, n, x);
    lemma_others_kept_within(s, n, o);
    assert(n.promises.dom() == s.promises.dom().insert(x));
    assert(n.tasks.dom() == s.tasks.dom().insert(x));
    lemma_finite_at(s, n, x);
}

pub(crate) proof fn lemma_task_release_agrees(
    config: AbstractConfig,
    req: echod_types::TaskReleaseReq,
    doc: DocumentBodyV,
    s: AStore,
    now: Time,
)
    requires
        doc_rel(spec_origin_key(origin(req.id@)), doc, s),
        finite_store(s),
    ensures
        request_agrees(config, Request::TaskRelease(req), spec_origin_key(origin(req.id@)), doc, s, now),
{
    let request = Request::TaskRelease(req);
    let x = req.id@;
    let o = origin(x);
    let key = spec_origin_key(o);
    assert(spec_handle(doc, request, now) == c_task_release(doc, req.id, req.version, now));
    let outs = spec_handler(config, request, s, now);
    assert(outs == a_task_release(req.id, req.version, s, now));
    lemma_origin_doc(key, o, doc, s);
    let map = spec_workflow_map(doc);
    assert(doc == DocumentBodyV::Workflow(map));
    lemma_held(map, o, s, x, req.version, now);
    let (_, held) = spec_held(map, x, req.version, now);
    assert(spec_with_workflow(doc, map) == doc);
    match held {
        Held::Missing => {
            assert(outs == spec_out(spec_status_res(404), s));
            lemma_others_same(key, s);
        },
        Held::Stale => {
            assert(outs == spec_out(spec_status_res(409), s));
            lemma_others_same(key, s);
        },
        Held::Ok(obj) => {
            let t = obj.task.unwrap();
            let t_a = s.tasks[x];
            let u_c = c_unlease(t, TaskState::Pending, Some(now));
            let u_a = a_unlease(t_a, TaskState::Pending, Some(now));
            assert(task_rel(u_c, u_a));
            let obj2 = ObjV { task: Some(u_c), ..obj };
            let p = s.promises[x];
            assert(object_rel(obj2, p, Some(u_a)));
            lemma_promises_kept(s, x);
            let n = AStore { promises: s.promises.insert(x, p), tasks: s.tasks.insert(x, u_a), ..s };
            assert(n == AStore { tasks: s.tasks.insert(x, u_a), ..s });
            assert(outs == spec_out(spec_status_res(200), n));
            lemma_held_update(key, o, map, s, x, obj2, p, u_a);
            assert(c_task_release(doc, req.id, req.version, now).0 == DocumentBodyV::Workflow(map.insert(x, obj2)));
        },
    }
}

pub(crate) proof fn lemma_task_fulfill_agrees(
    config: AbstractConfig,
    req: echod_types::TaskFulfillReq,
    doc: DocumentBodyV,
    s: AStore,
    now: Time,
)
    requires
        doc_rel(spec_origin_key(origin(req.id@)), doc, s),
        finite_store(s),
    ensures
        request_agrees(config, Request::TaskFulfill(req), spec_origin_key(origin(req.id@)), doc, s, now),
{
    let request = Request::TaskFulfill(req);
    let x = req.id@;
    let o = origin(x);
    let key = spec_origin_key(o);
    let action = req.action;
    assert(spec_handle(doc, request, now) == c_task_fulfill(doc, req.id, req.version, action, now));
    let outs = spec_handler(config, request, s, now);
    assert(outs == a_task_fulfill(req.id, req.version, action, s, now));
    if !action.state.spec_settable() {
        assert(outs == spec_out(a_promise_res(400, None), s));
        lemma_others_same(key, s);
    } else {
        lemma_origin_doc(key, o, doc, s);
        let map = spec_workflow_map(doc);
        assert(doc == DocumentBodyV::Workflow(map));
        lemma_held(map, o, s, x, req.version, now);
        let (_, held) = spec_held(map, x, req.version, now);
        assert(spec_with_workflow(doc, map) == doc);
        match held {
            Held::Missing => {
                assert(outs == spec_out(a_promise_res(404, None), s));
                lemma_others_same(key, s);
            },
            Held::Stale => {
                assert(outs == spec_out(a_promise_res(409, None), s));
                lemma_others_same(key, s);
            },
            Held::Ok(obj) => {
                let t = obj.task.unwrap();
                let t_a = s.tasks[x];
                let p = s.promises[x];
                let promise = PromV { state: action.state, value: action.value, settled_at: Some(now), ..obj.promise };
                let task = Some(spec_fulfill_task(t));
                let obj2 = ObjV { promise, task };
                let q = PromiseV { state: action.state, value: action.value, settled_at: Some(now), ..p };
                let u = spec_fulfill(t_a);
                assert(promise_rel(promise, q));
                assert(task_rel(spec_fulfill_task(t), u));
                assert(object_rel(obj2, q, Some(u)));
                let n = spec_settle(s, x, action.state, action.value, now);
                assert(t_a.state == TaskState::Acquired);
                assert(n == AStore { promises: s.promises.insert(x, q), tasks: s.tasks.insert(x, u), ..s });
                assert(n.promises.contains_key(x));
                assert(n.promises[x] == q);
                lemma_record(req.id, promise, q);
                assert(outs == spec_out(a_promise_res(200, Some(spec_promise_record(req.id, q))), n));
                assert(c_task_fulfill(doc, req.id, req.version, action, now).1 == c_promise_res(200, Some(echod_concrete_spec::state::spec_record(req.id, promise))));
                lemma_held_update(key, o, map, s, x, obj2, q, u);
                assert(c_task_fulfill(doc, req.id, req.version, action, now).0 == DocumentBodyV::Workflow(map.insert(x, obj2)));
            },
        }
    }
}

pub(crate) proof fn lemma_task_halt_agrees(config: AbstractConfig, id: String, doc: DocumentBodyV, s: AStore, now: Time)
    requires
        doc_rel(spec_origin_key(origin(id@)), doc, s),
        finite_store(s),
    ensures
        request_agrees(
            config,
            Request::TaskHalt(echod_types::TaskHaltReq { id }),
            spec_origin_key(origin(id@)),
            doc,
            s,
            now,
        ),
{
    let request = Request::TaskHalt(echod_types::TaskHaltReq { id });
    let x = id@;
    let o = origin(x);
    let key = spec_origin_key(o);
    assert(spec_handle(doc, request, now) == c_task_halt(doc, id, now));
    let outs = spec_handler(config, request, s, now);
    assert(outs == a_task_halt(id, s, now));
    lemma_origin_doc(key, o, doc, s);
    let map = spec_workflow_map(doc);
    assert(doc == DocumentBodyV::Workflow(map));
    if !map.contains_key(x) {
        assert(!s.tasks.contains_key(x));
        assert(outs == spec_out(spec_status_res(404), s));
        lemma_others_same(key, s);
    } else {
        let p = s.promises[x];
        let ta = abstract_task(s, x);
        lemma_project_object(map[x], p, ta, now);
        let seen = spec_project_obj(map[x], now);
        let seen_p = spec_project_promise(p, now);
        match (map[x].task, ta) {
            (None, None) => {
                assert(!s.tasks.contains_key(x));
                assert(outs == spec_out(spec_status_res(404), s));
                lemma_others_same(key, s);
            },
            (Some(ct), Some(stored)) => {
                assert(s.tasks.contains_key(x));
                let t = seen.task.unwrap();
                let seen_t = spec_project_task(stored, seen_p);
                assert(task_rel(t, seen_t));
                if t.state == TaskState::Fulfilled {
                    assert(outs == spec_out(spec_status_res(409), s));
                    lemma_others_same(key, s);
                } else if t.state == TaskState::Halted {
                    assert(outs == spec_out(spec_status_res(200), s));
                    lemma_others_same(key, s);
                } else {
                    lemma_unfulfilled_is_stored(map[x], p, ta, now);
                    assert(seen == map[x]);
                    assert(seen_t == stored);
                    let u_c = c_unlease(t, TaskState::Halted, None);
                    let u_a = a_unlease(stored, TaskState::Halted, None);
                    assert(task_rel(u_c, u_a));
                    let obj2 = ObjV { task: Some(u_c), ..seen };
                    assert(object_rel(obj2, p, Some(u_a)));
                    assert(obj2.promise.callbacks == map[x].promise.callbacks);
                    lemma_promises_kept(s, x);
                    let n = AStore { promises: s.promises.insert(x, p), tasks: s.tasks.insert(x, u_a), ..s };
                    assert(n == AStore { tasks: s.tasks.insert(x, u_a), ..s });
                    assert(outs == spec_out(spec_status_res(200), n));
                    lemma_held_update(key, o, map, s, x, obj2, p, u_a);
                    assert(c_task_halt(doc, id, now).0 == DocumentBodyV::Workflow(map.insert(x, obj2)));
                }
            },
            _ => {
                assert(false);
            },
        }
    }
}

pub(crate) proof fn lemma_task_continue_agrees(config: AbstractConfig, id: String, doc: DocumentBodyV, s: AStore, now: Time)
    requires
        doc_rel(spec_origin_key(origin(id@)), doc, s),
        finite_store(s),
    ensures
        request_agrees(
            config,
            Request::TaskContinue(echod_types::TaskContinueReq { id }),
            spec_origin_key(origin(id@)),
            doc,
            s,
            now,
        ),
{
    let request = Request::TaskContinue(echod_types::TaskContinueReq { id });
    let x = id@;
    let o = origin(x);
    let key = spec_origin_key(o);
    assert(spec_handle(doc, request, now) == c_task_continue(doc, id, now));
    let outs = spec_handler(config, request, s, now);
    assert(outs == a_task_continue(id, s, now));
    lemma_origin_doc(key, o, doc, s);
    let map = spec_workflow_map(doc);
    assert(doc == DocumentBodyV::Workflow(map));
    if !map.contains_key(x) {
        assert(!s.tasks.contains_key(x));
        assert(outs == spec_out(spec_status_res(404), s));
        lemma_others_same(key, s);
    } else {
        let p = s.promises[x];
        let ta = abstract_task(s, x);
        lemma_project_object(map[x], p, ta, now);
        let seen = spec_project_obj(map[x], now);
        let seen_p = spec_project_promise(p, now);
        match (map[x].task, ta) {
            (None, None) => {
                assert(!s.tasks.contains_key(x));
                assert(outs == spec_out(spec_status_res(404), s));
                lemma_others_same(key, s);
            },
            (Some(ct), Some(stored)) => {
                assert(s.tasks.contains_key(x));
                let t = seen.task.unwrap();
                let seen_t = spec_project_task(stored, seen_p);
                assert(task_rel(t, seen_t));
                let live = seen_p.state == PromiseState::Pending;
                assert(live == (seen.promise.state == PromiseState::Pending));
                if t.state != TaskState::Halted || seen.promise.state != PromiseState::Pending {
                    if live {
                        assert(seen_t == stored);
                        assert(t.state == stored.state);
                    }
                    assert(stored.state != TaskState::Halted || !live);
                    assert(outs == spec_out(spec_status_res(409), s));
                    lemma_others_same(key, s);
                } else {
                    lemma_unfulfilled_is_stored(map[x], p, ta, now);
                    assert(seen == map[x]);
                    assert(seen_t == stored);
                    assert(stored.state == TaskState::Halted);
                    let u_c = TkV { state: TaskState::Pending, retry_timeout_at: Some(now), ..t };
                    let u_a = TaskV { state: TaskState::Pending, retry_timeout_at: Some(now), ..stored };
                    assert(task_rel(u_c, u_a));
                    let obj2 = ObjV { task: Some(u_c), ..seen };
                    assert(object_rel(obj2, p, Some(u_a)));
                    assert(obj2.promise.callbacks == map[x].promise.callbacks);
                    lemma_promises_kept(s, x);
                    let n = AStore { promises: s.promises.insert(x, p), tasks: s.tasks.insert(x, u_a), ..s };
                    assert(n == AStore { tasks: s.tasks.insert(x, u_a), ..s });
                    assert(outs == spec_out(spec_status_res(200), n));
                    lemma_held_update(key, o, map, s, x, obj2, p, u_a);
                    assert(c_task_continue(doc, id, now).0 == DocumentBodyV::Workflow(map.insert(x, obj2)));
                }
            },
            _ => {
                assert(false);
            },
        }
    }
}


// ---------------------------------------------------------------------------
// The heartbeat
// ---------------------------------------------------------------------------

pub(crate) proof fn lemma_one_origin_from(refs: Seq<TaskRef>, o: Seq<char>, i: int)
    requires
        0 <= i,
    ensures
        spec_one_origin(refs, o, i) == forall|k: int| i <= k < refs.len() ==> origin(#[trigger] refs[k].id@) == o,
    decreases refs.len() - i,
{
    if i >= refs.len() {
    } else {
        lemma_one_origin_from(refs, o, i + 1);
    }
}

pub(crate) proof fn lemma_refs_one_origin_from(refs: Seq<TaskRef>, j: int)
    requires
        j >= 1,
    ensures
        spec_refs_one_origin(refs, j) == forall|k: int|
            j <= k < refs.len() ==> origin(#[trigger] refs[k].id@) == origin(refs[0].id@),
    decreases refs.len() - j,
{
    if j >= refs.len() {
    } else {
        lemma_refs_one_origin_from(refs, j + 1);
    }
}

/// The running document and the running task map, `i` refs in: related,
/// with the same keys as at the start, the tasks differing from the start
/// in their leases alone, and other origins untouched.
pub(crate) open spec fn extending(
    map0: Map<Seq<char>, ObjV>,
    o: Seq<char>,
    s: AStore,
    map_i: Map<Seq<char>, ObjV>,
    tasks_i: Map<Seq<char>, TaskV>,
) -> bool {
    &&& origin_rel(map_i, o, AStore { tasks: tasks_i, ..s })
    &&& forall|id: Seq<char>| #[trigger] map_i.contains_key(id) == map0.contains_key(id)
    &&& forall|id: Seq<char>|
        #[trigger] map0.contains_key(id) ==> {
            let a = map0[id];
            let b = map_i[id];
            &&& b.promise == a.promise
            &&& (b.task is Some) == (a.task is Some)
            &&& b.task is Some ==> b.task.unwrap() == (TkV {
                lease_timeout_at: b.task.unwrap().lease_timeout_at,
                ..a.task.unwrap()
            })
        }
    &&& forall|id: Seq<char>| #[trigger] tasks_i.contains_key(id) == s.tasks.contains_key(id)
    &&& forall|id: Seq<char>|
        #![trigger origin(id)]
        origin(id) != o ==> (s.tasks.contains_key(id) ==> tasks_i[id] == s.tasks[id])
}

pub(crate) proof fn lemma_extend(
    map0: Map<Seq<char>, ObjV>,
    o: Seq<char>,
    s: AStore,
    pid: Seq<char>,
    refs: Seq<TaskRef>,
    now: Time,
    i: int,
    map_i: Map<Seq<char>, ObjV>,
    tasks_i: Map<Seq<char>, TaskV>,
)
    requires
        origin_rel(map0, o, s),
        extending(map0, o, s, map_i, tasks_i),
        0 <= i <= refs.len(),
        forall|k: int| 0 <= k < refs.len() ==> origin(#[trigger] refs[k].id@) == o,
    ensures
        extending(map0, o, s, c_extend(map_i, pid, refs, now, i), a_extend(s, pid, refs, now, i, tasks_i)),
    decreases refs.len() - i,
{
    if i >= refs.len() {
    } else {
        let id = refs[i].id@;
        let version = refs[i].version;
        let s_i = AStore { tasks: tasks_i, ..s };
        lemma_held(map0, o, s, id, version, now);
        let (_, held0) = spec_held(map0, id, version, now);
        let a = a_held(s, id, version, now);
        let a_cond = a is Ok && a->Ok_0.pid == Some(pid);
        let c_cond = map_i.contains_key(id) && {
            let obj = spec_project_obj(map_i[id], now);
            match obj.task {
                Some(t) => t.state == TaskState::Acquired && t.version == version && t.pid == Some(pid),
                None => false,
            }
        };
        if map_i.contains_key(id) {
            assert(map0.contains_key(id));
            let a0 = map0[id];
            let b = map_i[id];
            assert(b.promise == a0.promise);
            let seen0 = spec_project_obj(a0, now);
            let seen = spec_project_obj(b, now);
            assert(seen.promise == seen0.promise);
            match (a0.task, b.task) {
                (Some(ta0), Some(tb)) => {
                    assert(tb == TkV { lease_timeout_at: tb.lease_timeout_at, ..ta0 });
                    let p = s.promises[id];
                    assert(object_rel(a0, p, abstract_task(s, id)));
                    let t_c = seen.task.unwrap();
                    let t_c0 = seen0.task.unwrap();
                    assert(t_c.state == t_c0.state);
                    assert(t_c.version == t_c0.version);
                    assert(t_c.pid == t_c0.pid);
                    if t_c.state == TaskState::Acquired {
                        assert(seen0.promise.state == PromiseState::Pending);
                    }
                    assert(c_cond == (held0 is Ok && t_c0.pid == Some(pid)));
                    if held0 is Ok {
                        assert(t_c0 == a0.task.unwrap());
                        assert(task_rel(a0.task.unwrap(), s.tasks[id]));
                        assert(t_c0.pid == s.tasks[id].pid);
                    }
                    assert(c_cond == a_cond);
                },
                (None, None) => {
                    assert(!s.tasks.contains_key(id));
                    assert(a is Missing);
                    assert(!c_cond);
                },
                _ => {
                    assert(false);
                },
            }
        } else {
            assert(!map0.contains_key(id));
            assert(!s.tasks.contains_key(id));
            assert(a is Missing);
        }
        if c_cond {
            let obj = spec_project_obj(map_i[id], now);
            let p = s.promises[id];
            let ta = abstract_task(s_i, id);
            assert(object_rel(map_i[id], p, ta));
            lemma_unfulfilled_is_stored(map_i[id], p, ta, now);
            assert(obj == map_i[id]);
            let t = obj.task.unwrap();
            assert(t.state == TaskState::Acquired);
            assert(t.ttl is Some);
            let ttl = match t.ttl {
                Some(n) => n,
                None => 0,
            };
            let at = echod_concrete_spec::state::spec_sat_add(now, ttl);
            let t2 = TkV { lease_timeout_at: Some(at), ..t };
            let obj2 = ObjV { task: Some(t2), ..obj };
            let t_a = a->Ok_0;
            assert(t_a == s.tasks[id]);
            let u_a = TaskV { acquired_at: now, ..t_a };
            assert(task_rel(map0[id].task.unwrap(), t_a));
            lemma_sat_add(now, ttl);
            assert(task_rel(t2, u_a));
            assert(object_rel(obj2, p, Some(u_a)));
            let map_next = map_i.insert(id, obj2);
            let tasks_next = tasks_i.insert(id, u_a);
            let s_next = AStore { tasks: tasks_next, ..s };
            assert(s_next.promises == s_i.promises.insert(id, p)) by {
                assert(s.promises.insert(id, p) =~= s.promises);
            };
            lemma_origin_update(map_i, o, s_i, id, obj2, p, Some(u_a), s_next);
            assert(extending(map0, o, s, map_next, tasks_next));
            assert(c_extend(map_i, pid, refs, now, i) == c_extend(map_next, pid, refs, now, i + 1));
            assert(a_extend(s, pid, refs, now, i, tasks_i) == a_extend(s, pid, refs, now, i + 1, tasks_next));
            lemma_extend(map0, o, s, pid, refs, now, i + 1, map_next, tasks_next);
        } else {
            assert(c_extend(map_i, pid, refs, now, i) == c_extend(map_i, pid, refs, now, i + 1));
            assert(a_extend(s, pid, refs, now, i, tasks_i) == a_extend(s, pid, refs, now, i + 1, tasks_i));
            lemma_extend(map0, o, s, pid, refs, now, i + 1, map_i, tasks_i);
        }
    }
}

pub(crate) proof fn lemma_heartbeat_agrees(
    config: AbstractConfig,
    req: echod_types::TaskHeartbeatReq,
    doc: DocumentBodyV,
    s: AStore,
    now: Time,
)
    requires
        req.tasks@.len() > 0,
        doc_rel(spec_origin_key(origin(req.tasks@[0].id@)), doc, s),
        finite_store(s),
    ensures
        request_agrees(
            config,
            Request::TaskHeartbeat(req),
            spec_origin_key(origin(req.tasks@[0].id@)),
            doc,
            s,
            now,
        ),
{
    let request = Request::TaskHeartbeat(req);
    let refs = req.tasks@;
    let pid = req.pid;
    let o = origin(refs[0].id@);
    let key = spec_origin_key(o);
    assert(spec_handle(doc, request, now) == c_heartbeat(doc, pid, refs, now));
    let outs = spec_handler(config, request, s, now);
    assert(outs == a_heartbeat(pid, refs, s, now));
    lemma_one_origin_from(refs, o, 0);
    lemma_refs_one_origin_from(refs, 1);
    assert(spec_one_origin(refs, o, 0) == spec_refs_one_origin(refs, 1));
    if !spec_one_origin(refs, o, 0) {
        assert(outs == spec_out(spec_status_res(400), s));
        lemma_others_same(key, s);
    } else {
        lemma_origin_doc(key, o, doc, s);
        let map = spec_workflow_map(doc);
        assert(doc == DocumentBodyV::Workflow(map));
        assert(extending(map, o, s, map, s.tasks));
        lemma_extend(map, o, s, pid@, refs, now, 0, map, s.tasks);
        let map2 = c_extend(map, pid@, refs, now, 0);
        let tasks2 = a_extend(s, pid@, refs, now, 0, s.tasks);
        let n = AStore { tasks: tasks2, ..s };
        assert(outs == spec_out(spec_status_res(200), n));
        assert(c_heartbeat(doc, pid, refs, now) == (DocumentBodyV::Workflow(map2), Response::Status(StatusRes { status: 200 })));
        assert(map2.dom() =~= map.dom());
        lemma_origin_reads(key, o, map2, n);
        assert(changed_within(s, n, o));
        lemma_others_kept_within(s, n, o);
        assert(tasks2.dom() =~= s.tasks.dom());
        assert(finite_store(n));
    }
}

// ---------------------------------------------------------------------------
// The suspend
// ---------------------------------------------------------------------------

pub(crate) proof fn lemma_bad_suspend_from(actions: Seq<PromiseRegisterCallbackReq>, x: Seq<char>, i: int)
    requires
        0 <= i,
    ensures
        spec_bad_suspend(actions, x, i) == exists|j: int|
            i <= j < actions.len() && ((#[trigger] actions[j]).awaited@ == x || origin(actions[j].awaited@) != origin(x)),
    decreases actions.len() - i,
{
    if i >= actions.len() {
    } else {
        lemma_bad_suspend_from(actions, x, i + 1);
    }
}

pub(crate) proof fn lemma_seen_from(actions: Seq<PromiseRegisterCallbackReq>, id: Seq<char>, j: int, stop: int)
    requires
        0 <= j,
    ensures
        spec_seen(actions, id, j, stop) == exists|k: int|
            j <= k < stop && k < actions.len() && (#[trigger] actions[k]).awaited@ == id,
    decreases stop - j,
{
    if j >= stop || j >= actions.len() {
    } else {
        lemma_seen_from(actions, id, j + 1, stop);
    }
}

pub(crate) proof fn lemma_distinct_from(actions: Seq<PromiseRegisterCallbackReq>, i: int)
    requires
        i >= 0,
    ensures
        spec_distinct_awaited(actions, i) == forall|a: int, b: int|
            #![trigger actions[a], actions[b]]
            i <= a < actions.len() && 0 <= b < a ==> actions[a].awaited@ != actions[b].awaited@,
    decreases actions.len() - i,
{
    if i >= actions.len() {
    } else {
        lemma_seen_from(actions, actions[i].awaited@, 0, i);
        lemma_distinct_from(actions, i + 1);
    }
}

pub(crate) proof fn lemma_missing_from(map: Map<Seq<char>, ObjV>, actions: Seq<PromiseRegisterCallbackReq>, i: int)
    requires
        0 <= i,
    ensures
        spec_missing_awaited(map, actions, i) == exists|j: int|
            i <= j < actions.len() && !map.contains_key((#[trigger] actions[j]).awaited@),
    decreases actions.len() - i,
{
    if i >= actions.len() {
    } else {
        lemma_missing_from(map, actions, i + 1);
    }
}

pub(crate) proof fn lemma_unawaitable_from(map: Map<Seq<char>, ObjV>, actions: Seq<PromiseRegisterCallbackReq>, i: int)
    requires
        0 <= i,
    ensures
        spec_unawaitable(map, actions, i) == exists|j: int|
            i <= j < actions.len() && map.contains_key((#[trigger] actions[j]).awaited@)
                && !spec_awaitable(map[actions[j].awaited@].promise.tags),
    decreases actions.len() - i,
{
    if i >= actions.len() {
    } else {
        lemma_unawaitable_from(map, actions, i + 1);
    }
}

pub(crate) proof fn lemma_c_any_settled_from(
    map: Map<Seq<char>, ObjV>,
    actions: Seq<PromiseRegisterCallbackReq>,
    now: Time,
    i: int,
)
    requires
        0 <= i,
    ensures
        c_any_settled(map, actions, now, i) == exists|j: int|
            i <= j < actions.len() && map.contains_key((#[trigger] actions[j]).awaited@)
                && spec_project_obj(map[actions[j].awaited@], now).promise.state != PromiseState::Pending,
    decreases actions.len() - i,
{
    if i >= actions.len() {
    } else {
        lemma_c_any_settled_from(map, actions, now, i + 1);
    }
}

pub(crate) proof fn lemma_a_any_settled_from(s: AStore, ids: Seq<Seq<char>>, now: Time, i: int)
    requires
        0 <= i,
        forall|k: int| 0 <= k < ids.len() ==> s.promises.contains_key(#[trigger] ids[k]),
    ensures
        a_any_settled(s, ids, now, i) == exists|j: int|
            i <= j < ids.len() && spec_project_promise(s.promises[#[trigger] ids[j]], now).state != PromiseState::Pending,
    decreases ids.len() - i,
{
    if i >= ids.len() {
    } else {
        lemma_a_any_settled_from(s, ids, now, i + 1);
    }
}

/// The running document and the running promises, `i` callbacks in.
pub(crate) open spec fn adding(
    map0: Map<Seq<char>, ObjV>,
    o: Seq<char>,
    s: AStore,
    x: Seq<char>,
    map_i: Map<Seq<char>, ObjV>,
    promises_i: Map<Seq<char>, PromiseV>,
) -> bool {
    &&& origin_rel(map_i, o, AStore { promises: promises_i, ..s })
    &&& forall|id: Seq<char>| #[trigger] map_i.contains_key(id) == map0.contains_key(id)
    &&& forall|id: Seq<char>| #[trigger] promises_i.contains_key(id) == s.promises.contains_key(id)
    &&& map0.contains_key(x) ==> map_i[x] == map0[x]
    &&& s.promises.contains_key(x) ==> promises_i[x] == s.promises[x]
    &&& forall|id: Seq<char>|
        #![trigger origin(id)]
        origin(id) != o ==> (s.promises.contains_key(id) ==> promises_i[id] == s.promises[id])
}

pub(crate) proof fn lemma_add_callbacks(
    map0: Map<Seq<char>, ObjV>,
    o: Seq<char>,
    s: AStore,
    x: Seq<char>,
    actions: Seq<PromiseRegisterCallbackReq>,
    i: int,
    map_i: Map<Seq<char>, ObjV>,
    promises_i: Map<Seq<char>, PromiseV>,
)
    requires
        adding(map0, o, s, x, map_i, promises_i),
        0 <= i <= actions.len(),
        origin(x) == o,
        forall|k: int|
            i <= k < actions.len() ==> map0.contains_key((#[trigger] actions[k]).awaited@) && actions[k].awaited@ != x
                && origin(actions[k].awaited@) == o,
    ensures
        adding(
            map0,
            o,
            s,
            x,
            spec_add_callbacks(map_i, x, actions, i),
            a_callbacks(promises_i, spec_awaited(actions), x, i),
        ),
    decreases actions.len() - i,
{
    if i >= actions.len() {
    } else {
        let a = actions[i].awaited@;
        let ids = spec_awaited(actions);
        assert(ids[i] == a);
        assert(map_i.contains_key(a));
        assert(promises_i.contains_key(a));
        let s_i = AStore { promises: promises_i, ..s };
        let obj = map_i[a];
        let p = promises_i[a];
        let ta = abstract_task(s_i, a);
        assert(object_rel(obj, p, ta));
        let callbacks = if obj.promise.callbacks.contains(x) {
            obj.promise.callbacks
        } else {
            obj.promise.callbacks.push(x)
        };
        lemma_add_callback(obj.promise.callbacks, p.callbacks, x);
        let obj2 = ObjV { promise: PromV { callbacks, ..obj.promise }, ..obj };
        let q = PromiseV { callbacks: p.callbacks.insert(x), ..p };
        assert(promise_rel(obj2.promise, q));
        assert(object_rel(obj2, q, ta));
        assert forall|k: int| 0 <= k < callbacks.len() implies origin(#[trigger] callbacks[k]) == o by {
            if k < obj.promise.callbacks.len() {
                assert(callbacks[k] == obj.promise.callbacks[k]);
            } else {
                assert(callbacks[k] == x);
            }
        };
        let map_next = map_i.insert(a, obj2);
        let promises_next = promises_i.insert(a, q);
        let s_next = AStore { promises: promises_next, ..s };
        lemma_tasks_kept(s_i, a);
        lemma_origin_update(map_i, o, s_i, a, obj2, q, ta, s_next);
        assert(adding(map0, o, s, x, map_next, promises_next));
        assert(spec_add_callbacks(map_i, x, actions, i) == spec_add_callbacks(map_next, x, actions, i + 1));
        assert(a_callbacks(promises_i, ids, x, i) == a_callbacks(promises_next, ids, x, i + 1));
        lemma_add_callbacks(map0, o, s, x, actions, i + 1, map_next, promises_next);
    }
}

pub(crate) proof fn lemma_suspend_agrees(
    config: AbstractConfig,
    req: echod_types::TaskSuspendReq,
    doc: DocumentBodyV,
    s: AStore,
    now: Time,
)
    requires
        doc_rel(spec_origin_key(origin(req.id@)), doc, s),
        finite_store(s),
    ensures
        request_agrees(config, Request::TaskSuspend(req), spec_origin_key(origin(req.id@)), doc, s, now),
{
    let request = Request::TaskSuspend(req);
    let x = req.id@;
    let o = origin(x);
    let key = spec_origin_key(o);
    let actions = req.actions@;
    let ids = spec_awaited(actions);
    assert(ids.len() == actions.len());
    assert forall|j: int| 0 <= j < actions.len() implies #[trigger] ids[j] == actions[j].awaited@ by {};
    assert(spec_handle(doc, request, now) == c_suspend(doc, req.id, req.version, actions, now));
    let outs = spec_handler(config, request, s, now);
    assert(outs == a_suspend(req.id, req.version, actions, s, now));
    lemma_bad_suspend_from(actions, x, 0);
    lemma_distinct_from(actions, 0);
    assert(spec_bad_suspend(actions, x, 0) == (ids.contains(x) || !all_in_origin(ids, x))) by {
        if spec_bad_suspend(actions, x, 0) {
            let j = choose|j: int|
                0 <= j < actions.len() && ((#[trigger] actions[j]).awaited@ == x || origin(actions[j].awaited@) != origin(x));
            if actions[j].awaited@ == x {
                assert(ids[j] == x);
                assert(ids.contains(x));
            } else {
                assert(origin(ids[j]) != origin(x));
                assert(!all_in_origin(ids, x));
            }
        }
        if ids.contains(x) {
            let j = choose|j: int| 0 <= j < ids.len() && ids[j] == x;
            assert(actions[j].awaited@ == x);
            assert(spec_bad_suspend(actions, x, 0));
        }
        if !all_in_origin(ids, x) {
            let j = choose|j: int| 0 <= j < ids.len() && origin(#[trigger] ids[j]) != origin(x);
            assert(origin(actions[j].awaited@) != origin(x));
            assert(spec_bad_suspend(actions, x, 0));
        }
    };
    assert(spec_distinct_awaited(actions, 0) == distinct(ids)) by {
        if spec_distinct_awaited(actions, 0) {
            assert forall|a: int, b: int| 0 <= a < b < ids.len() implies ids[a] != ids[b] by {
                assert(actions[b].awaited@ != actions[a].awaited@);
            };
        }
        if distinct(ids) {
            assert forall|a: int, b: int|
                #![trigger actions[a], actions[b]]
                0 <= a < actions.len() && 0 <= b < a implies actions[a].awaited@ != actions[b].awaited@ by {
                assert(ids[b] != ids[a]);
            };
        }
    };
    if actions.len() == 0 || spec_bad_suspend(actions, x, 0) || !spec_distinct_awaited(actions, 0) {
        assert(outs == spec_out(spec_status_res(400), s));
        assert(c_suspend(doc, req.id, req.version, actions, now) == (doc, Response::Status(StatusRes { status: 400 })));
        lemma_others_same(key, s);
    } else {
        assert(all_in_origin(ids, x));
        assert forall|k: int| 0 <= k < actions.len() implies origin((#[trigger] actions[k]).awaited@) == o
            && actions[k].awaited@ != x by {
            assert(origin(ids[k]) == origin(x));
            if actions[k].awaited@ == x {
                assert(ids.contains(x));
            }
        };
        lemma_origin_doc(key, o, doc, s);
        let map = spec_workflow_map(doc);
        assert(doc == DocumentBodyV::Workflow(map));
        lemma_held(map, o, s, x, req.version, now);
        let (_, held) = spec_held(map, x, req.version, now);
        assert(spec_with_workflow(doc, map) == doc);
        match held {
            Held::Missing => {
                assert(outs == spec_out(spec_status_res(404), s));
                lemma_others_same(key, s);
            },
            Held::Stale => {
                assert(outs == spec_out(spec_status_res(409), s));
                lemma_others_same(key, s);
            },
            Held::Ok(obj) => {
                let t = obj.task.unwrap();
                let t_a = s.tasks[x];
                let p = s.promises[x];
                lemma_missing_from(map, actions, 0);
                lemma_unawaitable_from(map, actions, 0);
                let missing = exists|j: int| 0 <= j < ids.len() && !s.promises.contains_key(#[trigger] ids[j]);
                assert(spec_missing_awaited(map, actions, 0) == missing) by {
                    if spec_missing_awaited(map, actions, 0) {
                        let j = choose|j: int| 0 <= j < actions.len() && !map.contains_key((#[trigger] actions[j]).awaited@);
                        assert(!s.promises.contains_key(ids[j]));
                    }
                    if missing {
                        let j = choose|j: int| 0 <= j < ids.len() && !s.promises.contains_key(#[trigger] ids[j]);
                        assert(!map.contains_key(actions[j].awaited@));
                    }
                };
                if missing {
                    assert(outs == spec_out(spec_status_res(422), s));
                    assert(c_suspend(doc, req.id, req.version, actions, now).1 == Response::Status(StatusRes { status: 422 }));
                    lemma_others_same(key, s);
                } else {
                    assert forall|k: int| 0 <= k < ids.len() implies s.promises.contains_key(#[trigger] ids[k]) by {};
                    assert forall|k: int| 0 <= k < actions.len() implies map.contains_key((#[trigger] actions[k]).awaited@) by {
                        assert(s.promises.contains_key(ids[k]));
                    };
                    let unawaitable = exists|j: int| 0 <= j < ids.len() && !spec_external(s.promises[#[trigger] ids[j]]);
                    assert(spec_unawaitable(map, actions, 0) == unawaitable) by {
                        if spec_unawaitable(map, actions, 0) {
                            let j = choose|j: int|
                                0 <= j < actions.len() && map.contains_key((#[trigger] actions[j]).awaited@)
                                    && !spec_awaitable(map[actions[j].awaited@].promise.tags);
                            let a = actions[j].awaited@;
                            assert(object_rel(map[a], s.promises[a], abstract_task(s, a)));
                            lemma_awaitable(map[a].promise, s.promises[a]);
                            assert(!spec_external(s.promises[ids[j]]));
                        }
                        if unawaitable {
                            let j = choose|j: int| 0 <= j < ids.len() && !spec_external(s.promises[#[trigger] ids[j]]);
                            let a = actions[j].awaited@;
                            assert(object_rel(map[a], s.promises[a], abstract_task(s, a)));
                            lemma_awaitable(map[a].promise, s.promises[a]);
                            assert(!spec_awaitable(map[a].promise.tags));
                        }
                    };
                    if unawaitable {
                        assert(outs == spec_out(spec_status_res(422), s));
                        assert(c_suspend(doc, req.id, req.version, actions, now).1 == Response::Status(StatusRes { status: 422 }));
                        lemma_others_same(key, s);
                    } else {
                        lemma_c_any_settled_from(map, actions, now, 0);
                        lemma_a_any_settled_from(s, ids, now, 0);
                        assert(c_any_settled(map, actions, now, 0) == a_any_settled(s, ids, now, 0)) by {
                            assert forall|j: int| 0 <= j < actions.len() implies spec_project_obj(
                                map[(#[trigger] actions[j]).awaited@],
                                now,
                            ).promise.state == spec_project_promise(s.promises[ids[j]], now).state by {
                                let a = actions[j].awaited@;
                                lemma_project_object(map[a], s.promises[a], abstract_task(s, a), now);
                            };
                        };
                        if c_any_settled(map, actions, now, 0) {
                            let task = Some(TkV { resumes: Seq::empty(), ..t });
                            let u = TaskV { resumes: Seq::empty(), ..t_a };
                            assert(task_rel(task.unwrap(), u));
                            let obj2 = ObjV { task, ..obj };
                            assert(object_rel(obj2, p, Some(u)));
                            lemma_promises_kept(s, x);
                            let n = AStore { promises: s.promises.insert(x, p), tasks: s.tasks.insert(x, u), ..s };
                            assert(n == AStore { tasks: s.tasks.insert(x, u), ..s });
                            assert(outs == spec_out(spec_status_res(300), n));
                            lemma_held_update(key, o, map, s, x, obj2, p, u);
                            assert(c_suspend(doc, req.id, req.version, actions, now) == (DocumentBodyV::Workflow(map.insert(x, obj2)), Response::Status(StatusRes { status: 300 })));
                        } else {
                            assert(adding(map, o, s, x, map, s.promises));
                            lemma_add_callbacks(map, o, s, x, actions, 0, map, s.promises);
                            let map2 = spec_add_callbacks(map, x, actions, 0);
                            let promises2 = a_callbacks(s.promises, ids, x, 0);
                            assert(adding(map, o, s, x, map2, promises2));
                            let s2 = AStore { promises: promises2, ..s };
                            assert(map2[x] == obj);
                            assert(promises2[x] == p);
                            let task = Some(TkV { resumes: Seq::empty(), ..c_unlease(t, TaskState::Suspended, None) });
                            let u = TaskV {
                                state: TaskState::Suspended,
                                pid: None,
                                ttl: None,
                                acquired_at: 0,
                                retry_timeout_at: None,
                                resumes: Seq::empty(),
                                ..t_a
                            };
                            assert(task_rel(task.unwrap(), u));
                            let obj3 = ObjV { task, ..obj };
                            assert(object_rel(obj3, p, Some(u)));
                            let n = AStore { promises: promises2, tasks: s.tasks.insert(x, u), ..s };
                            assert(outs == spec_out(spec_status_res(200), n));
                            assert(n.promises == s2.promises.insert(x, p)) by {
                                assert(promises2.insert(x, p) =~= promises2);
                            };
                            lemma_origin_update(map2, o, s2, x, obj3, p, Some(u), n);
                            assert(map2.dom() =~= map.dom());
                            assert(map2.insert(x, obj3).dom() == map2.dom().insert(x));
                            lemma_origin_reads(key, o, map2.insert(x, obj3), n);
                            assert(c_suspend(doc, req.id, req.version, actions, now) == (DocumentBodyV::Workflow(map2.insert(x, obj3)), Response::Status(StatusRes { status: 200 })));
                            assert(changed_within(s, n, o)) by {
                                assert forall|id: Seq<char>| #![trigger origin(id)] origin(id) != o implies {
                                    &&& s.promises.contains_key(id) == n.promises.contains_key(id)
                                    &&& (s.promises.contains_key(id) ==> s.promises[id] == n.promises[id])
                                    &&& s.tasks.contains_key(id) == n.tasks.contains_key(id)
                                    &&& (s.tasks.contains_key(id) ==> s.tasks[id] == n.tasks[id])
                                } by {
                                    assert(id != x);
                                };
                            };
                            lemma_others_kept_within(s, n, o);
                            assert(promises2.dom() =~= s.promises.dom());
                            assert(n.tasks.dom() == s.tasks.dom().insert(x));
                            assert(finite_store(n));
                        }
                    }
                }
            },
        }
    }
}

// ---------------------------------------------------------------------------
// The fence
// ---------------------------------------------------------------------------

/// The promise handlers answer a promise response.
pub(crate) proof fn lemma_promise_answers(doc: DocumentBodyV, action: TaskFenceAction, now: Time)
    ensures
        match action {
            TaskFenceAction::Create(c) => c_promise_create(doc, c, now).1 is Promise,
            TaskFenceAction::Settle(st) => c_promise_settle(doc, st, now).1 is Promise,
        },
{
}

pub(crate) proof fn lemma_fence_agrees(
    config: AbstractConfig,
    req: echod_types::TaskFenceReq,
    doc: DocumentBodyV,
    s: AStore,
    now: Time,
)
    requires
        doc_rel(spec_origin_key(origin(req.id@)), doc, s),
        finite_store(s),
    ensures
        request_agrees(config, Request::TaskFence(req), spec_origin_key(origin(req.id@)), doc, s, now),
{
    let request = Request::TaskFence(req);
    let x = req.id@;
    let o = origin(x);
    let key = spec_origin_key(o);
    let action = req.action;
    let target = match action {
        TaskFenceAction::Create(c) => c.id,
        TaskFenceAction::Settle(st) => st.id,
    };
    assert(spec_handle(doc, request, now) == c_fence(doc, req.id, req.version, action, now));
    let outs = spec_handler(config, request, s, now);
    assert(outs == a_fence(req, s, now));
    if target@ == x || !same_origin_spec(target@, x) {
        assert(outs == spec_out(spec_fence_res(400, None), s));
        assert(c_fence(doc, req.id, req.version, action, now) == (doc, Response::TaskFence(TaskFenceRes { status: 400, action: None })));
        lemma_others_same(key, s);
    } else {
        assert(origin(target@) == o);
        lemma_origin_doc(key, o, doc, s);
        let map = spec_workflow_map(doc);
        assert(doc == DocumentBodyV::Workflow(map));
        lemma_held(map, o, s, x, req.version, now);
        let (_, held) = spec_held(map, x, req.version, now);
        assert(spec_with_workflow(doc, map) == doc);
        match held {
            Held::Missing => {
                assert(outs == spec_out(spec_fence_res(404, None), s));
                lemma_others_same(key, s);
            },
            Held::Stale => {
                assert(outs == spec_out(spec_fence_res(409, None), s));
                lemma_others_same(key, s);
            },
            Held::Ok(_) => {
                lemma_promise_answers(doc, action, now);
                match action {
                    TaskFenceAction::Create(c) => {
                        assert(spec_origin_key(origin(c.id@)) == key);
                        lemma_promise_create_agrees(config, c, doc, s, now);
                        let inner_outs = spec_handler(config, Request::PromiseCreate(c), s, now);
                        assert(inner_outs == a_promise_create(c, s, now));
                        let (doc2, response) = c_promise_create(doc, c, now);
                        assert(spec_handle(doc, Request::PromiseCreate(c), now) == (doc2, response));
                        assert(inner_outs.len() == 1);
                        assert(inner_outs[0].resp == response);
                        let inner = response->Promise_0;
                        assert(outs == spec_wrap_fence(inner_outs, true));
                        assert(outs == seq![OutV { resp: spec_fence_res(200, Some(TaskFenceInnerRes::Create(inner))), ..inner_outs[0] }]);
                        assert(c_fence(doc, req.id, req.version, action, now) == (doc2, Response::TaskFence(TaskFenceRes { status: 200, action: Some(TaskFenceInnerRes::Create(inner)) })));
                    },
                    TaskFenceAction::Settle(st) => {
                        assert(spec_origin_key(origin(st.id@)) == key);
                        lemma_promise_settle_agrees(config, st, doc, s, now);
                        let inner_outs = spec_handler(config, Request::PromiseSettle(st), s, now);
                        assert(inner_outs == a_promise_settle(st, s, now));
                        let (doc2, response) = c_promise_settle(doc, st, now);
                        assert(spec_handle(doc, Request::PromiseSettle(st), now) == (doc2, response));
                        assert(inner_outs.len() == 1);
                        assert(inner_outs[0].resp == response);
                        let inner = response->Promise_0;
                        assert(outs == spec_wrap_fence(inner_outs, false));
                        assert(outs == seq![OutV { resp: spec_fence_res(200, Some(TaskFenceInnerRes::Settle(inner))), ..inner_outs[0] }]);
                        assert(c_fence(doc, req.id, req.version, action, now) == (doc2, Response::TaskFence(TaskFenceRes { status: 200, action: Some(TaskFenceInnerRes::Settle(inner)) })));
                    },
                }
            },
        }
    }
}

pub(crate) proof fn lemma_fence_check_agrees(
    config: AbstractConfig,
    req: echod_types::TaskFenceCheckReq,
    doc: DocumentBodyV,
    s: AStore,
    now: Time,
)
    requires
        doc_rel(spec_origin_key(origin(req.id@)), doc, s),
        finite_store(s),
    ensures
        request_agrees(config, Request::TaskFenceCheck(req), spec_origin_key(origin(req.id@)), doc, s, now),
{
    let request = Request::TaskFenceCheck(req);
    let x = req.id@;
    let o = origin(x);
    let key = spec_origin_key(o);
    assert(spec_handle(doc, request, now) == c_fence_check(doc, req.id, req.version, now));
    let outs = spec_handler(config, request, s, now);
    lemma_origin_doc(key, o, doc, s);
    let map = spec_workflow_map(doc);
    assert(doc == DocumentBodyV::Workflow(map));
    lemma_held(map, o, s, x, req.version, now);
    assert(spec_with_workflow(doc, map) == doc);
    assert(outs[0].next == s);
    lemma_others_same(key, s);
}

// ---------------------------------------------------------------------------
// Schedules
// ---------------------------------------------------------------------------

/// A related schedule is the value of the abstract schedule.
pub(crate) proof fn lemma_schedule_value(c: Schedule, a: ScheduleV)
    requires
        schedule_rel(c, a),
    ensures
        c == spec_schedule_value(a),
{
    lemma_string_of(c.id);
    lemma_string_of(c.cron);
    lemma_string_of(c.promise_id);
}

pub(crate) proof fn lemma_schedule_get_agrees(config: AbstractConfig, id: String, doc: DocumentBodyV, s: AStore, now: Time)
    requires
        doc_rel(spec_schedule_key(id@), doc, s),
        finite_store(s),
    ensures
        request_agrees(
            config,
            Request::ScheduleGet(echod_types::ScheduleGetReq { id }),
            spec_schedule_key(id@),
            doc,
            s,
            now,
        ),
{
    let request = Request::ScheduleGet(echod_types::ScheduleGetReq { id });
    let key = spec_schedule_key(id@);
    assert(spec_handle(doc, request, now) == c_schedule_get(doc, id));
    let outs = spec_handler(config, request, s, now);
    lemma_schedule_doc(key, id@, doc, s);
    let slot = doc->Schedule_0;
    match slot {
        Some(sch) => {
            assert(sch.id@ == id@);
            axiom_string_ext(sch.id, id);
            assert(s.schedules.contains_key(id@));
            lemma_schedule_value(sch, s.schedules[id@]);
            assert(outs == spec_out(spec_schedule_res(200, Some(sch)), s));
            assert(c_schedule_get(doc, id) == (doc, Response::Schedule(ScheduleRes { status: 200, schedule: Some(sch) })));
        },
        None => {
            assert(!s.schedules.contains_key(id@));
            assert(outs == spec_out(spec_schedule_res(404, None), s));
        },
    }
    lemma_others_same(key, s);
}

pub(crate) proof fn lemma_schedule_create_agrees(
    config: AbstractConfig,
    req: ScheduleCreateReq,
    doc: DocumentBodyV,
    s: AStore,
    now: Time,
)
    requires
        doc_rel(spec_schedule_key(req.id@), doc, s),
        finite_store(s),
    ensures
        request_agrees(config, Request::ScheduleCreate(req), spec_schedule_key(req.id@), doc, s, now),
{
    let request = Request::ScheduleCreate(req);
    let key = spec_schedule_key(req.id@);
    assert(spec_handle(doc, request, now) == c_schedule_create(doc, req, now));
    let outs = spec_handler(config, request, s, now);
    assert(outs == a_schedule_create(req, s, now));
    lemma_timer(req.promise_tags);
    lemma_targeted(req.promise_tags);
    lemma_schedule_doc(key, req.id@, doc, s);
    lemma_schedule_key(req.id@);
    let slot = doc->Schedule_0;
    let next_run_at = echod_abstract_spec::axioms::spec_next_cron(req.cron@, now);
    if !spec_deadline_bounded(next_run_at, req.promise_timeout)
        || (spec_targeted(req.promise_tags) && spec_timer(req.promise_tags)) {
        assert(outs == spec_out(spec_schedule_res(400, None), s));
        lemma_others_same(key, s);
    } else {
        match slot {
            Some(sch) => {
                assert(s.schedules.contains_key(req.id@));
                lemma_schedule_value(sch, s.schedules[req.id@]);
                assert(outs == spec_out(spec_schedule_res(200, Some(sch)), s));
                assert(c_schedule_create(doc, req, now) == (doc, Response::Schedule(ScheduleRes { status: 200, schedule: Some(sch) })));
                lemma_others_same(key, s);
            },
            None => {
                assert(!s.schedules.contains_key(req.id@));
                let schedule = Schedule {
                    id: req.id,
                    cron: req.cron,
                    promise_id: req.promise_id,
                    promise_timeout: req.promise_timeout,
                    promise_param: req.promise_param,
                    promise_tags: req.promise_tags,
                    next_run_at,
                    last_run_at: None,
                    created_at: now,
                };
                let c = ScheduleV {
                    id: req.id@,
                    cron: req.cron@,
                    promise_id: req.promise_id@,
                    promise_timeout: req.promise_timeout,
                    promise_param: req.promise_param,
                    promise_tags: req.promise_tags,
                    created_at: now,
                    next_run_at,
                    last_run_at: None,
                };
                let next = AStore { schedules: s.schedules.insert(req.id@, c), ..s };
                assert(outs == spec_out(spec_schedule_res(200, Some(schedule)), next));
                assert(c_schedule_create(doc, req, now) == (DocumentBodyV::Schedule(Some(schedule)), Response::Schedule(ScheduleRes { status: 200, schedule: Some(schedule) })));
                assert(schedule_rel(schedule, c));
                assert(slot_rel(Some(schedule), req.id@, next));
                assert(doc_rel(key, DocumentBodyV::Schedule(Some(schedule)), next));
                lemma_others_kept_schedule(s, next, req.id@);
                assert(next.schedules.dom() == s.schedules.dom().insert(req.id@));
                assert(finite_store(next));
            },
        }
    }
}

pub(crate) proof fn lemma_schedule_delete_agrees(config: AbstractConfig, id: String, doc: DocumentBodyV, s: AStore, now: Time)
    requires
        doc_rel(spec_schedule_key(id@), doc, s),
        finite_store(s),
    ensures
        request_agrees(
            config,
            Request::ScheduleDelete(echod_types::ScheduleDeleteReq { id }),
            spec_schedule_key(id@),
            doc,
            s,
            now,
        ),
{
    let request = Request::ScheduleDelete(echod_types::ScheduleDeleteReq { id });
    let key = spec_schedule_key(id@);
    assert(spec_handle(doc, request, now) == c_schedule_delete(doc, id));
    let outs = spec_handler(config, request, s, now);
    lemma_schedule_doc(key, id@, doc, s);
    lemma_schedule_key(id@);
    let slot = doc->Schedule_0;
    match slot {
        Some(sch) => {
            assert(sch.id@ == id@);
            axiom_string_ext(sch.id, id);
            assert(s.schedules.contains_key(id@));
            let next = AStore { schedules: s.schedules.remove(id@), ..s };
            assert(outs == spec_out(spec_status_res(200), next));
            assert(c_schedule_delete(doc, id) == (DocumentBodyV::Schedule(None), Response::Status(StatusRes { status: 200 })));
            assert(!next.schedules.contains_key(id@));
            assert(slot_rel(None, id@, next));
            assert(doc_rel(key, DocumentBodyV::Schedule(None), next));
            lemma_others_kept_schedule(s, next, id@);
            assert(next.schedules.dom() == s.schedules.dom().remove(id@));
            assert(finite_store(next));
        },
        None => {
            assert(!s.schedules.contains_key(id@));
            assert(outs == spec_out(spec_status_res(404), s));
            lemma_others_same(key, s);
        },
    }
}

// ---------------------------------------------------------------------------
// Every request
// ---------------------------------------------------------------------------

/// One request with a key agrees on the document under that key.
pub(crate) proof fn lemma_request_agrees(
    config: AbstractConfig,
    request: Request,
    key: Seq<char>,
    doc: DocumentBodyV,
    s: AStore,
    now: Time,
)
    requires
        spec_key(request) == Some(key),
        doc_rel(key, doc, s),
        finite_store(s),
    ensures
        request_agrees(config, request, key, doc, s, now),
{
    match request {
        Request::PromiseGet(_) | Request::PromiseCreate(_) | Request::PromiseSettle(_) => {
            lemma_promise_handlers_agree(config, request, doc, s, now);
        },
        Request::PromiseRegisterCallback(q) => lemma_register_callback_agrees(config, q, doc, s, now),
        Request::PromiseRegisterListener(q) => lemma_register_listener_agrees(config, q, doc, s, now),
        Request::TaskGet(q) => lemma_task_get_agrees(config, q.id, doc, s, now),
        Request::TaskCreate(q) => lemma_task_create_agrees(config, q, doc, s, now),
        Request::TaskAcquire(q) => lemma_task_acquire_agrees(config, q, doc, s, now),
        Request::TaskFulfill(q) => lemma_task_fulfill_agrees(config, q, doc, s, now),
        Request::TaskRelease(q) => lemma_task_release_agrees(config, q, doc, s, now),
        Request::TaskHalt(q) => lemma_task_halt_agrees(config, q.id, doc, s, now),
        Request::TaskContinue(q) => lemma_task_continue_agrees(config, q.id, doc, s, now),
        Request::TaskFence(q) => lemma_fence_agrees(config, q, doc, s, now),
        Request::TaskFenceCheck(q) => lemma_fence_check_agrees(config, q, doc, s, now),
        Request::TaskSuspend(q) => lemma_suspend_agrees(config, q, doc, s, now),
        Request::TaskHeartbeat(q) => {
            assert(q.tasks@.len() > 0);
            lemma_heartbeat_agrees(config, q, doc, s, now);
        },
        Request::ScheduleGet(q) => lemma_schedule_get_agrees(config, q.id, doc, s, now),
        Request::ScheduleDelete(q) => lemma_schedule_delete_agrees(config, q.id, doc, s, now),
        Request::ScheduleCreate(q) => lemma_schedule_create_agrees(config, q, doc, s, now),
    }
}

/// Lean's `refinement_handlers`, for the requests.
pub(crate) proof fn lemma_requests_agree(config: AbstractConfig)
    ensures
        super::relation::requests_agree(config),
{
    assert forall|request: Request, key: Seq<char>, doc: DocumentBodyV, s: AStore, now: u64|
        spec_key(request) == Some(key) && doc_rel(key, doc, s) && finite_store(s) implies #[trigger] request_agrees(
        config,
        request,
        key,
        doc,
        s,
        now,
    ) by {
        lemma_request_agrees(config, request, key, doc, s, now);
    };
}

} // verus!

}

mod work {
//! The due step and the occurrence agree.
//!
//! The concrete node walks one document and takes the first thing due in
//! it; the abstract service offers every timeout of every object. This
//! module finds the concrete choice among the abstract offers: the key
//! order ([`lemma_sorted`]), membership in the offers
//! ([`lemma_timeout_offered`]), and then each branch of
//! `spec_step_object` against its abstract counterpart. The occurrence is
//! Lean's `createPromiseAt` against `spec_create_if_absent`. The module ends
//! in [`lemma_agreement`]: at the configuration the node implements, the
//! handlers, the due step, and the occurrence all agree. Cargo erases these
//! bodies; a Verus run is what checks them.

use vstd::prelude::*;
use echod_types::{MAX_TIME, MAX_VERSION};
#[cfg(verus_keep_ghost)]
use echod_types::spec_deadline_bounded;

#[cfg(verus_keep_ghost)]
use super::requests::{
    lemma_finite_at, lemma_promises_kept, lemma_skip_no_duplicates, lemma_tasks_kept,
    lemma_within_one,
};
#[cfg(verus_keep_ghost)]
use super::interpretation::{
    abstract_task, callbacks_in, changed_within, doc_rel, finite_store, lemma_contains_to_set,
    lemma_empty_to_set, lemma_offer, lemma_origin_doc, lemma_origin_reads, lemma_origin_update,
    lemma_others_kept_schedule, lemma_others_kept_within, lemma_project_object, lemma_record,
    lemma_sat_add, lemma_schedule_key, lemma_starts_split, lemma_string_view, lemma_targeted,
    lemma_timer, object_rel, origin_prefix, origin_rel, promise_rel, schedule_prefix, schedule_rel,
    slot_rel, task_rel,
};
#[cfg(verus_keep_ghost)]
use echod_concrete_spec::rover::{spec_string as c_string};
#[cfg(verus_keep_ghost)]
use echod_concrete_spec::state::{
    lemma_min_key_present as c_lemma_min_key, DocumentBodyV, NoteV, ObjV, PendingV, PromV, spec_due_id,
    spec_min_key as c_min_key, spec_new_obj, spec_obj_due, spec_occurrence, spec_offer_at,
    spec_opened, spec_origin_key, spec_workflow_map, spec_project_obj, spec_record, spec_resume,
    spec_run_due, spec_schedule_key, spec_sorted as c_sorted, spec_step_object, spec_targeted,
    spec_timer, spec_unlease as c_unlease, TkV,
};
#[cfg(verus_keep_ghost)]
use echod_concrete_spec::state::{spec_sat_add, spec_starts};
#[cfg(verus_keep_ghost)]
use super::relation::{
    agreement, as_item, due_agrees, dues_agree, items, note_sends, occurrence_agrees,
    occurrences_agree,
};
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::state::{
    spec_has_target, spec_is_timer, spec_lease_at, spec_new_object, spec_project_promise, spec_project_task, spec_promise_record, spec_string as a_string, spec_unlease as a_unlease,
};
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::state::{
    spec_callback, spec_callback_apply, spec_create_if_absent, spec_did, spec_lease, spec_listener, spec_process_work, spec_retry, spec_schedule_step,
};
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::rover::{
    Pid as APid, spec_derived, spec_due_result, spec_keep, spec_over_callbacks, spec_over_listeners,
    spec_over_promises, spec_over_schedules, spec_over_tasks, spec_queue, spec_run_timeout, Proc,
};
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::state::{
    DispatchV, InOutV, InternalV, lemma_lift_dispatch, lemma_min_key as a_lemma_min_key,
    lift_dispatch, PromiseV, sat_add, ScheduleV, spec_keys, spec_min_key as a_min_key,
    spec_sorted as a_sorted, StoreV as AStore, TaskV,
};
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::protocol::Message as AMessage;
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::axioms::{pset_seq, spec_expand, spec_next_cron};
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::{Config as AbstractConfig, Dispatch, Output};
#[cfg(verus_keep_ghost)]
use rover_spec::rover::RoverSpec::StepResultV;
#[cfg(verus_keep_ghost)]
use rover_spec::rover::comm::{Sched, Time};
#[cfg(verus_keep_ghost)]
use echod_types::{origin, PromiseRecord, PromiseState, Response, Schedule, TaskState};

verus! {

broadcast use
    vstd::seq::group_seq_lemmas,
    vstd::set::group_set_lemmas,
    echod_abstract_spec::state::group_views;

/// One abstract step result.
#[cfg(verus_keep_ghost)]
pub(crate) type AResult = StepResultV<Proc, APid, AMessage>;

// ---------------------------------------------------------------------------
// The key order
// ---------------------------------------------------------------------------

/// The chosen minimums, both of them, are keys.
pub(crate) proof fn lemma_min_key(keys: Set<Seq<char>>)
    requires
        keys.finite(),
        keys.len() > 0,
    ensures
        keys.contains(c_min_key(keys)),
        keys.contains(a_min_key(keys)),
{
    c_lemma_min_key(keys);
    a_lemma_min_key(keys);
}

/// The concrete sorted keys are the keys.
pub(crate) proof fn lemma_c_sorted(keys: Set<Seq<char>>)
    requires
        keys.finite(),
    ensures
        c_sorted(keys).len() == keys.len(),
        forall|i: int| 0 <= i < keys.len() ==> keys.contains(#[trigger] c_sorted(keys)[i]),
        forall|id: Seq<char>| keys.contains(id) ==> c_sorted(keys).contains(id),
    decreases keys.len(),
{
    if keys.len() == 0 {
        assert(c_sorted(keys) == Seq::<Seq<char>>::empty());
    } else {
        lemma_min_key(keys);
        let k = c_min_key(keys);
        let rest = keys.remove(k);
        assert(rest.len() == keys.len() - 1);
        lemma_c_sorted(rest);
        let sorted = c_sorted(keys);
        assert(sorted == seq![k] + c_sorted(rest));
        assert forall|i: int| 0 <= i < keys.len() implies keys.contains(#[trigger] sorted[i]) by {
            if i > 0 {
                assert(sorted[i] == c_sorted(rest)[i - 1]);
            }
        };
        assert forall|id: Seq<char>| keys.contains(id) implies sorted.contains(id) by {
            if id == k {
                assert(sorted[0] == k);
            } else {
                assert(rest.contains(id));
                let j = choose|j: int| 0 <= j < c_sorted(rest).len() && c_sorted(rest)[j] == id;
                assert(sorted[j + 1] == id);
            }
        };
    }
}

/// The abstract sorted keys are the keys.
pub(crate) proof fn lemma_a_sorted(keys: Set<Seq<char>>)
    requires
        keys.finite(),
    ensures
        a_sorted(keys).len() == keys.len(),
        forall|i: int| 0 <= i < keys.len() ==> keys.contains(#[trigger] a_sorted(keys)[i]),
        forall|id: Seq<char>| keys.contains(id) ==> a_sorted(keys).contains(id),
    decreases keys.len(),
{
    if keys.len() == 0 {
        assert(a_sorted(keys) == Seq::<Seq<char>>::empty());
    } else {
        lemma_min_key(keys);
        let k = a_min_key(keys);
        let rest = keys.remove(k);
        assert(rest.len() == keys.len() - 1);
        lemma_a_sorted(rest);
        let sorted = a_sorted(keys);
        assert(sorted == seq![k] + a_sorted(rest));
        assert forall|i: int| 0 <= i < keys.len() implies keys.contains(#[trigger] sorted[i]) by {
            if i > 0 {
                assert(sorted[i] == a_sorted(rest)[i - 1]);
            }
        };
        assert forall|id: Seq<char>| keys.contains(id) implies sorted.contains(id) by {
            if id == k {
                assert(sorted[0] == k);
            } else {
                assert(rest.contains(id));
                let j = choose|j: int| 0 <= j < a_sorted(rest).len() && a_sorted(rest)[j] == id;
                assert(sorted[j + 1] == id);
            }
        };
    }
}

/// The sorted keys are the keys, on both sides.
pub(crate) proof fn lemma_sorted(keys: Set<Seq<char>>)
    requires
        keys.finite(),
    ensures
        c_sorted(keys).len() == keys.len(),
        a_sorted(keys).len() == keys.len(),
        forall|i: int| 0 <= i < keys.len() ==> keys.contains(#[trigger] c_sorted(keys)[i]),
        forall|i: int| 0 <= i < keys.len() ==> keys.contains(#[trigger] a_sorted(keys)[i]),
        forall|id: Seq<char>| keys.contains(id) ==> c_sorted(keys).contains(id),
        forall|id: Seq<char>| keys.contains(id) ==> a_sorted(keys).contains(id),
{
    lemma_c_sorted(keys);
    lemma_a_sorted(keys);
}

/// The first due id is an id of the document.
pub(crate) proof fn lemma_due_id(map: Map<Seq<char>, ObjV>, keys: Seq<Seq<char>>, now: Time)
    requires
        forall|i: int| 0 <= i < keys.len() ==> map.contains_key(#[trigger] keys[i]),
    ensures
        match spec_due_id(map, keys, now) {
            Some(id) => map.contains_key(id),
            None => true,
        },
    decreases keys.len(),
{
    if keys.len() == 0 {
    } else if spec_obj_due(map[keys[0]], now) is Some {
    } else {
        let rest = keys.drop_first();
        assert forall|i: int| 0 <= i < rest.len() implies map.contains_key(#[trigger] rest[i]) by {
            assert(rest[i] == keys[i + 1]);
        };
        lemma_due_id(map, rest, now);
    }
}

// ---------------------------------------------------------------------------
// Membership in the offers
// ---------------------------------------------------------------------------

/// The response of `work`, when due, is among `results`.
pub(crate) open spec fn offered(
    config: AbstractConfig,
    state: Proc,
    now: Time,
    work: InternalV,
    results: Seq<AResult>,
) -> bool {
    let response = spec_process_work(config, work, state.store, now);
    !response.not_due ==> results.contains(spec_due_result(state, response))
}

pub(crate) proof fn lemma_contains_left<T>(a: Seq<T>, b: Seq<T>, x: T)
    requires
        a.contains(x),
    ensures
        (a + b).contains(x),
{
    let j = choose|j: int| 0 <= j < a.len() && a[j] == x;
    assert((a + b)[j] == x);
}

pub(crate) proof fn lemma_contains_right<T>(a: Seq<T>, b: Seq<T>, x: T)
    requires
        b.contains(x),
    ensures
        (a + b).contains(x),
{
    let j = choose|j: int| 0 <= j < b.len() && b[j] == x;
    assert((a + b)[a.len() + j] == x);
}

pub(crate) proof fn lemma_offered_left(
    config: AbstractConfig,
    state: Proc,
    now: Time,
    work: InternalV,
    a: Seq<AResult>,
    b: Seq<AResult>,
)
    requires
        offered(config, state, now, work, a),
    ensures
        offered(config, state, now, work, a + b),
{
    let response = spec_process_work(config, work, state.store, now);
    if !response.not_due {
        lemma_contains_left(a, b, spec_due_result(state, response));
    }
}

pub(crate) proof fn lemma_offered_right(
    config: AbstractConfig,
    state: Proc,
    now: Time,
    work: InternalV,
    a: Seq<AResult>,
    b: Seq<AResult>,
)
    requires
        offered(config, state, now, work, b),
    ensures
        offered(config, state, now, work, a + b),
{
    let response = spec_process_work(config, work, state.store, now);
    if !response.not_due {
        lemma_contains_right(a, b, spec_due_result(state, response));
    }
}

pub(crate) proof fn lemma_keep_offered(config: AbstractConfig, state: Proc, now: Time, work: InternalV)
    ensures
        offered(config, state, now, work, spec_keep(config, state, now, work, Seq::empty())),
{
    let response = spec_process_work(config, work, state.store, now);
    if !response.not_due {
        let r = spec_due_result(state, response);
        let kept = spec_keep(config, state, now, work, Seq::empty());
        assert(kept == seq![r] + Seq::<AResult>::empty());
        assert(kept[0] == r);
    }
}

pub(crate) proof fn lemma_over_callbacks_offered(
    config: AbstractConfig,
    state: Proc,
    now: Time,
    awaited: Seq<char>,
    awaiters: Seq<Seq<char>>,
    awaiter: Seq<char>,
)
    requires
        awaiters.contains(awaiter),
    ensures
        offered(
            config,
            state,
            now,
            InternalV::Callback { awaited, awaiter },
            spec_over_callbacks(config, state, now, awaited, awaiters),
        ),
    decreases awaiters.len(),
{
    let work = InternalV::Callback { awaited, awaiter };
    let head = spec_keep(
        config,
        state,
        now,
        InternalV::Callback { awaited, awaiter: awaiters[0] },
        Seq::empty(),
    );
    let tail = spec_over_callbacks(config, state, now, awaited, awaiters.drop_first());
    assert(spec_over_callbacks(config, state, now, awaited, awaiters) == head + tail);
    if awaiters[0] == awaiter {
        lemma_keep_offered(config, state, now, work);
        lemma_offered_left(config, state, now, work, head, tail);
    } else {
        let j = choose|j: int| 0 <= j < awaiters.len() && awaiters[j] == awaiter;
        assert(awaiters.drop_first()[j - 1] == awaiter);
        lemma_over_callbacks_offered(config, state, now, awaited, awaiters.drop_first(), awaiter);
        lemma_offered_right(config, state, now, work, head, tail);
    }
}

pub(crate) proof fn lemma_over_listeners_offered(
    config: AbstractConfig,
    state: Proc,
    now: Time,
    awaited: Seq<char>,
    addresses: Seq<Seq<char>>,
    address: Seq<char>,
)
    requires
        addresses.contains(address),
    ensures
        offered(
            config,
            state,
            now,
            InternalV::Listener { awaited, address },
            spec_over_listeners(config, state, now, awaited, addresses),
        ),
    decreases addresses.len(),
{
    let work = InternalV::Listener { awaited, address };
    let head = spec_keep(
        config,
        state,
        now,
        InternalV::Listener { awaited, address: addresses[0] },
        Seq::empty(),
    );
    let tail = spec_over_listeners(config, state, now, awaited, addresses.drop_first());
    assert(spec_over_listeners(config, state, now, awaited, addresses) == head + tail);
    if addresses[0] == address {
        lemma_keep_offered(config, state, now, work);
        lemma_offered_left(config, state, now, work, head, tail);
    } else {
        let j = choose|j: int| 0 <= j < addresses.len() && addresses[j] == address;
        assert(addresses.drop_first()[j - 1] == address);
        lemma_over_listeners_offered(config, state, now, awaited, addresses.drop_first(), address);
        lemma_offered_right(config, state, now, work, head, tail);
    }
}

/// What the promises offer: every promise's timeout, every callback, every
/// listener.
pub(crate) open spec fn promise_offers(
    config: AbstractConfig,
    state: Proc,
    now: Time,
    id: Seq<char>,
    results: Seq<AResult>,
) -> bool {
    let p = state.store.promises[id];
    &&& offered(config, state, now, InternalV::PromiseTimeout(id), results)
    &&& forall|awaiter: Seq<char>|
        #[trigger] p.callbacks.contains(awaiter) ==> offered(
            config,
            state,
            now,
            InternalV::Callback { awaited: id, awaiter },
            results,
        )
    &&& forall|address: Seq<char>|
        #[trigger] p.listeners.contains(address) ==> offered(
            config,
            state,
            now,
            InternalV::Listener { awaited: id, address },
            results,
        )
}

pub(crate) proof fn lemma_promise_offers_left(
    config: AbstractConfig,
    state: Proc,
    now: Time,
    id: Seq<char>,
    a: Seq<AResult>,
    b: Seq<AResult>,
)
    requires
        promise_offers(config, state, now, id, a),
    ensures
        promise_offers(config, state, now, id, a + b),
{
    let p = state.store.promises[id];
    lemma_offered_left(config, state, now, InternalV::PromiseTimeout(id), a, b);
    assert forall|awaiter: Seq<char>| #[trigger] p.callbacks.contains(awaiter) implies offered(
        config,
        state,
        now,
        InternalV::Callback { awaited: id, awaiter },
        a + b,
    ) by {
        lemma_offered_left(config, state, now, InternalV::Callback { awaited: id, awaiter }, a, b);
    };
    assert forall|address: Seq<char>| #[trigger] p.listeners.contains(address) implies offered(
        config,
        state,
        now,
        InternalV::Listener { awaited: id, address },
        a + b,
    ) by {
        lemma_offered_left(config, state, now, InternalV::Listener { awaited: id, address }, a, b);
    };
}

pub(crate) proof fn lemma_promise_offers_right(
    config: AbstractConfig,
    state: Proc,
    now: Time,
    id: Seq<char>,
    a: Seq<AResult>,
    b: Seq<AResult>,
)
    requires
        promise_offers(config, state, now, id, b),
    ensures
        promise_offers(config, state, now, id, a + b),
{
    let p = state.store.promises[id];
    lemma_offered_right(config, state, now, InternalV::PromiseTimeout(id), a, b);
    assert forall|awaiter: Seq<char>| #[trigger] p.callbacks.contains(awaiter) implies offered(
        config,
        state,
        now,
        InternalV::Callback { awaited: id, awaiter },
        a + b,
    ) by {
        lemma_offered_right(config, state, now, InternalV::Callback { awaited: id, awaiter }, a, b);
    };
    assert forall|address: Seq<char>| #[trigger] p.listeners.contains(address) implies offered(
        config,
        state,
        now,
        InternalV::Listener { awaited: id, address },
        a + b,
    ) by {
        lemma_offered_right(config, state, now, InternalV::Listener { awaited: id, address }, a, b);
    };
}

pub(crate) proof fn lemma_over_promises_offered(
    config: AbstractConfig,
    state: Proc,
    now: Time,
    keys: Seq<Seq<char>>,
    id: Seq<char>,
)
    requires
        keys.contains(id),
    ensures
        promise_offers(config, state, now, id, spec_over_promises(config, state, now, keys)),
    decreases keys.len(),
{
    let head = keys[0];
    let p = state.store.promises[head];
    let a = spec_keep(config, state, now, InternalV::PromiseTimeout(head), Seq::empty());
    let b = spec_over_callbacks(config, state, now, head, pset_seq(p.callbacks));
    let c = spec_over_listeners(config, state, now, head, pset_seq(p.listeners));
    let d = spec_over_promises(config, state, now, keys.drop_first());
    assert(spec_over_promises(config, state, now, keys) == a + b + c + d);
    if head == id {
        lemma_keep_offered(config, state, now, InternalV::PromiseTimeout(id));
        lemma_offered_left(config, state, now, InternalV::PromiseTimeout(id), a, b);
        assert forall|awaiter: Seq<char>| #[trigger] p.callbacks.contains(awaiter) implies offered(
            config,
            state,
            now,
            InternalV::Callback { awaited: id, awaiter },
            a + b,
        ) by {
            assert(pset_seq(p.callbacks).to_set().contains(awaiter));
            lemma_contains_to_set(pset_seq(p.callbacks), awaiter);
            lemma_over_callbacks_offered(config, state, now, id, pset_seq(p.callbacks), awaiter);
            lemma_offered_right(config, state, now, InternalV::Callback { awaited: id, awaiter }, a, b);
        };
        assert forall|address: Seq<char>| #[trigger] p.listeners.contains(address) implies offered(
            config,
            state,
            now,
            InternalV::Listener { awaited: id, address },
            a + b + c,
        ) by {
            assert(pset_seq(p.listeners).to_set().contains(address));
            lemma_contains_to_set(pset_seq(p.listeners), address);
            lemma_over_listeners_offered(config, state, now, id, pset_seq(p.listeners), address);
            lemma_offered_right(config, state, now, InternalV::Listener { awaited: id, address }, a + b, c);
        };
        lemma_offered_left(config, state, now, InternalV::PromiseTimeout(id), a + b, c);
        assert forall|awaiter: Seq<char>| #[trigger] p.callbacks.contains(awaiter) implies offered(
            config,
            state,
            now,
            InternalV::Callback { awaited: id, awaiter },
            a + b + c,
        ) by {
            lemma_offered_left(config, state, now, InternalV::Callback { awaited: id, awaiter }, a + b, c);
        };
        assert(promise_offers(config, state, now, id, a + b + c));
        lemma_promise_offers_left(config, state, now, id, a + b + c, d);
    } else {
        let j = choose|j: int| 0 <= j < keys.len() && keys[j] == id;
        assert(keys.drop_first()[j - 1] == id);
        lemma_over_promises_offered(config, state, now, keys.drop_first(), id);
        lemma_promise_offers_right(config, state, now, id, a + b + c, d);
    }
}

/// What the tasks offer: every lease, and the retry of every task that has
/// one.
pub(crate) open spec fn task_offers(
    config: AbstractConfig,
    state: Proc,
    now: Time,
    id: Seq<char>,
    results: Seq<AResult>,
) -> bool {
    &&& offered(config, state, now, InternalV::TaskLeaseTimeout(id), results)
    &&& state.store.tasks[id].retry_timeout_at is Some ==> offered(
        config,
        state,
        now,
        InternalV::TaskRetryTimeout(id),
        results,
    )
}

pub(crate) proof fn lemma_over_tasks_offered(
    config: AbstractConfig,
    state: Proc,
    now: Time,
    keys: Seq<Seq<char>>,
    id: Seq<char>,
)
    requires
        keys.contains(id),
    ensures
        task_offers(config, state, now, id, spec_over_tasks(config, state, now, keys)),
    decreases keys.len(),
{
    let head = keys[0];
    let t = state.store.tasks[head];
    let lease = spec_keep(config, state, now, InternalV::TaskLeaseTimeout(head), Seq::empty());
    let retry = match t.retry_timeout_at {
        Some(_) => spec_keep(config, state, now, InternalV::TaskRetryTimeout(head), Seq::empty()),
        None => Seq::<AResult>::empty(),
    };
    let rest = spec_over_tasks(config, state, now, keys.drop_first());
    assert(spec_over_tasks(config, state, now, keys) == lease + retry + rest);
    if head == id {
        lemma_keep_offered(config, state, now, InternalV::TaskLeaseTimeout(id));
        lemma_offered_left(config, state, now, InternalV::TaskLeaseTimeout(id), lease, retry);
        lemma_offered_left(config, state, now, InternalV::TaskLeaseTimeout(id), lease + retry, rest);
        if t.retry_timeout_at is Some {
            lemma_keep_offered(config, state, now, InternalV::TaskRetryTimeout(id));
            lemma_offered_right(config, state, now, InternalV::TaskRetryTimeout(id), lease, retry);
            lemma_offered_left(config, state, now, InternalV::TaskRetryTimeout(id), lease + retry, rest);
        }
    } else {
        let j = choose|j: int| 0 <= j < keys.len() && keys[j] == id;
        assert(keys.drop_first()[j - 1] == id);
        lemma_over_tasks_offered(config, state, now, keys.drop_first(), id);
        lemma_offered_right(config, state, now, InternalV::TaskLeaseTimeout(id), lease + retry, rest);
        if state.store.tasks[id].retry_timeout_at is Some {
            lemma_offered_right(config, state, now, InternalV::TaskRetryTimeout(id), lease + retry, rest);
        }
    }
}

/// The timeout work of a schedule.
pub(crate) open spec fn schedule_work(s: AStore, id: Seq<char>) -> InternalV {
    let c = s.schedules[id];
    InternalV::ScheduleTimeout { id, promise: spec_expand(c.promise_id, id, c.next_run_at) }
}

pub(crate) proof fn lemma_over_schedules_offered(
    config: AbstractConfig,
    state: Proc,
    now: Time,
    keys: Seq<Seq<char>>,
    id: Seq<char>,
)
    requires
        keys.contains(id),
    ensures
        offered(
            config,
            state,
            now,
            schedule_work(state.store, id),
            spec_over_schedules(config, state, now, keys),
        ),
    decreases keys.len(),
{
    let head = keys[0];
    let first = spec_keep(config, state, now, schedule_work(state.store, head), Seq::empty());
    let rest = spec_over_schedules(config, state, now, keys.drop_first());
    assert(spec_over_schedules(config, state, now, keys) == first + rest);
    if head == id {
        lemma_keep_offered(config, state, now, schedule_work(state.store, id));
        lemma_offered_left(config, state, now, schedule_work(state.store, id), first, rest);
    } else {
        let j = choose|j: int| 0 <= j < keys.len() && keys[j] == id;
        assert(keys.drop_first()[j - 1] == id);
        lemma_over_schedules_offered(config, state, now, keys.drop_first(), id);
        lemma_offered_right(config, state, now, schedule_work(state.store, id), first, rest);
    }
}

/// Everything the abstract timeout step offers, by object.
pub(crate) proof fn lemma_timeout_offered(config: AbstractConfig, state: Proc, now: Time)
    requires
        finite_store(state.store),
    ensures
        forall|id: Seq<char>|
            #[trigger] state.store.promises.contains_key(id) ==> promise_offers(
                config,
                state,
                now,
                id,
                spec_run_timeout(config, state, now),
            ),
        forall|id: Seq<char>|
            #[trigger] state.store.tasks.contains_key(id) ==> task_offers(
                config,
                state,
                now,
                id,
                spec_run_timeout(config, state, now),
            ),
        forall|id: Seq<char>|
            #[trigger] state.store.schedules.contains_key(id) ==> offered(
                config,
                state,
                now,
                schedule_work(state.store, id),
                spec_run_timeout(config, state, now),
            ),
{
    let s = state.store;
    let queued = spec_queue(config, state, now, 0);
    let op = spec_over_promises(config, state, now, spec_keys(s.promises));
    let ot = spec_over_tasks(config, state, now, spec_keys(s.tasks));
    let os = spec_over_schedules(config, state, now, spec_keys(s.schedules));
    let results = spec_run_timeout(config, state, now);
    assert(spec_derived(config, state, now) == op + ot + os);
    assert(results == queued + (op + ot + os));
    lemma_sorted(s.promises.dom());
    lemma_sorted(s.tasks.dom());
    lemma_sorted(s.schedules.dom());
    assert forall|id: Seq<char>| #[trigger] s.promises.contains_key(id) implies promise_offers(
        config,
        state,
        now,
        id,
        results,
    ) by {
        assert(s.promises.dom().contains(id));
        lemma_over_promises_offered(config, state, now, spec_keys(s.promises), id);
        lemma_promise_offers_left(config, state, now, id, op, ot);
        lemma_promise_offers_left(config, state, now, id, op + ot, os);
        lemma_promise_offers_right(config, state, now, id, queued, op + ot + os);
    };
    assert forall|id: Seq<char>| #[trigger] s.tasks.contains_key(id) implies task_offers(
        config,
        state,
        now,
        id,
        results,
    ) by {
        assert(s.tasks.dom().contains(id));
        lemma_over_tasks_offered(config, state, now, spec_keys(s.tasks), id);
        lemma_offered_right(config, state, now, InternalV::TaskLeaseTimeout(id), op, ot);
        lemma_offered_left(config, state, now, InternalV::TaskLeaseTimeout(id), op + ot, os);
        lemma_offered_right(config, state, now, InternalV::TaskLeaseTimeout(id), queued, op + ot + os);
        if s.tasks[id].retry_timeout_at is Some {
            lemma_offered_right(config, state, now, InternalV::TaskRetryTimeout(id), op, ot);
            lemma_offered_left(config, state, now, InternalV::TaskRetryTimeout(id), op + ot, os);
            lemma_offered_right(config, state, now, InternalV::TaskRetryTimeout(id), queued, op + ot + os);
        }
    };
    assert forall|id: Seq<char>| #[trigger] s.schedules.contains_key(id) implies offered(
        config,
        state,
        now,
        schedule_work(s, id),
        results,
    ) by {
        assert(s.schedules.dom().contains(id));
        lemma_over_schedules_offered(config, state, now, spec_keys(s.schedules), id);
        lemma_offered_right(config, state, now, schedule_work(s, id), op + ot, os);
        lemma_offered_right(config, state, now, schedule_work(s, id), queued, op + ot + os);
    };
}

/// `work` names objects the store holds, so the timeout step offers it.
pub(crate) open spec fn work_known(s: AStore, work: InternalV) -> bool {
    match work {
        InternalV::PromiseTimeout(id) => s.promises.contains_key(id),
        InternalV::Callback { awaited, awaiter } => s.promises.contains_key(awaited)
            && s.promises[awaited].callbacks.contains(awaiter),
        InternalV::Listener { awaited, address } => s.promises.contains_key(awaited)
            && s.promises[awaited].listeners.contains(address),
        InternalV::TaskLeaseTimeout(id) => s.tasks.contains_key(id),
        InternalV::TaskRetryTimeout(id) => s.tasks.contains_key(id)
            && s.tasks[id].retry_timeout_at is Some,
        InternalV::ScheduleTimeout { id, promise } => s.schedules.contains_key(id)
            && work == schedule_work(s, id),
        InternalV::Occurrence { .. } => false,
    }
}

/// One offer, read off [`lemma_timeout_offered`]. The universal facts stay
/// inside this lemma.
pub(crate) proof fn lemma_work_offered(config: AbstractConfig, state: Proc, now: Time, work: InternalV)
    requires
        finite_store(state.store),
        work_known(state.store, work),
    ensures
        offered(config, state, now, work, spec_run_timeout(config, state, now)),
{
    lemma_timeout_offered(config, state, now);
    let results = spec_run_timeout(config, state, now);
    match work {
        InternalV::PromiseTimeout(id) => {
            assert(promise_offers(config, state, now, id, results));
        },
        InternalV::Callback { awaited, awaiter } => {
            assert(promise_offers(config, state, now, awaited, results));
        },
        InternalV::Listener { awaited, address } => {
            assert(promise_offers(config, state, now, awaited, results));
        },
        InternalV::TaskLeaseTimeout(id) => {
            assert(task_offers(config, state, now, id, results));
        },
        InternalV::TaskRetryTimeout(id) => {
            assert(task_offers(config, state, now, id, results));
        },
        InternalV::ScheduleTimeout { id, promise } => {
            assert(offered(config, state, now, schedule_work(state.store, id), results));
        },
        InternalV::Occurrence { .. } => {},
    }
}

// ---------------------------------------------------------------------------
// Dispatches and sends
// ---------------------------------------------------------------------------

/// A lifted execute is the execute of the string.
pub(crate) proof fn lemma_lift_execute(id: Seq<char>, version: u64)
    ensures
        lift_dispatch(DispatchV::Execute { id, version }) == (Dispatch::Execute { id: c_string(id), version }),
{
    let d = Dispatch::Execute { id: c_string(id), version };
    lemma_string_view(id);
    assert(d@ == DispatchV::Execute { id, version });
    lemma_lift_dispatch(d);
}

/// A lifted unblock is the unblock of the string.
pub(crate) proof fn lemma_lift_unblock(address: Seq<char>, promise: PromiseRecord)
    ensures
        lift_dispatch(DispatchV::Unblock { address, promise }) == (Dispatch::Unblock {
            address: c_string(address),
            promise,
        }),
{
    let d = Dispatch::Unblock { address: c_string(address), promise };
    lemma_string_view(address);
    assert(d@ == DispatchV::Unblock { address, promise });
    lemma_lift_dispatch(d);
}

/// The sends of a due result, from its dispatches.
pub(crate) open spec fn sends_of(send: Seq<DispatchV>) -> Seq<(APid, AMessage)> {
    send.map_values(|dispatch: DispatchV| (
        APid::Outside,
        AMessage::Output(Output::Dispatch(lift_dispatch(dispatch))),
    ))
}

/// A due result sends the lift of each dispatch.
pub(crate) proof fn lemma_sends_of(state: Proc, response: InOutV)
    ensures
        spec_due_result(state, response).send == sends_of(response.send),
{
    let a = spec_due_result(state, response).send;
    let b = sends_of(response.send);
    assert(a.len() == b.len());
    assert forall|i: int| 0 <= i < a.len() implies a[i] == b[i] by {
        assert(a[i] == (
            APid::Outside,
            AMessage::Output(Output::Dispatch(lift_dispatch(response.send[i]))),
        ));
        assert(b[i] == (
            APid::Outside,
            AMessage::Output(Output::Dispatch(lift_dispatch(response.send[i]))),
        ));
    };
    assert(a =~= b);
}

pub(crate) proof fn lemma_sends_none()
    ensures
        sends_of(Seq::empty()) == note_sends(Seq::empty()),
{
    assert(sends_of(Seq::empty()) =~= note_sends(Seq::empty()));
}

pub(crate) proof fn lemma_sends_execute(id: Seq<char>, version: u64)
    ensures
        sends_of(seq![DispatchV::Execute { id, version }]) == note_sends(seq![NoteV::Execute { id, version }]),
{
    lemma_lift_execute(id, version);
    let a = sends_of(seq![DispatchV::Execute { id, version }]);
    let b = note_sends(seq![NoteV::Execute { id, version }]);
    assert(a.len() == 1);
    assert(b.len() == 1);
    assert(a[0] == b[0]);
    assert(a =~= b);
}

pub(crate) proof fn lemma_sends_unblock(address: Seq<char>, promise: PromiseRecord)
    ensures
        sends_of(seq![DispatchV::Unblock { address, promise }]) == note_sends(
            seq![NoteV::Unblock { address, promise }],
        ),
{
    lemma_lift_unblock(address, promise);
    let a = sends_of(seq![DispatchV::Unblock { address, promise }]);
    let b = note_sends(seq![NoteV::Unblock { address, promise }]);
    assert(a.len() == 1);
    assert(b.len() == 1);
    assert(a[0] == b[0]);
    assert(a =~= b);
}

// ---------------------------------------------------------------------------
// One matched result
// ---------------------------------------------------------------------------

/// `r` is an abstract timeout result that does what the due step did.
pub(crate) open spec fn due_matched(
    config: AbstractConfig,
    key: Seq<char>,
    doc: DocumentBodyV,
    state: Proc,
    now: Time,
    r: AResult,
) -> bool {
    let (next, _, born, notes) = spec_run_due(doc, now, config.retry_timeout);
    &&& spec_run_timeout(config, state, now).contains(r)
    &&& r.send == note_sends(notes)
    &&& r.state.pending == state.pending + items(born)
    &&& doc_rel(key, next, r.state.store)
    &&& super::interpretation::others_kept(key, state.store, r.state.store)
    &&& finite_store(r.state.store)
}

pub(crate) proof fn lemma_matched(
    config: AbstractConfig,
    key: Seq<char>,
    doc: DocumentBodyV,
    state: Proc,
    now: Time,
    r: AResult,
)
    requires
        due_matched(config, key, doc, state, now, r),
    ensures
        due_agrees(config, key, doc, state, now),
{
    let results = spec_run_timeout(config, state, now);
    let j = choose|j: int| 0 <= j < results.len() && results[j] == r;
    assert(results[j] == r);
}

/// An origin document whose due step changed the store within its origin.
pub(crate) proof fn lemma_origin_matched(
    config: AbstractConfig,
    key: Seq<char>,
    o: Seq<char>,
    map: Map<Seq<char>, ObjV>,
    state: Proc,
    now: Time,
    work: InternalV,
    map2: Map<Seq<char>, ObjV>,
    notes: Seq<NoteV>,
)
    requires
        key == spec_origin_key(o),
        map.dom().finite(),
        map2.dom().finite(),
        finite_store(state.store),
        offered(config, state, now, work, spec_run_timeout(config, state, now)),
        ({
            let response = spec_process_work(config, work, state.store, now);
            &&& !response.not_due
            &&& response.work.len() == 0
            &&& response.next.schedules == state.store.schedules
            &&& origin_rel(map2, o, response.next)
            &&& changed_within(state.store, response.next, o)
            &&& finite_store(response.next)
            &&& sends_of(response.send) == note_sends(notes)
        }),
        spec_run_due(DocumentBodyV::Workflow(map), now, config.retry_timeout) == (DocumentBodyV::Workflow(map2), None::<Response>, Seq::<PendingV>::empty(), notes),
    ensures
        due_agrees(config, key, DocumentBodyV::Workflow(map), state, now),
{
    let s = state.store;
    let response = spec_process_work(config, work, s, now);
    let r = spec_due_result(state, response);
    let n = response.next;
    assert(r.state.pending == state.pending + response.work);
    assert(state.pending + response.work =~= state.pending);
    assert(items(Seq::<PendingV>::empty()) =~= Seq::<Sched<InternalV>>::empty());
    assert(state.pending + items(Seq::<PendingV>::empty()) =~= state.pending);
    lemma_sends_of(state, response);
    assert(r.send == sends_of(response.send));
    lemma_origin_reads(key, o, map2, n);
    lemma_others_kept_within(s, n, o);
    assert(due_matched(config, key, DocumentBodyV::Workflow(map), state, now, r));
    lemma_matched(config, key, DocumentBodyV::Workflow(map), state, now, r);
}

/// The store changed at one id of the origin: the next document reads as
/// the next store.
pub(crate) proof fn lemma_one_changed(
    map: Map<Seq<char>, ObjV>,
    o: Seq<char>,
    s: AStore,
    id: Seq<char>,
    obj2: ObjV,
    p2: PromiseV,
    t2: Option<TaskV>,
    n: AStore,
)
    requires
        map.dom().finite(),
        origin_rel(map, o, s),
        finite_store(s),
        origin(id) == o,
        object_rel(obj2, p2, t2),
        callbacks_in(obj2.promise.callbacks, o),
        n.promises == s.promises.insert(id, p2),
        n.tasks == match t2 {
            Some(t) => s.tasks.insert(id, t),
            None => s.tasks.remove(id),
        },
        n.schedules == s.schedules,
    ensures
        map.insert(id, obj2).dom().finite(),
        origin_rel(map.insert(id, obj2), o, n),
        changed_within(s, n, o),
        finite_store(n),
{
    lemma_origin_update(map, o, s, id, obj2, p2, t2, n);
    assert(map.insert(id, obj2).dom() == map.dom().insert(id));
    lemma_within_one(s, n, id);
    assert(n.promises.dom() == s.promises.dom().insert(id));
    match t2 {
        Some(t) => {
            assert(n.tasks.dom() == s.tasks.dom().insert(id));
        },
        None => {
            assert(n.tasks.dom() == s.tasks.dom().remove(id));
        },
    }
}

/// The store changed at two ids of the origin.
pub(crate) proof fn lemma_within_two(s: AStore, n: AStore, id: Seq<char>, y: Seq<char>)
    requires
        origin(y) == origin(id),
        forall|other: Seq<char>|
            other != id && other != y ==> #[trigger] n.promises.contains_key(other) == s.promises.contains_key(other)
                && (s.promises.contains_key(other) ==> n.promises[other] == s.promises[other]),
        forall|other: Seq<char>|
            other != id && other != y ==> #[trigger] n.tasks.contains_key(other) == s.tasks.contains_key(other)
                && (s.tasks.contains_key(other) ==> n.tasks[other] == s.tasks[other]),
    ensures
        changed_within(s, n, origin(id)),
{
    assert forall|other: Seq<char>| #![trigger origin(other)] origin(other) != origin(id) implies {
        &&& s.promises.contains_key(other) == n.promises.contains_key(other)
        &&& (s.promises.contains_key(other) ==> s.promises[other] == n.promises[other])
        &&& s.tasks.contains_key(other) == n.tasks.contains_key(other)
        &&& (s.tasks.contains_key(other) ==> s.tasks[other] == n.tasks[other])
    } by {
        assert(other != id);
        assert(other != y);
    };
}

// ---------------------------------------------------------------------------
// The due branches of an origin document
// ---------------------------------------------------------------------------

/// The context of one due object: the document, its origin, the store, and
/// the object with its abstract promise and task.
pub(crate) open spec fn due_context(
    key: Seq<char>,
    o: Seq<char>,
    map: Map<Seq<char>, ObjV>,
    s: AStore,
    id: Seq<char>,
) -> bool {
    &&& key == spec_origin_key(o)
    &&& map.dom().finite()
    &&& origin_rel(map, o, s)
    &&& finite_store(s)
    &&& map.contains_key(id)
}

/// A pending promise past its timeout: both sides project it.
pub(crate) proof fn lemma_promise_due(
    config: AbstractConfig,
    key: Seq<char>,
    o: Seq<char>,
    map: Map<Seq<char>, ObjV>,
    state: Proc,
    now: Time,
    id: Seq<char>,
)
    requires
        due_context(key, o, map, state.store, id),
        spec_due_id(map, c_sorted(map.dom()), now) == Some(id),
        map[id].promise.state == PromiseState::Pending,
        map[id].promise.timeout_at <= now,
    ensures
        due_agrees(config, key, DocumentBodyV::Workflow(map), state, now),
{
    let s = state.store;
    let obj = map[id];
    let p = s.promises[id];
    let ta = abstract_task(s, id);
    assert(origin(id) == o);
    assert(object_rel(obj, p, ta));
    let work = InternalV::PromiseTimeout(id);
    let results = spec_run_timeout(config, state, now);
    lemma_work_offered(config, state, now, work);
    assert(offered(config, state, now, work, results));
    let q = spec_project_promise(p, now);
    assert(p.state == PromiseState::Pending);
    assert(q.state != PromiseState::Pending);
    let tasks = if s.tasks.contains_key(id) {
        s.tasks.insert(id, spec_project_task(s.tasks[id], q))
    } else {
        s.tasks
    };
    let n = AStore { promises: s.promises.insert(id, q), tasks, ..s };
    let response = spec_process_work(config, work, s, now);
    assert(response == spec_did(n, Seq::empty(), Seq::empty()));
    let obj2 = spec_project_obj(obj, now);
    lemma_project_object(obj, p, ta, now);
    let t2 = match ta {
        Some(task) => Some(spec_project_task(task, q)),
        None => None,
    };
    assert(object_rel(obj2, q, t2));
    assert(obj2.promise.callbacks == obj.promise.callbacks);
    match ta {
        Some(_) => {
            assert(s.tasks.contains_key(id));
        },
        None => {
            assert(!s.tasks.contains_key(id));
            assert(s.tasks.remove(id) =~= s.tasks);
        },
    }
    lemma_one_changed(map, o, s, id, obj2, q, t2, n);
    assert(spec_step_object(map, id, now, config.retry_timeout) == (map.insert(id, obj2), Seq::<NoteV>::empty()));
    lemma_sends_none();
    lemma_origin_matched(config, key, o, map, state, now, work, map.insert(id, obj2), Seq::empty());
}

/// An acquired task whose lease ran out: both sides release it.
pub(crate) proof fn lemma_lease_due(
    config: AbstractConfig,
    key: Seq<char>,
    o: Seq<char>,
    map: Map<Seq<char>, ObjV>,
    state: Proc,
    now: Time,
    id: Seq<char>,
)
    requires
        due_context(key, o, map, state.store, id),
        spec_due_id(map, c_sorted(map.dom()), now) == Some(id),
        map[id].promise.state == PromiseState::Pending,
        map[id].promise.timeout_at > now,
        map[id].task is Some,
        map[id].task.unwrap().state == TaskState::Acquired,
        map[id].task.unwrap().lease_timeout_at is Some,
        map[id].task.unwrap().lease_timeout_at.unwrap() <= now,
    ensures
        due_agrees(config, key, DocumentBodyV::Workflow(map), state, now),
{
    let s = state.store;
    let obj = map[id];
    let t = obj.task.unwrap();
    let p = s.promises[id];
    let ta = abstract_task(s, id);
    assert(origin(id) == o);
    assert(object_rel(obj, p, ta));
    assert(ta is Some);
    let t_a = ta.unwrap();
    assert(task_rel(t, t_a));
    assert(s.tasks.contains_key(id));
    assert(t_a == s.tasks[id]);
    let work = InternalV::TaskLeaseTimeout(id);
    let results = spec_run_timeout(config, state, now);
    lemma_work_offered(config, state, now, work);
    assert(offered(config, state, now, work, results));
    assert(spec_project_promise(p, now).state == PromiseState::Pending);
    assert(t_a.state == TaskState::Acquired);
    assert(t.ttl is Some);
    let at = t.lease_timeout_at.unwrap();
    assert(sat_add(t_a.acquired_at, t.ttl.unwrap()) == at);
    assert(spec_lease_at(t_a) == at);
    let u = a_unlease(t_a, TaskState::Pending, Some(now));
    let n = AStore { tasks: s.tasks.insert(id, u), ..s };
    let response = spec_process_work(config, work, s, now);
    assert(response == spec_lease(s, id, now));
    assert(response == spec_did(n, Seq::empty(), Seq::empty()));
    let t2 = c_unlease(t, TaskState::Pending, Some(now));
    let obj2 = ObjV { task: Some(t2), ..obj };
    assert(task_rel(t2, u));
    assert(object_rel(obj2, p, Some(u)));
    lemma_promises_kept(s, id);
    lemma_one_changed(map, o, s, id, obj2, p, Some(u), n);
    assert(spec_step_object(map, id, now, config.retry_timeout) == (map.insert(id, obj2), Seq::<NoteV>::empty()));
    lemma_sends_none();
    lemma_origin_matched(config, key, o, map, state, now, work, map.insert(id, obj2), Seq::empty());
}

/// A pending task whose offer is due: both sides offer it again and tell
/// the outside to execute it.
pub(crate) proof fn lemma_retry_due(
    config: AbstractConfig,
    key: Seq<char>,
    o: Seq<char>,
    map: Map<Seq<char>, ObjV>,
    state: Proc,
    now: Time,
    id: Seq<char>,
)
    requires
        due_context(key, o, map, state.store, id),
        spec_due_id(map, c_sorted(map.dom()), now) == Some(id),
        map[id].promise.state == PromiseState::Pending,
        map[id].promise.timeout_at > now,
        map[id].task is Some,
        map[id].task.unwrap().state == TaskState::Pending,
        map[id].task.unwrap().retry_timeout_at is Some,
        map[id].task.unwrap().retry_timeout_at.unwrap() <= now,
    ensures
        due_agrees(config, key, DocumentBodyV::Workflow(map), state, now),
{
    let s = state.store;
    let obj = map[id];
    let t = obj.task.unwrap();
    let p = s.promises[id];
    let ta = abstract_task(s, id);
    assert(origin(id) == o);
    assert(object_rel(obj, p, ta));
    assert(ta is Some);
    let t_a = ta.unwrap();
    assert(task_rel(t, t_a));
    assert(s.tasks.contains_key(id));
    assert(t_a == s.tasks[id]);
    assert(t_a.retry_timeout_at == t.retry_timeout_at);
    let work = InternalV::TaskRetryTimeout(id);
    let results = spec_run_timeout(config, state, now);
    lemma_work_offered(config, state, now, work);
    assert(offered(config, state, now, work, results));
    assert(spec_project_promise(p, now).state == PromiseState::Pending);
    lemma_sat_add(now, config.retry_timeout);
    let again = sat_add(now, config.retry_timeout);
    assert(again == spec_sat_add(now, config.retry_timeout));
    let u = TaskV { retry_timeout_at: Some(again), ..t_a };
    let n = AStore { tasks: s.tasks.insert(id, u), ..s };
    let response = spec_process_work(config, work, s, now);
    assert(response == spec_retry(config, s, id, now));
    assert(response == spec_did(n, Seq::empty(), seq![DispatchV::Execute { id, version: t_a.version }]));
    let t2 = TkV { retry_timeout_at: Some(spec_sat_add(now, config.retry_timeout)), ..t };
    let obj2 = ObjV { task: Some(t2), ..obj };
    assert(task_rel(t2, u));
    assert(object_rel(obj2, p, Some(u)));
    lemma_promises_kept(s, id);
    lemma_one_changed(map, o, s, id, obj2, p, Some(u), n);
    let notes = seq![NoteV::Execute { id, version: t.version }];
    assert(spec_step_object(map, id, now, config.retry_timeout) == (map.insert(id, obj2), notes));
    assert(t.version == t_a.version);
    lemma_sends_execute(id, t.version);
    lemma_origin_matched(config, key, o, map, state, now, work, map.insert(id, obj2), notes);
}

/// A settled promise with a callback: both sides drop the callback and
/// resume the awaiter.
pub(crate) proof fn lemma_callback_due(
    config: AbstractConfig,
    key: Seq<char>,
    o: Seq<char>,
    map: Map<Seq<char>, ObjV>,
    state: Proc,
    now: Time,
    id: Seq<char>,
)
    requires
        due_context(key, o, map, state.store, id),
        spec_due_id(map, c_sorted(map.dom()), now) == Some(id),
        map[id].promise.state != PromiseState::Pending,
        map[id].promise.callbacks.len() > 0,
    ensures
        due_agrees(config, key, DocumentBodyV::Workflow(map), state, now),
{
    let s = state.store;
    let obj = map[id];
    let p = s.promises[id];
    let ta = abstract_task(s, id);
    assert(origin(id) == o);
    assert(object_rel(obj, p, ta));
    assert(promise_rel(obj.promise, p));
    let callbacks = obj.promise.callbacks;
    let awaiter = callbacks[0];
    assert(callbacks.contains(awaiter));
    lemma_contains_to_set(callbacks, awaiter);
    assert(p.callbacks.contains(awaiter));
    assert(origin(awaiter) == o);
    let since = match obj.promise.settled_at {
        Some(at) => at,
        None => 0,
    };
    let work = InternalV::Callback { awaited: id, awaiter };
    let results = spec_run_timeout(config, state, now);
    lemma_work_offered(config, state, now, work);
    assert(offered(config, state, now, work, results));
    // The awaited side.
    assert(spec_project_promise(p, now) == p);
    let q = PromiseV { callbacks: p.callbacks.remove(awaiter), ..p };
    let response = spec_process_work(config, work, s, now);
    assert(response == spec_callback(s, id, awaiter, now));
    assert(response == spec_callback_apply(s, id, awaiter, q, since, now));
    let tasks0 = if s.tasks.contains_key(id) {
        s.tasks.insert(id, spec_project_task(s.tasks[id], q))
    } else {
        s.tasks
    };
    assert(tasks0 == s.tasks) by {
        if s.tasks.contains_key(id) {
            assert(ta is Some);
            assert(obj.task is Some);
            assert(obj.task.unwrap().state == TaskState::Fulfilled);
            assert(s.tasks[id].state == TaskState::Fulfilled);
            assert(spec_project_task(s.tasks[id], q) == s.tasks[id]);
            assert(s.tasks.insert(id, s.tasks[id]) =~= s.tasks);
        }
    };
    lemma_skip_no_duplicates(callbacks);
    let obj1 = ObjV { promise: PromV { callbacks: callbacks.skip(1), ..obj.promise }, ..obj };
    assert(promise_rel(obj1.promise, q));
    assert(object_rel(obj1, q, ta));
    assert forall|k: int| 0 <= k < callbacks.skip(1).len() implies origin(#[trigger] callbacks.skip(1)[k]) == o by {
        assert(callbacks.skip(1)[k] == callbacks[k + 1]);
    };
    assert(callbacks_in(obj1.promise.callbacks, o));
    let map1 = map.insert(id, obj1);
    let n1 = AStore { promises: s.promises.insert(id, q), tasks: s.tasks, ..s };
    lemma_tasks_kept(s, id);
    lemma_one_changed(map, o, s, id, obj1, q, ta, n1);
    let map2 = spec_resume(map1, awaiter, id, since, now);
    assert(spec_step_object(map, id, now, config.retry_timeout) == (map2, Seq::<NoteV>::empty()));
    lemma_sends_none();
    // The awaiter side.
    let n = AStore { promises: s.promises.insert(id, q), tasks: response.next.tasks, ..s };
    assert(response.next == n);
    assert(response.send.len() == 0);
    assert(response.work.len() == 0);
    if !map.contains_key(awaiter) {
        assert(!s.tasks.contains_key(awaiter));
        assert(n.tasks == tasks0);
        assert(awaiter != id);
        assert(!map1.contains_key(awaiter));
        assert(map2 == map1);
        lemma_origin_matched(config, key, o, map, state, now, work, map1, Seq::empty());
    } else if awaiter == id {
        let proj = spec_project_obj(obj1, now);
        assert(proj.promise.state != PromiseState::Pending);
        match proj.task {
            None => {
                assert(map2 == map1);
            },
            Some(tp) => {
                assert(tp.state == TaskState::Fulfilled);
                assert(map2 == map1);
            },
        }
        if s.tasks.contains_key(id) {
            assert(s.tasks[id].state == TaskState::Fulfilled);
            let stored = s.tasks[id];
            let t = spec_project_task(stored, spec_project_promise(p, now));
            assert(t.state == TaskState::Fulfilled);
            assert(n.tasks == tasks0);
        } else {
            assert(n.tasks == tasks0);
        }
        lemma_origin_matched(config, key, o, map, state, now, work, map1, Seq::empty());
    } else {
        let objw = map[awaiter];
        let pw = s.promises[awaiter];
        let taw = abstract_task(s, awaiter);
        assert(object_rel(objw, pw, taw));
        assert(map1[awaiter] == objw);
        assert(s.promises.contains_key(awaiter));
        let proj = spec_project_obj(objw, now);
        let pwq = spec_project_promise(pw, now);
        lemma_project_object(objw, pw, taw, now);
        match proj.task {
            None => {
                assert(taw is None);
                assert(!s.tasks.contains_key(awaiter));
                assert(n.tasks == tasks0);
                assert(map2 == map1);
                lemma_origin_matched(config, key, o, map, state, now, work, map1, Seq::empty());
            },
            Some(tp) => {
                assert(taw is Some);
                assert(s.tasks.contains_key(awaiter));
                let tw = taw.unwrap();
                let t = spec_project_task(tw, pwq);
                assert(task_rel(tp, t));
                assert(callbacks_in(objw.promise.callbacks, o));
                match tp.state {
                    TaskState::Suspended => {
                        assert(objw.promise.state == PromiseState::Pending);
                        let u = TaskV {
                            state: TaskState::Pending,
                            resumes: seq![id],
                            retry_timeout_at: Some(now),
                            ..t
                        };
                        assert(n.tasks == tasks0.insert(awaiter, u));
                        let tc = TkV {
                            state: TaskState::Pending,
                            pid: None,
                            ttl: None,
                            lease_timeout_at: None,
                            retry_timeout_at: Some(now),
                            resumes: seq![id],
                            ..tp
                        };
                        let objw2 = ObjV { task: Some(tc), ..objw };
                        assert(map2 == map1.insert(awaiter, objw2));
                        assert(tp.pid is None);
                        assert(tp.ttl is None);
                        assert(task_rel(tc, u));
                        assert(object_rel(objw2, pw, Some(u)));
                        assert(n.promises == n1.promises.insert(awaiter, pw)) by {
                            assert(n1.promises[awaiter] == pw);
                            assert(n1.promises.insert(awaiter, pw) =~= n1.promises);
                        };
                        assert(n.tasks == n1.tasks.insert(awaiter, u));
                        lemma_origin_update(map1, o, n1, awaiter, objw2, pw, Some(u), n);
                        assert(map2.dom() == map1.dom().insert(awaiter));
                        lemma_within_two(s, n, id, awaiter);
                        assert(n.tasks.dom() == s.tasks.dom().insert(awaiter));
                        assert(finite_store(n));
                        lemma_origin_matched(config, key, o, map, state, now, work, map2, Seq::empty());
                    },
                    TaskState::Fulfilled => {
                        assert(n.tasks == tasks0);
                        assert(map2 == map1);
                        lemma_origin_matched(config, key, o, map, state, now, work, map1, Seq::empty());
                    },
                    _ => {
                        assert(objw.promise.state == PromiseState::Pending);
                        if tp.resumes.contains(id) {
                            assert(t.resumes.contains(id));
                            assert(n.tasks == tasks0);
                            assert(map2 == map1);
                            lemma_origin_matched(config, key, o, map, state, now, work, map1, Seq::empty());
                        } else {
                            assert(!t.resumes.contains(id));
                            let u = TaskV { resumes: t.resumes.push(id), ..t };
                            assert(n.tasks == tasks0.insert(awaiter, u));
                            let tc = TkV { resumes: tp.resumes.push(id), ..tp };
                            let objw2 = ObjV { task: Some(tc), ..objw };
                            assert(map2 == map1.insert(awaiter, objw2));
                            assert(task_rel(tc, u));
                            assert(object_rel(objw2, pw, Some(u)));
                            assert(n.promises == n1.promises.insert(awaiter, pw)) by {
                                assert(n1.promises[awaiter] == pw);
                                assert(n1.promises.insert(awaiter, pw) =~= n1.promises);
                            };
                            assert(n.tasks == n1.tasks.insert(awaiter, u));
                            lemma_origin_update(map1, o, n1, awaiter, objw2, pw, Some(u), n);
                            assert(map2.dom() == map1.dom().insert(awaiter));
                            lemma_within_two(s, n, id, awaiter);
                            assert(n.tasks.dom() == s.tasks.dom().insert(awaiter));
                            assert(finite_store(n));
                            lemma_origin_matched(config, key, o, map, state, now, work, map2, Seq::empty());
                        }
                    },
                }
            },
        }
    }
}

/// A settled promise with a listener: both sides drop the listener and tell
/// the address.
pub(crate) proof fn lemma_listener_due(
    config: AbstractConfig,
    key: Seq<char>,
    o: Seq<char>,
    map: Map<Seq<char>, ObjV>,
    state: Proc,
    now: Time,
    id: Seq<char>,
)
    requires
        due_context(key, o, map, state.store, id),
        spec_due_id(map, c_sorted(map.dom()), now) == Some(id),
        map[id].promise.state != PromiseState::Pending,
        map[id].promise.callbacks.len() == 0,
        map[id].promise.listeners.len() > 0,
    ensures
        due_agrees(config, key, DocumentBodyV::Workflow(map), state, now),
{
    let s = state.store;
    let obj = map[id];
    let p = s.promises[id];
    let ta = abstract_task(s, id);
    assert(origin(id) == o);
    assert(object_rel(obj, p, ta));
    assert(promise_rel(obj.promise, p));
    let listeners = obj.promise.listeners;
    let address = listeners[0];
    assert(listeners.contains(address));
    lemma_contains_to_set(listeners, address);
    assert(p.listeners.contains(address));
    let work = InternalV::Listener { awaited: id, address };
    let results = spec_run_timeout(config, state, now);
    lemma_work_offered(config, state, now, work);
    assert(offered(config, state, now, work, results));
    assert(spec_project_promise(p, now) == p);
    lemma_string_view(id);
    assert(c_string(id) == a_string(id));
    lemma_record(c_string(id), obj.promise, p);
    let rec = spec_promise_record(a_string(id), p);
    assert(rec == spec_record(c_string(id), obj.promise));
    let q = PromiseV { listeners: p.listeners.remove(address), ..p };
    let tasks = if s.tasks.contains_key(id) {
        s.tasks.insert(id, spec_project_task(s.tasks[id], q))
    } else {
        s.tasks
    };
    assert(tasks == s.tasks) by {
        if s.tasks.contains_key(id) {
            assert(ta is Some);
            assert(obj.task is Some);
            assert(obj.task.unwrap().state == TaskState::Fulfilled);
            assert(s.tasks[id].state == TaskState::Fulfilled);
            assert(spec_project_task(s.tasks[id], q) == s.tasks[id]);
            assert(s.tasks.insert(id, s.tasks[id]) =~= s.tasks);
        }
    };
    let n = AStore { promises: s.promises.insert(id, q), tasks, ..s };
    let response = spec_process_work(config, work, s, now);
    assert(response == spec_listener(s, id, address, now));
    assert(response == spec_did(n, Seq::empty(), seq![DispatchV::Unblock { address, promise: rec }]));
    lemma_skip_no_duplicates(listeners);
    let obj2 = ObjV { promise: PromV { listeners: listeners.skip(1), ..obj.promise }, ..obj };
    assert(promise_rel(obj2.promise, q));
    assert(object_rel(obj2, q, ta));
    assert(callbacks_in(obj2.promise.callbacks, o));
    lemma_tasks_kept(s, id);
    lemma_one_changed(map, o, s, id, obj2, q, ta, n);
    let notes = seq![NoteV::Unblock { address, promise: rec }];
    assert(spec_step_object(map, id, now, config.retry_timeout) == (map.insert(id, obj2), notes));
    lemma_sends_unblock(address, rec);
    lemma_origin_matched(config, key, o, map, state, now, work, map.insert(id, obj2), notes);
}

/// The due step of an origin document.
pub(crate) proof fn lemma_origin_due(
    config: AbstractConfig,
    key: Seq<char>,
    o: Seq<char>,
    map: Map<Seq<char>, ObjV>,
    state: Proc,
    now: Time,
)
    requires
        key == spec_origin_key(o),
        map.dom().finite(),
        origin_rel(map, o, state.store),
        finite_store(state.store),
    ensures
        due_agrees(config, key, DocumentBodyV::Workflow(map), state, now),
{
    let doc = DocumentBodyV::Workflow(map);
    let keys = c_sorted(map.dom());
    lemma_sorted(map.dom());
    assert forall|i: int| 0 <= i < keys.len() implies map.contains_key(#[trigger] keys[i]) by {
        assert(map.dom().contains(keys[i]));
    };
    lemma_due_id(map, keys, now);
    match spec_due_id(map, keys, now) {
        None => {
            assert(spec_run_due(doc, now, config.retry_timeout) == (doc, None::<Response>, Seq::<PendingV>::empty(), Seq::<NoteV>::empty()));
        },
        Some(id) => {
            assert(map.contains_key(id));
            assert(due_context(key, o, map, state.store, id));
            let obj = map[id];
            let (map2, notes) = spec_step_object(map, id, now, config.retry_timeout);
            assert(spec_run_due(doc, now, config.retry_timeout) == (DocumentBodyV::Workflow(map2), None::<Response>, Seq::<PendingV>::empty(), notes));
            if obj.promise.state == PromiseState::Pending && obj.promise.timeout_at <= now {
                lemma_promise_due(config, key, o, map, state, now, id);
            } else if obj.promise.state == PromiseState::Pending {
                match obj.task {
                    Some(t) if t.state == TaskState::Acquired && match t.lease_timeout_at {
                        Some(at) => at <= now,
                        None => false,
                    } => {
                        lemma_lease_due(config, key, o, map, state, now, id);
                    },
                    Some(t) if t.state == TaskState::Pending && match t.retry_timeout_at {
                        Some(at) => at <= now,
                        None => false,
                    } => {
                        lemma_retry_due(config, key, o, map, state, now, id);
                    },
                    _ => {
                        assert(map2 == map);
                        assert(notes.len() == 0);
                    },
                }
            } else if obj.promise.callbacks.len() > 0 {
                lemma_callback_due(config, key, o, map, state, now, id);
            } else if obj.promise.listeners.len() > 0 {
                lemma_listener_due(config, key, o, map, state, now, id);
            } else {
                assert(map2 == map);
                assert(notes.len() == 0);
            }
        },
    }
}

// ---------------------------------------------------------------------------
// The due step of a schedule
// ---------------------------------------------------------------------------

/// A schedule whose run is due: both sides advance it and queue the
/// occurrence.
pub(crate) proof fn lemma_schedule_due(
    config: AbstractConfig,
    key: Seq<char>,
    id: Seq<char>,
    sch: Schedule,
    state: Proc,
    now: Time,
)
    requires
        key == spec_schedule_key(id),
        slot_rel(Some(sch), id, state.store),
        finite_store(state.store),
        sch.next_run_at <= now,
    ensures
        due_agrees(config, key, DocumentBodyV::Schedule(Some(sch)), state, now),
{
    let s = state.store;
    let doc = DocumentBodyV::Schedule(Some(sch));
    assert(s.schedules.contains_key(id));
    let c = s.schedules[id];
    assert(schedule_rel(sch, c));
    assert(sch.id@ == id);
    let at = sch.next_run_at;
    assert(c.next_run_at == at);
    let work = schedule_work(s, id);
    let results = spec_run_timeout(config, state, now);
    lemma_work_offered(config, state, now, work);
    assert(offered(config, state, now, work, results));
    let response = spec_process_work(config, work, s, now);
    assert(response == spec_schedule_step(s, id, now));
    let d = ScheduleV { last_run_at: Some(at), next_run_at: spec_next_cron(c.cron, at), ..c };
    let occ = Sched::Timer(
        at,
        InternalV::Occurrence {
            promise: spec_expand(c.promise_id, id, at),
            at,
            timeout: c.promise_timeout,
            param: c.promise_param,
            tags: c.promise_tags,
        },
    );
    let n = AStore { schedules: s.schedules.insert(id, d), ..s };
    assert(response == spec_did(n, seq![occ], Seq::empty()));
    let r = spec_due_result(state, response);
    let (next, _, born, notes) = spec_run_due(doc, now, config.retry_timeout);
    let pending = PendingV {
        promise: spec_expand(sch.promise_id@, sch.id@, at),
        at,
        timeout: sch.promise_timeout,
        param: sch.promise_param,
        tags: sch.promise_tags,
    };
    let sch2 = Schedule { last_run_at: Some(at), next_run_at: spec_next_cron(sch.cron@, at), ..sch };
    assert(next == DocumentBodyV::Schedule(Some(sch2)));
    assert(born == seq![pending]);
    assert(notes.len() == 0);
    lemma_sends_none();
    lemma_sends_of(state, response);
    assert(r.send == sends_of(Seq::empty()));
    assert(r.send == note_sends(notes)) by {
        assert(notes =~= Seq::<NoteV>::empty());
    };
    assert(as_item(pending) == occ);
    assert(items(born) =~= seq![occ]);
    assert(r.state.pending == state.pending + items(born));
    assert(schedule_rel(sch2, d));
    assert(slot_rel(Some(sch2), id, n));
    lemma_schedule_key(id);
    assert(doc_rel(key, next, n));
    lemma_others_kept_schedule(s, n, id);
    assert(n.schedules.dom() == s.schedules.dom().insert(id));
    assert(finite_store(n));
    assert(due_matched(config, key, doc, state, now, r));
    lemma_matched(config, key, doc, state, now, r);
}

// ---------------------------------------------------------------------------
// Every due step
// ---------------------------------------------------------------------------

pub(crate) proof fn lemma_due_agrees(config: AbstractConfig, key: Seq<char>, doc: DocumentBodyV, state: Proc, now: Time)
    requires
        doc_rel(key, doc, state.store),
        finite_store(state.store),
    ensures
        due_agrees(config, key, doc, state, now),
{
    let s = state.store;
    if spec_starts(key, schedule_prefix()) {
        let id = key.skip(2);
        lemma_starts_split(key, schedule_prefix());
        assert(key == spec_schedule_key(id));
        match doc {
            DocumentBodyV::Schedule(Some(sch)) => {
                if sch.next_run_at <= now {
                    lemma_schedule_due(config, key, id, sch, state, now);
                } else {
                    assert(spec_run_due(doc, now, config.retry_timeout) == (doc, None::<Response>, Seq::<PendingV>::empty(), Seq::<NoteV>::empty()));
                }
            },
            _ => {
                assert(spec_run_due(doc, now, config.retry_timeout) == (doc, None::<Response>, Seq::<PendingV>::empty(), Seq::<NoteV>::empty()));
            },
        }
    } else if spec_starts(key, origin_prefix()) {
        let o = key.skip(2);
        lemma_starts_split(key, origin_prefix());
        assert(key == spec_origin_key(o));
        match doc {
            DocumentBodyV::Workflow(map) => {
                lemma_origin_due(config, key, o, map, state, now);
            },
            _ => {},
        }
    } else {
        match doc {
            DocumentBodyV::Workflow(map) => {
                lemma_sorted(map.dom());
                assert(c_sorted(map.dom()).len() == 0);
                assert(spec_due_id(map, c_sorted(map.dom()), now) is None);
                assert(spec_run_due(doc, now, config.retry_timeout) == (doc, None::<Response>, Seq::<PendingV>::empty(), Seq::<NoteV>::empty()));
            },
            DocumentBodyV::Schedule(_) => {
                assert(spec_run_due(doc, now, config.retry_timeout) == (doc, None::<Response>, Seq::<PendingV>::empty(), Seq::<NoteV>::empty()));
            },
        }
    }
}

pub(crate) proof fn lemma_dues_agree(config: AbstractConfig)
    ensures
        dues_agree(config),
{
    assert forall|key: Seq<char>, doc: DocumentBodyV, state: Proc, now: u64|
        doc_rel(key, doc, state.store) && finite_store(state.store) implies #[trigger] due_agrees(
        config,
        key,
        doc,
        state,
        now,
    ) by {
        lemma_due_agrees(config, key, doc, state, now);
    };
}

// ---------------------------------------------------------------------------
// The occurrence
// ---------------------------------------------------------------------------

/// Lean's `createPromiseAt`: the object born of an occurrence relates to the
/// abstract object born of it.
pub(crate) proof fn lemma_born(pending: PendingV, now: Time)
    requires
        now >= pending.at,
    ensures
        ({
            let timeout_at = spec_sat_add(pending.at, pending.timeout);
            let runnable = spec_targeted(pending.tags) && !spec_timer(pending.tags);
            let born = spec_new_obj(timeout_at, now, pending.param, pending.tags, runnable);
            let promise = if timeout_at > pending.at {
                PromV { created_at: pending.at, ..born.promise }
            } else {
                born.promise
            };
            let task = match born.task {
                Some(t) if t.state == TaskState::Pending => Some(TkV {
                    retry_timeout_at: Some(now),
                    ..t
                }),
                other => other,
            };
            let (p, t) = spec_new_object(
                sat_add(pending.at, pending.timeout),
                pending.at,
                now,
                pending.param,
                pending.tags,
                spec_has_target(pending.tags) && !spec_is_timer(pending.tags),
            );
            &&& object_rel(ObjV { promise, task }, p, t)
            &&& promise.callbacks.len() == 0
        }),
{
    let at = pending.at;
    let tags = pending.tags;
    lemma_sat_add(at, pending.timeout);
    lemma_targeted(tags);
    lemma_timer(tags);
    lemma_offer(tags, at);
    lemma_empty_to_set();
    let timeout_at = spec_sat_add(at, pending.timeout);
    let runnable = spec_targeted(tags) && !spec_timer(tags);
    let born = spec_new_obj(timeout_at, now, pending.param, tags, runnable);
    let promise = if timeout_at > at {
        PromV { created_at: at, ..born.promise }
    } else {
        born.promise
    };
    let task = match born.task {
        Some(t) if t.state == TaskState::Pending => Some(TkV {
            retry_timeout_at: Some(now),
            ..t
        }),
        other => other,
    };
    let (p, t) = spec_new_object(timeout_at, at, now, pending.param, tags, runnable);
    let live_now = timeout_at > now;
    assert(promise.state == p.state);
    assert(promise.created_at == p.created_at);
    assert(promise.settled_at == p.settled_at);
    assert(promise_rel(promise, p));
    match (task, t) {
        (Some(ct), Some(at_)) => {
            assert(task_rel(ct, at_));
        },
        (None, None) => {},
        _ => {
            assert(false);
        },
    }
    assert(object_rel(ObjV { promise, task }, p, t));
}

pub(crate) proof fn lemma_occurrence_agrees(pending: PendingV, doc: DocumentBodyV, s: AStore, now: Time)
    requires
        doc_rel(spec_origin_key(origin(pending.promise)), doc, s),
        finite_store(s),
    ensures
        occurrence_agrees(pending, doc, s, now),
{
    let x = pending.promise;
    let o = origin(x);
    let key = spec_origin_key(o);
    lemma_origin_doc(key, o, doc, s);
    let map = spec_workflow_map(doc);
    assert(doc == DocumentBodyV::Workflow(map));
    assert(spec_opened(doc) == doc);
    let next = spec_occurrence(doc, pending, now);
    if map.contains_key(x) || now < pending.at {
        assert(next == doc);
    } else {
        assert(!s.promises.contains_key(x));
        assert(!s.tasks.contains_key(x));
        lemma_born(pending, now);
        let timeout_at = spec_sat_add(pending.at, pending.timeout);
        let runnable = spec_targeted(pending.tags) && !spec_timer(pending.tags);
        let born = spec_new_obj(timeout_at, now, pending.param, pending.tags, runnable);
        let promise = if timeout_at > pending.at {
            PromV { created_at: pending.at, ..born.promise }
        } else {
            born.promise
        };
        let task = match born.task {
            Some(t) if t.state == TaskState::Pending => Some(TkV {
                retry_timeout_at: Some(now),
                ..t
            }),
            other => other,
        };
        let obj = ObjV { promise, task };
        assert(next == DocumentBodyV::Workflow(map.insert(x, obj)));
        let (p, t) = spec_new_object(
            sat_add(pending.at, pending.timeout),
            pending.at,
            now,
            pending.param,
            pending.tags,
            spec_has_target(pending.tags) && !spec_is_timer(pending.tags),
        );
        assert(object_rel(obj, p, t));
        assert(callbacks_in(obj.promise.callbacks, o));
        let out = spec_create_if_absent(
            s,
            x,
            pending.at,
            pending.timeout,
            pending.param,
            pending.tags,
            now,
        );
        let tasks = match t {
            Some(task) => s.tasks.insert(x, task),
            None => s.tasks,
        };
        let n = AStore { promises: s.promises.insert(x, p), tasks, ..s };
        assert(out == spec_did(n, Seq::empty(), Seq::empty()));
        match t {
            Some(_) => {},
            None => {
                assert(s.tasks.remove(x) =~= s.tasks);
            },
        }
        lemma_one_changed(map, o, s, x, obj, p, t, n);
        lemma_origin_reads(key, o, map.insert(x, obj), n);
        lemma_others_kept_within(s, n, o);
    }
}

pub(crate) proof fn lemma_occurrences_agree()
    ensures
        occurrences_agree(),
{
    assert forall|pending: PendingV, doc: DocumentBodyV, s: AStore, now: u64|
        doc_rel(spec_origin_key(origin(pending.promise)), doc, s) && finite_store(s) implies #[trigger] occurrence_agrees(
        pending,
        doc,
        s,
        now,
    ) by {
        lemma_occurrence_agrees(pending, doc, s, now);
    };
}

// ---------------------------------------------------------------------------
// Agreement
// ---------------------------------------------------------------------------

/// Lean's `refinement_handlers`: at every configuration, every handler,
/// the due step, and the occurrence agree.
pub(crate) proof fn lemma_agreement(config: AbstractConfig)
    ensures
        agreement(config),
{
    super::requests::lemma_requests_agree(config);
    lemma_dues_agree(config);
    lemma_occurrences_agree();
}

} // verus!

}

mod simulation {
//! Forward simulation from the Echod concrete model to the Echod abstract model.
//!
//! The relation is `relation::related`. An injected `Request` is one abstract
//! input of that request; `Stop`, and an outside step whose message is not an
//! output, are empty abstract executions; an observed output is one abstract
//! outside step of that output. A store step is an empty abstract execution.
//! A node step that begins a flight is one abstract step, taken at the time
//! the flight's handler runs with: a served request, or one timeout result.
//! A node step that answers a request without a flight is one abstract shed, or
//! one served empty heartbeat. Every other node step is an empty abstract
//! execution: a read, a write, and the reply when the write lands change
//! nothing the relation reads.
//!
//! [`lemma_simulation`] is the simulation under [`agreement`]: the
//! handlers, the due step, and the occurrence do the same on a document and
//! on the abstract store it reads as. `requests` and `work` prove that
//! agreement at the configuration the node implements, and
//! [`prove_refinement`] establishes trace inclusion there, with nothing assumed. Cargo
//! erases these bodies; a Verus run is what checks them.

use vstd::prelude::*;
use echod_types::{MAX_TIME, MAX_VERSION};
#[cfg(verus_keep_ghost)]
use echod_types::spec_deadline_bounded;

#[cfg(verus_keep_ghost)]
use super::interpretation::{doc_rel, finite_store, lemma_others_same, others_kept, request_agrees};
#[cfg(verus_keep_ghost)]
use echod_concrete_spec::{Config as ConcreteConfig, Proc as CProc, Spec as CModel};
#[cfg(verus_keep_ghost)]
use echod_concrete_spec::rover::{
    EntryV, Message as CMessage, NodeV, Pid as CPid, spec_bytes, spec_get,
    spec_initial_node as initial_node,
    spec_node as spec_node_step, spec_nodes, spec_notes, spec_notify, spec_one, spec_reply,
    spec_store, spec_string, spec_world, StoreV as CStore,
};
#[cfg(verus_keep_ghost)]
use echod_concrete_spec::state::{
    axiom_decode_encode_body, CachedV, DocumentBodyV, FlightV, JobV, NoteV, PendingV, spec_begin, spec_cached,
    spec_cached_from, spec_commit, spec_decide, spec_earliest_from, spec_earliest_key,
    spec_empty_body, spec_encode_body, spec_flight, spec_forget, spec_handle, spec_body_is_empty, spec_keep,
    spec_key, spec_occurrence, spec_owns, spec_pure, spec_read, spec_remember, spec_request,
    spec_run_due, spec_store_reply, spec_timeout, spec_unavailable,
};
#[cfg(verus_keep_ghost)]
use echod_concrete_spec::state::{
    Etag, spec_apply, spec_etag, spec_etag_chars, spec_find, spec_put, StoreReq, StoreRes,
};
#[cfg(verus_keep_ghost)]
use super::relation::*;
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::state::{
    spec_handler,
};
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::state::{
    spec_body, spec_create_if_absent, spec_process_work,
};
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::rover::{
    empty_store, lemma_empty_heartbeat_is_first, lemma_shed_is_last, remove_at, spec_idle,
    spec_internal_result, spec_queue, spec_ready, spec_request_outcome, spec_run, spec_run_timeout,
    spec_send, spec_service, spec_shed,
};
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::rover::Pid as APid;
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::protocol::Message as AMessage;
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::axioms::axiom_string_ext;
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::state::{InOutV, InternalV, OutV, StoreV as AStore};
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::{
    BoundaryEvent, Call, Config as AbstractConfig, Output, Proc as AProc, Spec as AModel,
};
#[cfg(verus_keep_ghost)]
use rover_spec::rover::RoverSpec::refinement::{
    concrete_refines_abstract, end, matches, project, refines, simulation,
};
#[cfg(verus_keep_ghost)]
use rover_spec::rover::RoverSpec::{
    before, envelopes, event_valid, Execution, inject, is_process, Label, land, legal,
    observe_outside, Proc as _, Spec, State, StepResultV,
};
#[cfg(verus_keep_ghost)]
use rover_spec::rover::comm::{Envelope, ProcessEvent};
#[cfg(verus_keep_ghost)]
use rover_spec::rover::comm::{Sched, Time};
#[cfg(verus_keep_ghost)]
use echod_types::{origin, Response};
#[cfg(verus_keep_ghost)]
use vstd::multiset::Multiset;

verus! {

broadcast use
    vstd::seq::group_seq_lemmas,
    vstd::seq_lib::group_to_multiset_ensures,
    vstd::multiset::group_multiset_axioms;

/// The Echod concrete model: the nodes and the store.
pub(crate) open spec fn concrete_model() -> CModel {
    CModel
}

/// The Echod abstract model: the one service.
pub(crate) open spec fn abstract_model() -> AModel {
    AModel
}

/// `related`, packaged as the function the generic theorem takes.
pub(crate) open spec fn link(fleet: ConcreteConfig) -> spec_fn(State<CModel>, State<AModel>) -> bool {
    |concrete: State<CModel>, abstract_world: State<AModel>| related(fleet, concrete, abstract_world)
}

pub(crate) proof fn lemma_link(fleet: ConcreteConfig, concrete: State<CModel>, abstract_world: State<AModel>)
    ensures
        link(fleet)(concrete, abstract_world) == related(fleet, concrete, abstract_world),
{
    assert(link(fleet)(concrete, abstract_world) == related(fleet, concrete, abstract_world));
}

/// `later` still contains every envelope of `earlier`, in front.
pub(crate) open spec fn extends<P, M>(later: Seq<Envelope<P, M>>, earlier: Seq<Envelope<P, M>>) -> bool {
    earlier.len() <= later.len() && forall|j: int|
        #![trigger later[j]]
        0 <= j < earlier.len() ==> later[j] == earlier[j]
}

/// The document a node holds under `key`: its cache, or the empty document.
/// `relation::loaded` is this.
pub(crate) open spec fn held(node: NodeV, key: Seq<char>) -> DocumentBodyV {
    match spec_cached(node, key) {
        Some(cached) => spec_read(key, cached.body),
        None => spec_empty_body(key),
    }
}

/// Two nodes with the same work: documents, flight, pending list, and op
/// counter. They differ at most in the process shell, `logic`, `wake`,
/// `next_request`, which the relation does not read.
pub(crate) open spec fn same_work(a: NodeV, b: NodeV) -> bool {
    a == (NodeV { logic: a.logic, wake: a.wake, next_request: a.next_request, ..b })
}

/// The flight a begin decides with, before it has an op. `decision` reads
/// only the job and the time, so every flight of this begin decides alike.
pub(crate) open spec fn probe(key: Seq<char>, now: Time, caller: Option<(Seq<char>, u64)>, job: JobV) -> FlightV {
    spec_flight(0, key, None, now, caller, job)
}

pub(crate) open spec fn reply_send(reply: Option<(Seq<char>, u64, Response)>) -> Seq<(CPid, CMessage)> {
    match reply {
        Some((client, id, response)) => seq![spec_reply(client, id, response)],
        None => Seq::empty(),
    }
}

/// The writing flight `spec_decide` opens from `flight` on `doc`.
pub(crate) open spec fn written(node: NodeV, flight: FlightV, doc: DocumentBodyV) -> FlightV {
    let (next, reply, born, notes) = decision(flight, doc, node.retry_timeout);
    FlightV {
        op: node.next_op,
        writing: true,
        born,
        reply: flight_reply(flight, reply),
        notify: notes,
        decided: Some(spec_encode_body(next)),
        ..flight
    }
}

pub(crate) open spec fn node_result(node: NodeV, send: Seq<(CPid, CMessage)>) -> StepResultV<CProc, CPid, CMessage> {
    StepResultV { state: CProc::Node(node), send }
}

pub(crate) open spec fn store_result(store: CStore, send: Seq<(CPid, CMessage)>) -> StepResultV<CProc, CPid, CMessage> {
    StepResultV { state: CProc::Store(store), send }
}

pub(crate) open spec fn node_pid(i: int) -> CPid {
    CPid::Node(i as u64)
}

pub(crate) open spec fn no_store_traffic(env: Envelope<CPid, CMessage>) -> bool {
    !(env.message is StoreReq) && !(env.message is StoreRes)
}

pub(crate) open spec fn process_label(label: Label<CPid, CMessage>) -> bool {
    match label {
        Label::Process { .. } => true,
        _ => false,
    }
}

pub(crate) open spec fn sent(sender: CPid, entry: (CPid, CMessage)) -> Envelope<CPid, CMessage> {
    Envelope { sender, recipient: entry.0, message: entry.1 }
}

/// `request` is still a client request on `network`. The network only grows.
pub(crate) open spec fn request_carried(network: Seq<Envelope<CPid, CMessage>>, request: Call) -> bool {
    exists|i: int|
        #![trigger network[i]]
        0 <= i < network.len() && network[i].sender == CPid::Outside && network[i].message
            == CMessage::Request(request)
}

pub(crate) open spec fn empty_heartbeat(request: Call) -> bool {
    match request.request {
        echod_types::Request::TaskHeartbeat(q) => q.tasks@.len() == 0,
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Network arithmetic
// ---------------------------------------------------------------------------

pub(crate) proof fn lemma_inject_keeps_process<M: Spec>(
    world: State<M>,
    outside: M::Pid,
    recipient: M::Pid,
    at: Time,
    message: M::Message,
)
    ensures
        inject(world, outside, recipient, at, message).process == world.process,
{
    let after = inject(world, outside, recipient, at, message);
    assert(after.process == world.process);
}

pub(crate) proof fn lemma_observe_keeps_world<M: Spec>(world: State<M>, at: Time)
    ensures
        observe_outside(world, at).process == world.process,
        observe_outside(world, at).network == world.network,
        observe_outside(world, at).now == at,
{
    let after = observe_outside(world, at);
    assert(after.process == world.process);
    assert(after.network == world.network);
    assert(after.now == at);
}

pub(crate) proof fn lemma_push_eq_add<A>(s: Seq<A>, x: A)
    ensures
        s.push(x) == s.add(Seq::<A>::empty().push(x)),
{
    let suffix = Seq::<A>::empty().push(x);
    assert(suffix.len() == 1);
    assert forall|i: int| 0 <= i < s.push(x).len() implies s.push(x)[i] == s.add(suffix)[i] by {
        if i < s.len() {
        } else {
            assert(i == s.len());
            assert(suffix[0] == x);
            assert(s.add(suffix)[i] == x);
        }
    };
    assert(s.push(x) =~= s.add(suffix));
}

pub(crate) proof fn lemma_extends_refl<P, M>(network: Seq<Envelope<P, M>>)
    ensures
        extends(network, network),
{
}

pub(crate) proof fn lemma_extends_push<P, M>(earlier: Seq<Envelope<P, M>>, added: Envelope<P, M>)
    ensures
        extends(earlier.push(added), earlier),
{
}

pub(crate) proof fn lemma_extends_add<P, M>(earlier: Seq<Envelope<P, M>>, suffix: Seq<Envelope<P, M>>)
    ensures
        extends(earlier + suffix, earlier),
{
}

pub(crate) proof fn lemma_service_output_monotone(
    earlier: Seq<Envelope<APid, AMessage>>,
    later: Seq<Envelope<APid, AMessage>>,
    output: Output,
)
    requires
        service_output(earlier, output),
        extends(later, earlier),
    ensures
        service_output(later, output),
{
    let j = choose|j: int|
        #![trigger earlier[j]]
        0 <= j < earlier.len() && earlier[j] == Envelope {
            sender: APid::Service,
            recipient: APid::Outside,
            message: AMessage::Output(output),
        };
    assert(later[j] == earlier[j]);
}

pub(crate) proof fn lemma_request_monotone(
    env: Envelope<CPid, CMessage>,
    earlier: Seq<Envelope<APid, AMessage>>,
    later: Seq<Envelope<APid, AMessage>>,
)
    requires
        carried_request(env, earlier),
        extends(later, earlier),
    ensures
        carried_request(env, later),
{
    match env.message {
        CMessage::Request(request) => {
            if env.sender == CPid::Outside {
                let j = choose|j: int|
                    #![trigger earlier[j]]
                    0 <= j < earlier.len() && earlier[j] == Envelope {
                        sender: APid::Outside,
                        recipient: APid::Service,
                        message: AMessage::Request(request),
                    };
                assert(later[j] == earlier[j]);
                assert(service_request(later, request));
            }
        },
        _ => {},
    }
}

pub(crate) proof fn lemma_output_monotone(
    env: Envelope<CPid, CMessage>,
    earlier: Seq<Envelope<APid, AMessage>>,
    later: Seq<Envelope<APid, AMessage>>,
)
    requires
        carried_output(env, earlier),
        extends(later, earlier),
    ensures
        carried_output(env, later),
{
    match env.message {
        CMessage::Output(output) => {
            if env.recipient == CPid::Outside {
                lemma_service_output_monotone(earlier, later, output);
            }
        },
        _ => {},
    }
}

pub(crate) proof fn lemma_append_keeps_coverage(
    before: Seq<Envelope<CPid, CMessage>>,
    suffix: Seq<Envelope<CPid, CMessage>>,
    earlier: Seq<Envelope<APid, AMessage>>,
    later: Seq<Envelope<APid, AMessage>>,
)
    requires
        requests_covered(before, earlier),
        outputs_covered(before, earlier),
        extends(later, earlier),
        forall|k: int|
            #![trigger suffix[k]]
            0 <= k < suffix.len() ==> carried_request(suffix[k], later) && carried_output(
                suffix[k],
                later,
            ),
    ensures
        requests_covered(before.add(suffix), later),
        outputs_covered(before.add(suffix), later),
{
    let combined = before.add(suffix);
    assert forall|i: int| 0 <= i < combined.len() implies carried_request(
        #[trigger] combined[i],
        later,
    ) && carried_output(combined[i], later) by {
        if i < before.len() {
            assert(combined[i] == before[i]);
            lemma_request_monotone(before[i], earlier, later);
            lemma_output_monotone(before[i], earlier, later);
        } else {
            let k = i - before.len();
            assert(combined[i] == suffix[k]);
        }
    };
}

pub(crate) proof fn lemma_push_keeps_coverage(
    before: Seq<Envelope<CPid, CMessage>>,
    added: Envelope<CPid, CMessage>,
    earlier: Seq<Envelope<APid, AMessage>>,
    later: Seq<Envelope<APid, AMessage>>,
)
    requires
        requests_covered(before, earlier),
        outputs_covered(before, earlier),
        extends(later, earlier),
        carried_request(added, later),
        carried_output(added, later),
    ensures
        requests_covered(before.push(added), later),
        outputs_covered(before.push(added), later),
{
    let suffix = Seq::<Envelope<CPid, CMessage>>::empty().push(added);
    lemma_push_eq_add(before, added);
    assert forall|k: int| 0 <= k < suffix.len() implies carried_request(
        #[trigger] suffix[k],
        later,
    ) && carried_output(suffix[k], later) by {
        assert(suffix[0] == added);
    };
    lemma_append_keeps_coverage(before, suffix, earlier, later);
}

pub(crate) proof fn lemma_pushed_request(network: Seq<Envelope<APid, AMessage>>, request: Call)
    ensures
        service_request(
            network.push(Envelope {
                sender: APid::Outside,
                recipient: APid::Service,
                message: AMessage::Request(request),
            }),
            request,
        ),
{
    let added = Envelope {
        sender: APid::Outside,
        recipient: APid::Service,
        message: AMessage::Request(request),
    };
    let later = network.push(added);
    let j = network.len() as int;
    assert(later[j] == added);
}

pub(crate) proof fn lemma_envelope_at<P, M>(sender: P, send: Seq<(P, M)>, k: int)
    requires
        0 <= k < send.len(),
    ensures
        envelopes(sender, send).len() == send.len(),
        envelopes(sender, send)[k] == (Envelope { sender, recipient: send[k].0, message: send[k].1 }),
{
}

/// The outputs of one abstract send are on the network it lands on.
pub(crate) proof fn lemma_sent_outputs(
    network: Seq<Envelope<APid, AMessage>>,
    send: Seq<(APid, AMessage)>,
    k: int,
)
    requires
        0 <= k < send.len(),
        send[k].0 == APid::Outside,
        send[k].1 is Output,
    ensures
        service_output(network + envelopes(APid::Service, send), send[k].1->Output_0),
{
    let later = network + envelopes(APid::Service, send);
    let j = network.len() + k;
    lemma_envelope_at(APid::Service, send, k);
    assert(later[j] == envelopes(APid::Service, send)[k]);
}

// ---------------------------------------------------------------------------
// One abstract step, and the empty execution
// ---------------------------------------------------------------------------

pub(crate) proof fn lemma_empty_matches(config: AbstractConfig, before: State<AModel>)
    ensures
        matches(abstract_model(), config, before, Seq::<BoundaryEvent>::empty(), before),
{
    let execution = Seq::<(Label<APid, AMessage>, State<AModel>)>::empty();
    assert forall|i: int| 0 <= i < execution.len() implies #[trigger]
        rover_spec::rover::spec::before::<AModel>(before, execution, i).step(
        abstract_model(),
        config,
        execution[i].0,
        execution[i].1,
    ) by {
        assert(false);
    };
    assert(legal(abstract_model(), config, before, execution));
    assert(project::<AModel>(abstract_model(), execution) =~= Seq::<BoundaryEvent>::empty());
    assert(end::<AModel>(before, execution) == before);
}

pub(crate) proof fn lemma_matched_step(
    config: AbstractConfig,
    before: State<AModel>,
    label: Label<APid, AMessage>,
    after: State<AModel>,
    visible: Seq<BoundaryEvent>,
)
    requires
        before.step(abstract_model(), config, label, after),
        abstract_model().observe(label) == visible,
    ensures
        matches(abstract_model(), config, before, visible, after),
{
    let pair = (label, after);
    let execution = Seq::<(Label<APid, AMessage>, State<AModel>)>::empty().push(pair);
    assert(execution.len() == 1);
    assert(execution[0] == pair);
    assert(execution.last() == pair);
    assert(execution.drop_last() =~= Seq::<(Label<APid, AMessage>, State<AModel>)>::empty());
    assert(project::<AModel>(abstract_model(), execution.drop_last()) =~= Seq::<BoundaryEvent>::empty());
    let empty = Seq::<BoundaryEvent>::empty();
    assert(empty.add(visible) =~= visible);
    assert(project::<AModel>(abstract_model(), execution) =~= visible);
    assert forall|i: int| 0 <= i < execution.len() implies #[trigger]
        rover_spec::rover::spec::before::<AModel>(before, execution, i).step(
        abstract_model(),
        config,
        execution[i].0,
        execution[i].1,
    ) by {
        assert(i == 0);
        assert(rover_spec::rover::spec::before::<AModel>(before, execution, 0) == before);
    };
    assert(legal(abstract_model(), config, before, execution));
    assert(end::<AModel>(before, execution) == after);
}

pub(crate) proof fn lemma_matches_same_visible(
    config: AbstractConfig,
    before: State<AModel>,
    visible: Seq<BoundaryEvent>,
    same: Seq<BoundaryEvent>,
    after: State<AModel>,
)
    requires
        matches(abstract_model(), config, before, visible, after),
        visible == same,
    ensures
        matches(abstract_model(), config, before, same, after),
{
    let execution = choose|execution: Execution<AModel>|
        #![trigger legal(abstract_model(), config, before, execution)]
        legal(abstract_model(), config, before, execution) && project::<AModel>(abstract_model(), execution)
            == visible && end::<AModel>(before, execution) == after;
    assert(project::<AModel>(abstract_model(), execution) == same);
}

/// A process step with the response at `j`, stated over the model's trait: the
/// witness `step` asks for is in the form `step` names it.
pub(crate) proof fn lemma_process_step<M: Spec>(
    m: M,
    config: M::Config,
    world: State<M>,
    i: int,
    at: Time,
    event: ProcessEvent<M::Pid, M::Message>,
    j: int,
)
    requires
        world.now <= at,
        0 <= i < world.process.len(),
        is_process(m, world, world.process[i].0),
        event_valid(world, world.process[i].0, event),
        0 <= j < world.process[i].1.on_event(config, at, event).len(),
    ensures
        ({
            let process = world.process[i].0;
            let response = world.process[i].1.on_event(config, at, event)[j];
            world.step(
                m,
                config,
                Label::Process { process, at, event, send: response.send },
                land(world, i, process, at, response),
            )
        }),
{
    rover_spec::rover::spec::process_step(m, config, world, i, at, event, j);
}

/// One abstract process step of the service, with the response at `index`.
/// The world it lands in: the one slot holds the response's state, the
/// network grew by the response's sends, the clock is `at`.
pub(crate) proof fn lemma_service_step(
    config: AbstractConfig,
    before_a: State<AModel>,
    at: Time,
    event: ProcessEvent<APid, AMessage>,
    index: int,
) -> (after_a: State<AModel>)
    requires
        single(before_a),
        before_a.now <= at,
        event_valid(before_a, APid::Service, event),
        0 <= index < astate(before_a).on_event(config, at, event).len(),
    ensures
        ({
            let response = astate(before_a).on_event(config, at, event)[index];
            &&& after_a == land(before_a, 0, APid::Service, at, response)
            &&& single(after_a)
            &&& astate(after_a) == response.state
            &&& after_a.network == before_a.network + envelopes(APid::Service, response.send)
            &&& after_a.now == at
            &&& extends(after_a.network, before_a.network)
            &&& matches(abstract_model(), config, before_a, Seq::<BoundaryEvent>::empty(), after_a)
        }),
{
    reveal(State::step);
    let outcomes = astate(before_a).on_event(config, at, event);
    let response = outcomes[index];
    lemma_single_present(before_a);
    let label = Label::Process { process: APid::Service, at, event, send: response.send };
    let after_a = land(before_a, 0, APid::Service, at, response);
    assert(before_a.process[0].1 == astate(before_a));
    lemma_process_step(abstract_model(), config, before_a, 0, at, event, index);
    assert(before_a.step(abstract_model(), config, label, after_a));
    assert(abstract_model().observe(label) =~= Seq::<BoundaryEvent>::empty());
    lemma_matched_step(config, before_a, label, after_a, Seq::<BoundaryEvent>::empty());
    assert(after_a.process.len() == 1);
    assert(after_a.process[0] == (APid::Service, response.state));
    lemma_extends_add(before_a.network, envelopes(APid::Service, response.send));
    after_a
}

// ---------------------------------------------------------------------------
// Finding by key
// ---------------------------------------------------------------------------

/// `spec_find` from `j` finds the first entry at or after `j` with the key.
pub(crate) proof fn lemma_find_from(entries: Seq<echod_concrete_spec::rover::EntryV>, key: Seq<char>, j: int)
    requires
        0 <= j <= entries.len(),
    ensures
        match spec_find(entries, key, j) {
            Some(i) => j <= i < entries.len() && entries[i].key == key && forall|k: int|
                j <= k < i ==> #[trigger] entries[k].key != key,
            None => forall|k: int| j <= k < entries.len() ==> #[trigger] entries[k].key != key,
        },
    decreases entries.len() - j,
{
    if j >= entries.len() {
    } else if entries[j].key == key {
    } else {
        lemma_find_from(entries, key, j + 1);
    }
}

/// The characterisation of a hit, in both directions.
pub(crate) proof fn lemma_find_is(entries: Seq<echod_concrete_spec::rover::EntryV>, key: Seq<char>, i: int)
    requires
        0 <= i < entries.len(),
        entries[i].key == key,
        forall|k: int| 0 <= k < i ==> #[trigger] entries[k].key != key,
    ensures
        spec_find(entries, key, 0) == Some(i),
{
    lemma_find_from(entries, key, 0);
    match spec_find(entries, key, 0) {
        Some(found) => {
            if found < i {
                assert(entries[found].key != key);
            } else if found > i {
                assert(entries[i].key != key);
            }
        },
        None => {
            assert(entries[i].key != key);
        },
    }
}

pub(crate) proof fn lemma_find_absent(entries: Seq<echod_concrete_spec::rover::EntryV>, key: Seq<char>)
    requires
        forall|k: int| 0 <= k < entries.len() ==> #[trigger] entries[k].key != key,
    ensures
        spec_find(entries, key, 0) == None::<int>,
{
    lemma_find_from(entries, key, 0);
    match spec_find(entries, key, 0) {
        Some(found) => {
            assert(entries[found].key != key);
        },
        None => {},
    }
}

/// `spec_cached_from` has the same shape.
pub(crate) proof fn lemma_cached_from(docs: Seq<CachedV>, key: Seq<char>, j: int)
    requires
        0 <= j <= docs.len(),
    ensures
        match spec_cached_from(docs, key, j) {
            Some(cached) => exists|i: int|
                j <= i < docs.len() && #[trigger] docs[i] == cached && cached.key == key,
            None => forall|k: int| j <= k < docs.len() ==> #[trigger] docs[k].key != key,
        },
    decreases docs.len() - j,
{
    if j >= docs.len() {
    } else if docs[j].key == key {
        assert(docs[j] == docs[j]);
    } else {
        lemma_cached_from(docs, key, j + 1);
    }
}

/// With distinct keys, a hit is the one entry with the key.
pub(crate) proof fn lemma_cached_is(docs: Seq<CachedV>, key: Seq<char>, i: int)
    requires
        0 <= i < docs.len(),
        docs[i].key == key,
        forall|j: int, k: int| 0 <= j < k < docs.len() ==> #[trigger] docs[j].key != #[trigger] docs[k].key,
    ensures
        spec_cached_from(docs, key, 0) == Some(docs[i]),
{
    lemma_cached_from(docs, key, 0);
    match spec_cached_from(docs, key, 0) {
        Some(cached) => {
            let found = choose|found: int|
                0 <= found < docs.len() && #[trigger] docs[found] == cached && cached.key == key;
            if found != i {
                if found < i {
                    assert(docs[found].key != docs[i].key);
                } else {
                    assert(docs[i].key != docs[found].key);
                }
            }
        },
        None => {
            assert(docs[i].key != key);
        },
    }
}

pub(crate) proof fn lemma_cached_absent(docs: Seq<CachedV>, key: Seq<char>)
    requires
        forall|k: int| 0 <= k < docs.len() ==> #[trigger] docs[k].key != key,
    ensures
        spec_cached_from(docs, key, 0) == None::<CachedV>,
{
    lemma_cached_from(docs, key, 0);
    match spec_cached_from(docs, key, 0) {
        Some(cached) => {
            let found = choose|found: int|
                0 <= found < docs.len() && #[trigger] docs[found] == cached && cached.key == key;
            assert(docs[found].key != key);
        },
        None => {},
    }
}

/// A key the node does not own is not cached.
pub(crate) proof fn lemma_unowned_uncached(node: NodeV, key: Seq<char>)
    requires
        cache_owned(node),
        !spec_owns(node, key),
    ensures
        spec_cached(node, key) is None,
{
    assert forall|k: int| 0 <= k < node.documents.len() implies #[trigger] node.documents[k].key
        != key by {
        assert(spec_owns(node, node.documents[k].key));
    };
    lemma_cached_absent(node.documents, key);
}

/// Remembering `key` changes the cache under `key` and nothing else, and
/// keeps the keys distinct.
pub(crate) proof fn lemma_remember(
    docs: Seq<CachedV>,
    key: Seq<char>,
    body: Seq<u8>,
    etag: Option<Seq<char>>,
    i: int,
)
    requires
        0 <= i <= docs.len(),
        forall|k: int| 0 <= k < i ==> #[trigger] docs[k].key != key,
        forall|j: int, k: int| 0 <= j < k < docs.len() ==> #[trigger] docs[j].key != #[trigger] docs[k].key,
    ensures
        ({
            let next = spec_remember(docs, key, body, etag, i);
            &&& forall|j: int, k: int| 0 <= j < k < next.len() ==> #[trigger] next[j].key != #[trigger] next[k].key
            &&& spec_cached_from(next, key, 0) == Some(CachedV { key, body, etag })
            &&& forall|other: Seq<char>| other != key ==> #[trigger] spec_cached_from(next, other, 0)
                == spec_cached_from(docs, other, 0)
            &&& forall|k: int| 0 <= k < next.len() ==> #[trigger] next[k].key == key || exists|m: int|
                0 <= m < docs.len() && #[trigger] docs[m] == next[k]
        }),
    decreases docs.len() - i,
{
    let entry = CachedV { key, body, etag };
    let next = spec_remember(docs, key, body, etag, i);
    if i >= docs.len() {
        assert(next == docs.push(entry));
        assert forall|j: int, k: int| 0 <= j < k < next.len() implies #[trigger] next[j].key
            != #[trigger] next[k].key by {
            if k == docs.len() {
                assert(next[j] == docs[j]);
                assert(docs[j].key != key);
            }
        };
        assert forall|k: int| 0 <= k < docs.len() implies #[trigger] next[k].key != key by {
            assert(next[k] == docs[k]);
        };
        lemma_cached_is(next, key, docs.len() as int);
        assert forall|other: Seq<char>| other != key implies #[trigger] spec_cached_from(next, other, 0)
            == spec_cached_from(docs, other, 0) by {
            lemma_cached_from(docs, other, 0);
            match spec_cached_from(docs, other, 0) {
                Some(cached) => {
                    let m = choose|m: int|
                        0 <= m < docs.len() && #[trigger] docs[m] == cached && cached.key == other;
                    assert(next[m] == docs[m]);
                    lemma_cached_is(next, other, m);
                },
                None => {
                    assert forall|k: int| 0 <= k < next.len() implies #[trigger] next[k].key != other by {
                        if k < docs.len() {
                            assert(next[k] == docs[k]);
                        }
                    };
                    lemma_cached_absent(next, other);
                },
            }
        };
        assert forall|k: int| 0 <= k < next.len() implies #[trigger] next[k].key == key || exists|m: int|
            0 <= m < docs.len() && #[trigger] docs[m] == next[k] by {
            if k < docs.len() {
                assert(docs[k] == next[k]);
            }
        };
    } else if docs[i].key == key {
        assert(next == docs.update(i, entry));
        assert forall|j: int, k: int| 0 <= j < k < next.len() implies #[trigger] next[j].key
            != #[trigger] next[k].key by {
            assert(next[j].key == docs[j].key);
            assert(next[k].key == docs[k].key);
        };
        lemma_cached_is(next, key, i);
        assert forall|other: Seq<char>| other != key implies #[trigger] spec_cached_from(next, other, 0)
            == spec_cached_from(docs, other, 0) by {
            lemma_cached_from(docs, other, 0);
            match spec_cached_from(docs, other, 0) {
                Some(cached) => {
                    let m = choose|m: int|
                        0 <= m < docs.len() && #[trigger] docs[m] == cached && cached.key == other;
                    assert(m != i);
                    assert(next[m] == docs[m]);
                    lemma_cached_is(next, other, m);
                },
                None => {
                    assert forall|k: int| 0 <= k < next.len() implies #[trigger] next[k].key != other by {
                        assert(next[k].key == docs[k].key);
                    };
                    lemma_cached_absent(next, other);
                },
            }
        };
        assert forall|k: int| 0 <= k < next.len() implies #[trigger] next[k].key == key || exists|m: int|
            0 <= m < docs.len() && #[trigger] docs[m] == next[k] by {
            if k != i {
                assert(docs[k] == next[k]);
            }
        };
    } else {
        lemma_remember(docs, key, body, etag, i + 1);
    }
}

/// Forgetting `key` empties the cache under `key` and changes nothing else.
pub(crate) proof fn lemma_forget(docs: Seq<CachedV>, key: Seq<char>, i: int)
    requires
        0 <= i <= docs.len(),
        forall|k: int| 0 <= k < i ==> #[trigger] docs[k].key != key,
        forall|j: int, k: int| 0 <= j < k < docs.len() ==> #[trigger] docs[j].key != #[trigger] docs[k].key,
    ensures
        ({
            let next = spec_forget(docs, key, i);
            &&& forall|j: int, k: int| 0 <= j < k < next.len() ==> #[trigger] next[j].key != #[trigger] next[k].key
            &&& spec_cached_from(next, key, 0) is None
            &&& forall|other: Seq<char>| other != key ==> #[trigger] spec_cached_from(next, other, 0)
                == spec_cached_from(docs, other, 0)
            &&& forall|k: int| 0 <= k < next.len() ==> exists|m: int|
                0 <= m < docs.len() && #[trigger] docs[m] == #[trigger] next[k]
        }),
    decreases docs.len() - i,
{
    let next = spec_forget(docs, key, i);
    if i >= docs.len() {
        assert(next == docs);
        lemma_cached_absent(docs, key);
        assert forall|k: int| 0 <= k < next.len() implies exists|m: int|
            0 <= m < docs.len() && #[trigger] docs[m] == #[trigger] next[k] by {
            assert(docs[k] == next[k]);
        };
    } else if docs[i].key == key {
        assert(next == docs.take(i) + docs.skip(i + 1));
        assert(next.len() == docs.len() - 1);
        assert forall|k: int| 0 <= k < next.len() implies #[trigger] next[k] == (if k < i {
            docs[k]
        } else {
            docs[k + 1]
        }) by {
            if k < i {
                assert(next[k] == docs.take(i)[k]);
            } else {
                assert(next[k] == docs.skip(i + 1)[k - i]);
            }
        };
        assert forall|j: int, k: int| 0 <= j < k < next.len() implies #[trigger] next[j].key
            != #[trigger] next[k].key by {
        };
        assert forall|k: int| 0 <= k < next.len() implies #[trigger] next[k].key != key by {
            if k < i {
            } else {
                assert(docs[i].key != docs[k + 1].key);
            }
        };
        lemma_cached_absent(next, key);
        assert forall|other: Seq<char>| other != key implies #[trigger] spec_cached_from(next, other, 0)
            == spec_cached_from(docs, other, 0) by {
            lemma_cached_from(docs, other, 0);
            match spec_cached_from(docs, other, 0) {
                Some(cached) => {
                    let m = choose|m: int|
                        0 <= m < docs.len() && #[trigger] docs[m] == cached && cached.key == other;
                    assert(m != i);
                    if m < i {
                        assert(next[m] == docs[m]);
                        lemma_cached_is(next, other, m);
                    } else {
                        assert(next[m - 1] == docs[m]);
                        lemma_cached_is(next, other, m - 1);
                    }
                },
                None => {
                    lemma_cached_absent(next, other);
                },
            }
        };
        assert forall|k: int| 0 <= k < next.len() implies exists|m: int|
            0 <= m < docs.len() && #[trigger] docs[m] == #[trigger] next[k] by {
            if k < i {
                assert(docs[k] == next[k]);
            } else {
                assert(docs[k + 1] == next[k]);
            }
        };
    } else {
        lemma_forget(docs, key, i + 1);
    }
}

/// `spec_keep` under `key`: the kept document reads as `doc`, or is gone when
/// `doc` is empty and there is no etag. Other keys are untouched.
pub(crate) proof fn lemma_keep(
    docs: Seq<CachedV>,
    key: Seq<char>,
    doc: DocumentBodyV,
    etag: Option<Seq<char>>,
)
    requires
        forall|j: int, k: int| 0 <= j < k < docs.len() ==> #[trigger] docs[j].key != #[trigger] docs[k].key,
    ensures
        ({
            let next = spec_keep(docs, key, doc, etag);
            &&& forall|j: int, k: int| 0 <= j < k < next.len() ==> #[trigger] next[j].key != #[trigger] next[k].key
            &&& (spec_body_is_empty(doc) && etag is None ==> spec_cached_from(next, key, 0) is None)
            &&& (!(spec_body_is_empty(doc) && etag is None) ==> spec_cached_from(next, key, 0) == Some(
                CachedV { key, body: spec_encode_body(doc), etag },
            ))
            &&& forall|other: Seq<char>| other != key ==> #[trigger] spec_cached_from(next, other, 0)
                == spec_cached_from(docs, other, 0)
            &&& forall|k: int| 0 <= k < next.len() ==> #[trigger] next[k].key == key || exists|m: int|
                0 <= m < docs.len() && #[trigger] docs[m] == next[k]
        }),
{
    if spec_body_is_empty(doc) && etag is None {
        lemma_forget(docs, key, 0);
        let next = spec_forget(docs, key, 0);
        assert forall|k: int| 0 <= k < next.len() implies #[trigger] next[k].key == key || exists|m: int|
            0 <= m < docs.len() && #[trigger] docs[m] == next[k] by {
            let m = choose|m: int| 0 <= m < docs.len() && #[trigger] docs[m] == next[k];
            assert(docs[m] == next[k]);
        };
    } else {
        lemma_remember(docs, key, spec_encode_body(doc), etag, 0);
    }
}

// ---------------------------------------------------------------------------
// The store's entries
// ---------------------------------------------------------------------------

/// Inserting an absent key: the new key is found with its body, other keys
/// read as before, and keys stay distinct.
pub(crate) proof fn lemma_insert_at(
    entries: Seq<echod_concrete_spec::rover::EntryV>,
    entry: echod_concrete_spec::rover::EntryV,
    i: int,
)
    requires
        0 <= i <= entries.len(),
        forall|k: int| 0 <= k < entries.len() ==> #[trigger] entries[k].key != entry.key,
        forall|j: int, k: int|
            0 <= j < k < entries.len() ==> #[trigger] entries[j].key != #[trigger] entries[k].key,
    ensures
        ({
            let next = echod_concrete_spec::state::spec_insert_at(entries, entry, i);
            &&& forall|j: int, k: int| 0 <= j < k < next.len() ==> #[trigger] next[j].key != #[trigger] next[k].key
            &&& physical(echod_concrete_spec::rover::StoreV { entries: next, appendable: false, seen: Seq::empty() }, entry.key)
                == Some(entry.body)
            &&& forall|other: Seq<char>| other != entry.key ==> #[trigger] physical(
                echod_concrete_spec::rover::StoreV { entries: next, appendable: false, seen: Seq::empty() },
                other,
            ) == physical(
                echod_concrete_spec::rover::StoreV { entries, appendable: false, seen: Seq::empty() },
                other,
            )
        }),
    decreases entries.len() - i,
{
    let next = echod_concrete_spec::state::spec_insert_at(entries, entry, i);
    let after = echod_concrete_spec::rover::StoreV { entries: next, appendable: false, seen: Seq::empty() };
    let before_store = echod_concrete_spec::rover::StoreV { entries, appendable: false, seen: Seq::empty() };
    if i >= entries.len() {
        assert(next == entries.push(entry));
        assert forall|j: int, k: int| 0 <= j < k < next.len() implies #[trigger] next[j].key
            != #[trigger] next[k].key by {
            if k == entries.len() {
                assert(next[j] == entries[j]);
            }
        };
        assert forall|k: int| 0 <= k < entries.len() implies #[trigger] next[k].key != entry.key by {
            assert(next[k] == entries[k]);
        };
        lemma_find_is(next, entry.key, entries.len() as int);
        assert forall|other: Seq<char>| other != entry.key implies #[trigger] physical(after, other)
            == physical(before_store, other) by {
            lemma_find_from(entries, other, 0);
            match spec_find(entries, other, 0) {
                Some(m) => {
                    assert(next[m] == entries[m]);
                    assert forall|k: int| 0 <= k < m implies #[trigger] next[k].key != other by {
                        assert(next[k] == entries[k]);
                    };
                    lemma_find_is(next, other, m);
                },
                None => {
                    assert forall|k: int| 0 <= k < next.len() implies #[trigger] next[k].key != other by {
                        if k < entries.len() {
                            assert(next[k] == entries[k]);
                        }
                    };
                    lemma_find_absent(next, other);
                },
            }
        };
    } else if echod_concrete_spec::state::spec_before(entry.key, entries[i].key) {
        assert(next == entries.take(i).push(entry) + entries.skip(i));
        assert(next.len() == entries.len() + 1);
        assert forall|k: int| 0 <= k < next.len() implies #[trigger] next[k] == (if k < i {
            entries[k]
        } else if k == i {
            entry
        } else {
            entries[k - 1]
        }) by {
            if k < i {
                assert(next[k] == entries.take(i).push(entry)[k]);
            } else if k == i {
                assert(next[k] == entries.take(i).push(entry)[k]);
            } else {
                assert(next[k] == entries.skip(i)[k - i - 1]);
            }
        };
        assert forall|j: int, k: int| 0 <= j < k < next.len() implies #[trigger] next[j].key
            != #[trigger] next[k].key by {
        };
        assert forall|k: int| 0 <= k < i implies #[trigger] next[k].key != entry.key by {
        };
        lemma_find_is(next, entry.key, i);
        assert forall|other: Seq<char>| other != entry.key implies #[trigger] physical(after, other)
            == physical(before_store, other) by {
            lemma_find_from(entries, other, 0);
            match spec_find(entries, other, 0) {
                Some(m) => {
                    if m < i {
                        assert forall|k: int| 0 <= k < m implies #[trigger] next[k].key != other by {
                        };
                        lemma_find_is(next, other, m);
                    } else {
                        assert(next[m + 1] == entries[m]);
                        assert forall|k: int| 0 <= k < m + 1 implies #[trigger] next[k].key != other by {
                        };
                        lemma_find_is(next, other, m + 1);
                    }
                },
                None => {
                    assert forall|k: int| 0 <= k < next.len() implies #[trigger] next[k].key != other by {
                    };
                    lemma_find_absent(next, other);
                },
            }
        };
    } else {
        lemma_insert_at(entries, entry, i + 1);
    }
}

/// `spec_put`: the key reads as the new body, other keys as before, and keys
/// stay distinct.
pub(crate) proof fn lemma_put(
    store: echod_concrete_spec::rover::StoreV,
    entry: echod_concrete_spec::rover::EntryV,
)
    requires
        entries_distinct(store),
    ensures
        ({
            let next = echod_concrete_spec::rover::StoreV {
                entries: echod_concrete_spec::state::spec_put(store.entries, entry),
                ..store
            };
            &&& entries_distinct(next)
            &&& physical(next, entry.key) == Some(entry.body)
            &&& forall|other: Seq<char>| other != entry.key ==> #[trigger] physical(next, other)
                == physical(store, other)
        }),
{
    let entries = store.entries;
    let next_entries = echod_concrete_spec::state::spec_put(entries, entry);
    let next = echod_concrete_spec::rover::StoreV { entries: next_entries, ..store };
    lemma_find_from(entries, entry.key, 0);
    match spec_find(entries, entry.key, 0) {
        Some(i) => {
            assert(next_entries == entries.update(i, entry));
            assert forall|k: int| 0 <= k < next_entries.len() implies #[trigger] next_entries[k].key
                == entries[k].key by {
            };
            lemma_find_is(next_entries, entry.key, i);
            assert forall|other: Seq<char>| other != entry.key implies #[trigger] physical(next, other)
                == physical(store, other) by {
                lemma_find_from(entries, other, 0);
                match spec_find(entries, other, 0) {
                    Some(m) => {
                        assert(m != i);
                        assert(next_entries[m] == entries[m]);
                        lemma_find_is(next_entries, other, m);
                    },
                    None => {
                        lemma_find_absent(next_entries, other);
                    },
                }
            };
        },
        None => {
            lemma_insert_at(entries, entry, 0);
            let bare_next = echod_concrete_spec::rover::StoreV {
                entries: next_entries,
                appendable: false,
                seen: Seq::empty(),
            };
            let bare = echod_concrete_spec::rover::StoreV { entries, appendable: false, seen: Seq::empty() };
            assert(physical(bare_next, entry.key) == physical(next, entry.key));
            assert forall|other: Seq<char>| other != entry.key implies #[trigger] physical(next, other)
                == physical(store, other) by {
                assert(physical(bare_next, other) == physical(next, other));
                assert(physical(bare, other) == physical(store, other));
            };
        },
    }
}

// ---------------------------------------------------------------------------
// Occurrences owed
// ---------------------------------------------------------------------------

pub(crate) open spec fn owed_by(node: NodeV, item: Sched<InternalV>) -> nat {
    items(occurrences(node)).to_multiset().count(item)
}

/// `owed` from `k` is the sum over the nodes from `k`; replacing one node's
/// state moves the sum by that node's difference.
pub(crate) proof fn lemma_owed_update(
    fleet: ConcreteConfig,
    before_w: State<CModel>,
    after_w: State<CModel>,
    i: int,
    item: Sched<InternalV>,
    k: int,
)
    requires
        0 <= i < fleet.nodes,
        forall|j: int| 0 <= j < fleet.nodes && j != i ==> #[trigger] node_at(after_w, j) == node_at(before_w, j),
    ensures
        0 <= k <= i ==> owed(fleet, after_w, item, k) + owed_by(node_at(before_w, i), item) == owed(
            fleet,
            before_w,
            item,
            k,
        ) + owed_by(node_at(after_w, i), item),
        k > i ==> owed(fleet, after_w, item, k) == owed(fleet, before_w, item, k),
    decreases fleet.nodes - k,
{
    if k < 0 || k >= fleet.nodes {
    } else {
        lemma_owed_update(fleet, before_w, after_w, i, item, k + 1);
        if k != i {
            assert(node_at(after_w, k) == node_at(before_w, k));
        }
    }
}

pub(crate) proof fn lemma_owed_same(
    fleet: ConcreteConfig,
    before_w: State<CModel>,
    after_w: State<CModel>,
    item: Sched<InternalV>,
    k: int,
)
    requires
        forall|j: int| 0 <= j < fleet.nodes ==> #[trigger] node_at(after_w, j) == node_at(before_w, j),
    ensures
        owed(fleet, after_w, item, k) == owed(fleet, before_w, item, k),
    decreases fleet.nodes - k,
{
    if k < 0 || k >= fleet.nodes {
    } else {
        lemma_owed_same(fleet, before_w, after_w, item, k + 1);
    }
}

pub(crate) proof fn lemma_owed_nonneg(fleet: ConcreteConfig, world: State<CModel>, item: Sched<InternalV>, i: int, k: int)
    requires
        0 <= i < fleet.nodes,
        0 <= k <= i,
    ensures
        owed(fleet, world, item, k) >= owed_by(node_at(world, i), item),
    decreases i - k,
{
    if k < i {
        lemma_owed_nonneg(fleet, world, item, i, k + 1);
    }
}

pub(crate) proof fn lemma_add_multiset<A>(a: Seq<A>, b: Seq<A>)
    ensures
        (a + b).to_multiset() =~= a.to_multiset().add(b.to_multiset()),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
        assert(b =~= Seq::<A>::empty());
        assert(b.to_multiset() =~= Multiset::<A>::empty());
    } else {
        let front = b.drop_last();
        assert(a + b =~= (a + front).push(b.last()));
        assert(b =~= front.push(b.last()));
        lemma_add_multiset(a, front);
    }
}

pub(crate) proof fn lemma_items_add(a: Seq<PendingV>, b: Seq<PendingV>)
    ensures
        items(a + b) =~= items(a) + items(b),
{
}

pub(crate) proof fn lemma_items_push(a: Seq<PendingV>, p: PendingV)
    ensures
        items(a.push(p)) =~= items(a).push(as_item(p)),
{
}

/// `remove_at` is `remove`.
pub(crate) proof fn lemma_remove_at<A>(s: Seq<A>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        echod_abstract_spec::rover::remove_at(s, i) =~= s.remove(i),
{
}

// ---------------------------------------------------------------------------
// Documents
// ---------------------------------------------------------------------------

/// An empty document that reads as `s` under `key` is the empty document.
pub(crate) proof fn lemma_empty_body_rel(key: Seq<char>, doc: DocumentBodyV, s: echod_abstract_spec::state::StoreV)
    requires
        doc_rel(key, doc, s),
        spec_body_is_empty(doc),
    ensures
        doc_rel(key, spec_empty_body(key), s),
{
    match doc {
        DocumentBodyV::Workflow(map) => {
            assert(!echod_concrete_spec::state::spec_starts(key, super::interpretation::schedule_prefix()));
            assert(map.dom().finite());
            assert(map.dom().len() == 0);
            assert(map.dom() =~= Set::<Seq<char>>::empty());
            assert(map =~= Map::<Seq<char>, echod_concrete_spec::state::ObjV>::empty());
            assert(spec_empty_body(key) == DocumentBodyV::Workflow(Map::<Seq<char>, echod_concrete_spec::state::ObjV>::empty()));
        },
        DocumentBodyV::Schedule(slot) => {
            assert(slot is None);
            if echod_concrete_spec::state::spec_starts(key, super::interpretation::schedule_prefix()) {
                assert(spec_empty_body(key) == DocumentBodyV::Schedule(None::<echod_types::Schedule>));
            } else {
                let map = Map::<Seq<char>, echod_concrete_spec::state::ObjV>::empty();
                assert(spec_empty_body(key) == DocumentBodyV::Workflow(map));
                assert(map.dom() =~= Set::<Seq<char>>::empty());
            }
        },
    }
}

/// The owner of a key is the node that owns it.
pub(crate) proof fn lemma_owner(fleet: ConcreteConfig, world: State<CModel>, i: int, key: Seq<char>)
    requires
        shaped(fleet, world),
        0 <= i < fleet.nodes,
    ensures
        spec_owns(node_at(world, i), key) == (owner(fleet, key) == i),
{
    assert(world.process[i].0 == CPid::Node(i as u64));
    let node = node_at(world, i);
    assert(node.nodes == fleet.nodes);
    assert(node.address == i);
    assert(node.nodes as u64 == fleet.nodes);
    assert(node.address as u64 == i as u64);
}

/// The realised string and bytes.
pub(crate) proof fn lemma_string(chars: Seq<char>)
    ensures
        spec_string(chars)@ == chars,
{
    echod_concrete_spec::rover::lemma_string_realised(chars);
}

pub(crate) proof fn lemma_bytes(bytes: Seq<u8>)
    ensures
        echod_concrete_spec::rover::spec_bytes(bytes)@ == bytes,
{
    echod_concrete_spec::rover::lemma_bytes_realised(bytes);
}

/// `spec_notes` sends each note's output to the outside.
pub(crate) proof fn lemma_notes(notes: Seq<NoteV>)
    ensures
        spec_notes(notes).len() == notes.len(),
        forall|k: int|
            0 <= k < notes.len() ==> #[trigger] spec_notes(notes)[k] == (
                CPid::Outside,
                CMessage::Output(note_output(notes[k])),
            ),
    decreases notes.len(),
{
    if notes.len() == 0 {
    } else {
        lemma_notes(notes.drop_first());
        assert(spec_notify(notes[0]) == (CPid::Outside, CMessage::Output(note_output(notes[0]))));
        assert forall|k: int| 0 <= k < notes.len() implies #[trigger] spec_notes(notes)[k] == (
            CPid::Outside,
            CMessage::Output(note_output(notes[k])),
        ) by {
            if k == 0 {
            } else {
                assert(spec_notes(notes)[k] == spec_notes(notes.drop_first())[k - 1]);
                assert(notes.drop_first()[k - 1] == notes[k]);
            }
        };
    }
}

/// A node's reply is the service's output of the same request.
pub(crate) proof fn lemma_reply_is_output(request: Call, response: Response)
    ensures
        spec_reply(request.client@, request.id, response) == (
            CPid::Outside,
            CMessage::Output(Output::Response { client: request.client, id: request.id, response }),
        ),
        reply_output(request.client@, request.id, response) == (Output::Response {
            client: request.client,
            id: request.id,
            response,
        }),
{
    lemma_string(request.client@);
    axiom_string_ext(spec_string(request.client@), request.client);
}

/// `decision` reads the job and the time of a flight.
pub(crate) proof fn lemma_decision_same(a: FlightV, b: FlightV, doc: DocumentBodyV, retry_timeout: u64)
    requires
        a.job == b.job,
        a.now == b.now,
    ensures
        decision(a, doc, retry_timeout) == decision(b, doc, retry_timeout),
{
    reveal(decision);
}

/// A flight that answers a caller answers the probe's caller.
pub(crate) proof fn lemma_reply_same(a: FlightV, b: FlightV, reply: Option<Response>)
    requires
        a.caller == b.caller,
    ensures
        flight_reply(a, reply) == flight_reply(b, reply),
{
}

/// The empty document is empty.
pub(crate) proof fn lemma_empty_is_empty(key: Seq<char>)
    ensures
        spec_body_is_empty(spec_empty_body(key)),
{
    if echod_concrete_spec::state::spec_starts(key, seq!['s', '/']) {
    } else {
        let map = Map::<Seq<char>, echod_concrete_spec::state::ObjV>::empty();
        assert(map.dom() =~= Set::<Seq<char>>::empty());
        assert(Set::<Seq<char>>::empty().len() == 0);
    }
}

/// Forgetting a key that is not cached changes nothing.
pub(crate) proof fn lemma_forget_absent(docs: Seq<CachedV>, key: Seq<char>, i: int)
    requires
        0 <= i <= docs.len(),
        forall|k: int| 0 <= k < docs.len() ==> #[trigger] docs[k].key != key,
    ensures
        spec_forget(docs, key, i) == docs,
    decreases docs.len() - i,
{
    if i >= docs.len() {
    } else {
        lemma_forget_absent(docs, key, i + 1);
    }
}

/// `spec_decide` from a reading flight: the node keeps the document and
/// answers, or opens the write of what it decided.
pub(crate) proof fn lemma_decide(node: NodeV, flight: FlightV, doc: DocumentBodyV)
    requires
        !flight.writing,
    ensures
        ({
            let (next, reply, born, notes) = decision(flight, doc, node.retry_timeout);
            let (after, send) = spec_decide(node, flight, doc);
            if next == held(node, flight.key) && born.len() == 0 {
                &&& after == NodeV {
                    flight: None,
                    documents: spec_keep(node.documents, flight.key, next, flight.etag),
                    ..node
                }
                &&& send == reply_send(flight_reply(flight, reply)) + spec_notes(notes)
            } else {
                let w = written(node, flight, doc);
                &&& after == NodeV { flight: Some(w), next_op: (node.next_op + 1) as u64, ..node }
                &&& send == seq![(CPid::Store, CMessage::StoreReq { op: node.next_op, request: request_of(w) })]
            }
        }),
{
    reveal(decision);
    let (next, reply, born, notes) = decision(flight, doc, node.retry_timeout);
    let (after, send) = spec_decide(node, flight, doc);
    if next == held(node, flight.key) && born.len() == 0 {
    } else {
        let w = written(node, flight, doc);
        assert(w.decided == Some(spec_encode_body(next)));
        assert(w.writing);
        match flight.etag {
            Some(chars) => {
                assert(request_of(w) == StoreReq::PutIfMatch {
                    key: spec_string(flight.key),
                    body: spec_bytes(spec_encode_body(next)),
                    etag: Etag(spec_string(chars)),
                });
            },
            None => {
                assert(request_of(w) == StoreReq::PutIfNoneMatch {
                    key: spec_string(flight.key),
                    body: spec_bytes(spec_encode_body(next)),
                });
            },
        }
    }
}

/// The node slots of the initial world.
pub(crate) proof fn lemma_spec_nodes(fleet: ConcreteConfig, id: u64)
    requires
        id <= fleet.nodes,
    ensures
        spec_nodes(fleet, id).len() == fleet.nodes - id,
        forall|k: int|
            0 <= k < fleet.nodes - id ==> #[trigger] spec_nodes(fleet, id)[k] == (
                CPid::Node((id + k) as u64),
                CProc::Node(initial_node(fleet, (id + k) as u64)),
            ),
    decreases fleet.nodes - id,
{
    if id >= fleet.nodes {
    } else {
        lemma_spec_nodes(fleet, (id + 1) as u64);
        let head = seq![(CPid::Node(id), CProc::Node(initial_node(fleet, id)))];
        let tail = spec_nodes(fleet, (id + 1) as u64);
        assert(spec_nodes(fleet, id) == head + tail);
        assert forall|k: int| 0 <= k < fleet.nodes - id implies #[trigger] spec_nodes(fleet, id)[k] == (
            CPid::Node((id + k) as u64),
            CProc::Node(initial_node(fleet, (id + k) as u64)),
        ) by {
            if k == 0 {
                assert((head + tail)[0] == head[0]);
            } else {
                assert((head + tail)[k] == tail[k - 1]);
            }
        };
    }
}

/// `spec_queue` from `m` offers the ready item at `k >= m`.
pub(crate) proof fn lemma_queue_from(config: AbstractConfig, state: AProc, now: Time, m: int, k: int)
    requires
        0 <= m <= k < state.pending.len(),
        spec_ready(spec_body(state.pending[k]), now),
        !spec_process_work(config, spec_body(state.pending[k]), state.store, now).not_due,
    ensures
        ({
            let results = spec_queue(config, state, now, m);
            let response = spec_process_work(config, spec_body(state.pending[k]), state.store, now);
            exists|j: int|
                0 <= j < results.len() && #[trigger] results[j] == spec_internal_result(state, k, response)
        }),
    decreases k - m,
{
    let results = spec_queue(config, state, now, m);
    let response = spec_process_work(config, spec_body(state.pending[k]), state.store, now);
    let wanted = spec_internal_result(state, k, response);
    if m == k {
        assert(results[0] == wanted);
    } else {
        lemma_queue_from(config, state, now, m + 1, k);
        let tail = spec_queue(config, state, now, m + 1);
        let j = choose|j: int| 0 <= j < tail.len() && #[trigger] tail[j] == wanted;
        let work = spec_body(state.pending[m]);
        let here = spec_process_work(config, work, state.store, now);
        if spec_ready(work, now) && !here.not_due {
            assert(results == seq![spec_internal_result(state, m, here)] + tail);
            assert(results[j + 1] == tail[j]);
        } else {
            assert(results == tail);
        }
    }
}

/// The service's timeout step offers the ready item at `k`: an index into
/// its outcomes whose state removed that item and sends nothing.
pub(crate) proof fn lemma_queue_offers(config: AbstractConfig, state: AProc, now: Time, k: int) -> (j: int)
    requires
        0 <= k < state.pending.len(),
        spec_ready(spec_body(state.pending[k]), now),
        !spec_process_work(config, spec_body(state.pending[k]), state.store, now).not_due,
    ensures
        ({
            let outcomes = state.on_event(config, now, ProcessEvent::Timeout);
            let response = spec_process_work(config, spec_body(state.pending[k]), state.store, now);
            &&& 0 <= j < outcomes.len()
            &&& outcomes[j] == spec_internal_result(state, k, response)
        }),
{
    lemma_queue_from(config, state, now, 0, k);
    let queued = spec_queue(config, state, now, 0);
    let response = spec_process_work(config, spec_body(state.pending[k]), state.store, now);
    let wanted = spec_internal_result(state, k, response);
    let j = choose|j: int| 0 <= j < queued.len() && #[trigger] queued[j] == wanted;
    let results = spec_run_timeout(config, state, now);
    assert(results == queued + self::derived(config, state, now));
    assert(results[j] == queued[j]);
    assert(results.len() > 0);
    assert(state.on_event(config, now, ProcessEvent::Timeout) == results);
    j
}

/// The second half of `spec_run_timeout`, named so the sum above reads.
pub(crate) open spec fn derived(config: AbstractConfig, state: AProc, now: Time) -> Seq<StepResultV<AProc, APid, AMessage>> {
    echod_abstract_spec::rover::spec_derived(config, state, now)
}

/// A timeout result at `j` is an response of the service's timeout step.
pub(crate) proof fn lemma_timeout_offers(config: AbstractConfig, state: AProc, now: Time, j: int)
    requires
        0 <= j < spec_run_timeout(config, state, now).len(),
    ensures
        ({
            let outcomes = state.on_event(config, now, ProcessEvent::Timeout);
            &&& outcomes == spec_run_timeout(config, state, now)
            &&& 0 <= j < outcomes.len()
        }),
{
}

/// The earliest key is a cached key the node owns.
pub(crate) proof fn lemma_earliest_from(
    node: NodeV,
    docs: Seq<CachedV>,
    i: int,
    now: Time,
    best: Option<(u64, Seq<char>)>,
)
    requires
        0 <= i <= docs.len(),
    ensures
        match spec_earliest_from(node, docs, i, now, best) {
            Some(key) => (best is Some && best.unwrap().1 == key) || exists|m: int|
                i <= m < docs.len() && #[trigger] docs[m].key == key && spec_owns(node, key),
            None => true,
        },
    decreases docs.len() - i,
{
    if i >= docs.len() {
    } else if !spec_owns(node, docs[i].key) {
        lemma_earliest_from(node, docs, i + 1, now, best);
    } else {
        match echod_concrete_spec::state::spec_earliest_in(spec_read(docs[i].key, docs[i].body), now) {
            Some(at) => {
                let better = match best {
                    None => true,
                    Some((b, _)) => at < b,
                };
                let next_best = if better { Some((at, docs[i].key)) } else { best };
                lemma_earliest_from(node, docs, i + 1, now, next_best);
                match spec_earliest_from(node, docs, i + 1, now, next_best) {
                    Some(key) => {
                        if better && key == docs[i].key {
                            assert(docs[i].key == key && spec_owns(node, key));
                        }
                    },
                    None => {},
                }
            },
            None => {
                lemma_earliest_from(node, docs, i + 1, now, best);
            },
        }
    }
}

pub(crate) proof fn lemma_earliest_cached(node: NodeV, now: Time, key: Seq<char>)
    requires
        cache_owned(node),
        spec_earliest_key(node, now) == Some(key),
    ensures
        spec_cached(node, key) is Some,
        spec_owns(node, key),
{
    lemma_earliest_from(node, node.documents, 0, now, None);
    let m = choose|m: int|
        0 <= m < node.documents.len() && #[trigger] node.documents[m].key == key && spec_owns(
            node,
            key,
        );
    lemma_cached_is(node.documents, key, m);
}

/// An item a node owes is queued at the service.
pub(crate) proof fn lemma_owed_present(fleet: ConcreteConfig, world: State<AModel>, concrete: State<CModel>, i: int, p: PendingV)
    requires
        0 <= i < fleet.nodes,
        pending_covered(fleet, concrete, astate(world)),
        node_at(concrete, i).pending.contains(p),
    ensures
        astate(world).pending.contains(as_item(p)),
{
    let node = node_at(concrete, i);
    let item = as_item(p);
    let all = items(occurrences(node));
    let k = choose|k: int| 0 <= k < node.pending.len() && node.pending[k] == p;
    assert(occurrences(node)[k] == p);
    assert(all[k] == item);
    assert(all.contains(item));
    assert(all.to_multiset().count(item) > 0);
    assert(owed_by(node, item) >= 1);
    lemma_owed_nonneg(fleet, concrete, item, i, 0);
    assert(astate(world).pending.to_multiset().count(item) >= 1);
}

/// Dropping the head of a pending list drops one of its item.
pub(crate) proof fn lemma_pending_head(pending: Seq<PendingV>, item: Sched<InternalV>)
    requires
        pending.len() > 0,
    ensures
        items(pending).to_multiset().count(item) == items(pending.skip(1)).to_multiset().count(item) + (
        if item == as_item(pending[0]) {
            1int
        } else {
            0int
        }),
{
    let all = items(pending);
    assert(pending.skip(1) =~= pending.remove(0));
    assert(items(pending.remove(0)) =~= all.remove(0));
    assert(all.remove(0).to_multiset() == all.to_multiset().remove(all[0]));
    assert(all[0] == as_item(pending[0]));
    assert(all.contains(all[0]));
    assert(all.to_multiset().count(all[0]) >= 1);
}

// ---------------------------------------------------------------------------
// Frames
// ---------------------------------------------------------------------------

/// What `land` does for a node step.
pub(crate) proof fn lemma_land_node(fleet: ConcreteConfig, cb: State<CModel>, i: int, at: Time, node2: NodeV, send: Seq<(CPid, CMessage)>)
    requires
        shaped(fleet, cb),
        0 <= i < fleet.nodes,
        node2.address == i,
        node2.nodes == fleet.nodes,
        node2.retry_timeout == fleet.retry_timeout,
    ensures
        ({
            let ca = land(cb, i, node_pid(i), at, node_result(node2, send));
            &&& shaped(fleet, ca)
            &&& node_at(ca, i) == node2
            &&& forall|k: int| 0 <= k < fleet.nodes && k != i ==> #[trigger] node_at(ca, k) == node_at(cb, k)
            &&& store_at(fleet, ca) == store_at(fleet, cb)
            &&& ca.network == cb.network + envelopes(node_pid(i), send)
            &&& ca.now == at
            &&& extends(ca.network, cb.network)
        }),
{
    let ca = land(cb, i, node_pid(i), at, node_result(node2, send));
    assert(ca.process == cb.process.update(i, (node_pid(i), CProc::Node(node2))));
    assert(ca.process.len() == cb.process.len());
    assert(ca.process[i] == (node_pid(i), CProc::Node(node2)));
    assert forall|k: int| 0 <= k < fleet.nodes && k != i implies #[trigger] node_at(ca, k) == node_at(cb, k) by {
        assert(ca.process[k] == cb.process[k]);
    };
    assert(ca.process[fleet.nodes as int] == cb.process[fleet.nodes as int]);
    lemma_extends_add(cb.network, envelopes(node_pid(i), send));
}

/// What `land` does for a store step.
pub(crate) proof fn lemma_land_store(fleet: ConcreteConfig, cb: State<CModel>, at: Time, store2: CStore, send: Seq<(CPid, CMessage)>)
    requires
        shaped(fleet, cb),
    ensures
        ({
            let ca = land(cb, fleet.nodes as int, CPid::Store, at, store_result(store2, send));
            &&& shaped(fleet, ca)
            &&& store_at(fleet, ca) == store2
            &&& forall|k: int| 0 <= k < fleet.nodes ==> #[trigger] node_at(ca, k) == node_at(cb, k)
            &&& ca.network == cb.network + envelopes(CPid::Store, send)
            &&& ca.now == at
            &&& extends(ca.network, cb.network)
        }),
{
    let slot = fleet.nodes as int;
    let ca = land(cb, slot, CPid::Store, at, store_result(store2, send));
    assert(ca.process == cb.process.update(slot, (CPid::Store, CProc::Store(store2))));
    assert(ca.process[slot] == (CPid::Store, CProc::Store(store2)));
    assert forall|k: int| 0 <= k < fleet.nodes implies #[trigger] node_at(ca, k) == node_at(cb, k) by {
        assert(ca.process[k] == cb.process[k]);
    };
    lemma_extends_add(cb.network, envelopes(CPid::Store, send));
}

pub(crate) proof fn lemma_requested_grows(
    earlier: State<CModel>,
    later: State<CModel>,
    sender: CPid,
    op: u64,
)
    requires
        requested(earlier, sender, op),
        extends(later.network, earlier.network),
    ensures
        requested(later, sender, op),
{
    let k = choose|k: int|
        #![trigger earlier.network[k]]
        0 <= k < earlier.network.len() && earlier.network[k].sender == sender
            && earlier.network[k].recipient == CPid::Store && earlier.network[k].message is StoreReq
            && earlier.network[k].message->StoreReq_op == op;
    assert(later.network[k] == earlier.network[k]);
}

/// The invariant survives a step that touched no process and added only
/// envelopes that are not store traffic.
pub(crate) proof fn lemma_invariant_grow(fleet: ConcreteConfig, cb: State<CModel>, ca: State<CModel>)
    requires
        inv(fleet, cb),
        ca.process == cb.process,
        extends(ca.network, cb.network),
        forall|k: int|
            cb.network.len() <= k < ca.network.len() ==> no_store_traffic(#[trigger] ca.network[k]),
    ensures
        inv(fleet, ca),
{
    assert forall|k: int| 0 <= k < fleet.nodes implies #[trigger] node_at(ca, k) == node_at(cb, k) by {
        assert(ca.process[k] == cb.process[k]);
    };
    assert(store_at(fleet, ca) == store_at(fleet, cb));
    assert(shaped(fleet, ca));
    assert forall|k: int| 0 <= k < fleet.nodes implies #[trigger] node_ok(k, node_at(ca, k), store_at(fleet, ca)) by {
        assert(node_ok(k, node_at(cb, k), store_at(fleet, cb)));
    };
    assert forall|k: int| 0 <= k < ca.network.len() implies match (#[trigger] ca.network[k]).message {
        CMessage::StoreReq { op, request } => {
            let env = ca.network[k];
            &&& env.recipient == CPid::Store
            &&& env.sender is Node
            &&& {
                let i = env.sender->Node_0 as int;
                let node = node_at(ca, i);
                &&& 0 <= i < fleet.nodes
                &&& op < node.next_op
                &&& (flight_op(node) == Some(op) ==> request == request_of(node.flight.unwrap()))
                &&& (!store_at(fleet, ca).seen.contains((env.sender, op)) ==> flight_op(node) == Some(op))
            }
        },
        _ => true,
    } by {
        if k < cb.network.len() {
            assert(ca.network[k] == cb.network[k]);
        } else {
            assert(no_store_traffic(ca.network[k]));
        }
    };
    assert forall|k: int| 0 <= k < ca.network.len() implies match (#[trigger] ca.network[k]).message {
        CMessage::StoreRes { op, response } => {
            let env = ca.network[k];
            &&& env.sender == CPid::Store
            &&& env.recipient is Node
            &&& {
                let i = env.recipient->Node_0 as int;
                let node = node_at(ca, i);
                &&& 0 <= i < fleet.nodes
                &&& store_at(fleet, ca).seen.contains((env.recipient, op))
                &&& (flight_op(node) == Some(op) ==> response == outcome_of(node.flight.unwrap()))
            }
        },
        _ => true,
    } by {
        if k < cb.network.len() {
            assert(ca.network[k] == cb.network[k]);
        } else {
            assert(no_store_traffic(ca.network[k]));
        }
    };
    assert forall|pair: (CPid, u64)| #[trigger] store_at(fleet, ca).seen.contains(pair) implies requested(
        ca,
        pair.0,
        pair.1,
    ) by {
        assert(store_at(fleet, cb).seen.contains(pair));
        lemma_requested_grows(cb, ca, pair.0, pair.1);
    };
}

pub(crate) proof fn lemma_flight_outputs_monotone(
    node: NodeV,
    earlier: Seq<Envelope<APid, AMessage>>,
    later: Seq<Envelope<APid, AMessage>>,
)
    requires
        flight_outputs_covered(node, earlier),
        extends(later, earlier),
    ensures
        flight_outputs_covered(node, later),
{
    match node.flight {
        None => {},
        Some(flight) => {
            let (_, reply, _, notes) = decision(flight, loaded(node, flight.key), node.retry_timeout);
            match flight_reply(flight, reply) {
                Some((client, id, response)) => {
                    lemma_service_output_monotone(earlier, later, reply_output(client, id, response));
                },
                None => {},
            }
            assert forall|k: int| 0 <= k < notes.len() implies service_output(later, note_output(#[trigger] notes[k])) by {
                lemma_service_output_monotone(earlier, later, note_output(notes[k]));
            };
        },
    }
}

/// The relation carries to worlds whose processes did not change.
pub(crate) proof fn lemma_carry(fleet: ConcreteConfig, cb: State<CModel>, ab: State<AModel>, ca: State<CModel>, aa: State<AModel>)
    requires
        related(fleet, cb, ab),
        ca.process == cb.process,
        aa.process == ab.process,
        extends(aa.network, ab.network),
        aa.now <= ca.now,
        requests_covered(ca.network, aa.network),
        outputs_covered(ca.network, aa.network),
        inv(fleet, ca),
    ensures
        related(fleet, ca, aa),
{
    assert(single(aa));
    assert(astate(aa) == astate(ab));
    assert forall|k: int| 0 <= k < fleet.nodes implies #[trigger] node_at(ca, k) == node_at(cb, k) by {
        assert(ca.process[k] == cb.process[k]);
    };
    assert forall|key: Seq<char>| #[trigger] doc_rel(key, effective(fleet, ca, key), astate(aa).store) by {
        assert(effective(fleet, ca, key) == effective(fleet, cb, key));
    };
    assert forall|item: Sched<InternalV>| #[trigger] owed(fleet, ca, item, 0) <= astate(aa).pending.to_multiset().count(item) by {
        lemma_owed_same(fleet, cb, ca, item, 0);
    };
    assert forall|k: int| 0 <= k < fleet.nodes implies flight_outputs_covered(#[trigger] node_at(ca, k), aa.network) by {
        lemma_flight_outputs_monotone(node_at(cb, k), ab.network, aa.network);
    };
}

/// What `related` says of node `i`, instantiated.
pub(crate) proof fn lemma_node_facts(fleet: ConcreteConfig, cb: State<CModel>, ab: State<AModel>, i: int)
    requires
        related(fleet, cb, ab),
        0 <= i < fleet.nodes,
    ensures
        shaped(fleet, cb),
        cb.process[i].0 == CPid::Node(i as u64),
        cb.process[i].1 is Node,
        node_at(cb, i).address == i,
        node_at(cb, i).nodes == fleet.nodes,
        node_at(cb, i).retry_timeout == fleet.retry_timeout,
        node_ok(i, node_at(cb, i), store_at(fleet, cb)),
        flight_outputs_covered(node_at(cb, i), ab.network),
{
    assert(cb.process[i].0 == CPid::Node(i as u64));
    assert(node_ok(i, node_at(cb, i), store_at(fleet, cb)));
    assert(flight_outputs_covered(node_at(cb, i), ab.network));
}

/// `node_ok` reads nothing of the pending list or the shell.
pub(crate) proof fn lemma_node_ok_pending(i: int, node0: NodeV, node2: NodeV, store: CStore)
    requires
        node_ok(i, node0, store),
        same_work(node2, NodeV { pending: node2.pending, ..node0 }),
    ensures
        node_ok(i, node2, store),
{
    assert(node2.flight == node0.flight);
    assert(node2.documents == node0.documents);
    assert(node2.next_op == node0.next_op);
    assert(node2.address == node0.address);
    assert(node2.nodes == node0.nodes);
    assert(node2.retry_timeout == node0.retry_timeout);
    assert forall|key: Seq<char>| #[trigger] spec_cached(node2, key) == spec_cached(node0, key) by {
    };
    assert forall|key: Seq<char>| #[trigger] loaded(node2, key) == loaded(node0, key) by {
    };
    match node0.flight {
        None => {},
        Some(flight) => {
            assert(loaded(node2, flight.key) == loaded(node0, flight.key));
            assert(decision(flight, loaded(node2, flight.key), node2.retry_timeout) == decision(flight, loaded(node0, flight.key), node0.retry_timeout));
            assert(cached_etag(node2, flight.key) == cached_etag(node0, flight.key));
        },
    }
    assert(flight_ok(node2));
    assert(cache_owned(node2));
    assert forall|key: Seq<char>| spec_owns(node2, key) implies (if applied_write(i, node2, store, key) {
        physical(store, key) == node2.flight.unwrap().decided
    } else {
        match #[trigger] spec_cached(node2, key) {
            Some(cached) => cache_entry_ok(key, cached, store),
            None => physical(store, key) is None,
        }
    }) by {
        assert(spec_owns(node0, key));
        assert(applied_write(i, node2, store, key) == applied_write(i, node0, store, key));
    };
}

/// A node without a flight that keeps a document it had cached still
/// agrees with the store: `key` is cached again with the bytes it held,
/// every other key is cached as before.
pub(crate) proof fn lemma_cache_ok_keep(
    i: int,
    node0: NodeV,
    node2: NodeV,
    store: CStore,
    key: Seq<char>,
    c: CachedV,
    next: DocumentBodyV,
)
    requires
        cache_ok(i, node0, store),
        node0.flight is None,
        node2.flight is None,
        node2.address == node0.address,
        node2.nodes == node0.nodes,
        spec_cached(node0, key) == Some(c),
        cache_entry_ok(key, c, store),
        c.body == spec_encode_body(next),
        spec_body_is_empty(next) && c.etag is None ==> spec_cached(node2, key) is None,
        !(spec_body_is_empty(next) && c.etag is None) ==> spec_cached(node2, key) == Some(
            CachedV { key, body: spec_encode_body(next), etag: c.etag },
        ),
        forall|other: Seq<char>| other != key ==> #[trigger] spec_cached(node2, other)
            == spec_cached(node0, other),
    ensures
        cache_ok(i, node2, store),
{
    assert forall|k: Seq<char>| spec_owns(node2, k) implies (if applied_write(i, node2, store, k) {
        physical(store, k) == node2.flight.unwrap().decided
    } else {
        match #[trigger] spec_cached(node2, k) {
            Some(cc) => cache_entry_ok(k, cc, store),
            None => physical(store, k) is None,
        }
    }) by {
        assert(!applied_write(i, node2, store, k));
        assert(spec_owns(node0, k));
        assert(!applied_write(i, node0, store, k));
        if k == key {
            if spec_body_is_empty(next) && c.etag is None {
                assert(physical(store, key) is None);
            } else {
                lemma_cached_from(node0.documents, key, 0);
                assert(c.key == key);
                assert(CachedV { key, body: spec_encode_body(next), etag: c.etag } == c);
            }
        } else {
            assert(spec_cached(node2, k) == spec_cached(node0, k));
        }
    };
}

/// A node step that sent nothing and changed only its pending list, owing
/// no more than before, is an empty abstract execution.
pub(crate) proof fn lemma_silent(
    fleet: ConcreteConfig,
    config: AbstractConfig,
    cb: State<CModel>,
    ab: State<AModel>,
    i: int,
    at: Time,
    node2: NodeV,
    ca: State<CModel>,
)
    requires
        related(fleet, cb, ab),
        0 <= i < fleet.nodes,
        cb.now <= at,
        same_work(node2, NodeV { pending: node2.pending, ..node_at(cb, i) }),
        forall|item: Sched<InternalV>| #[trigger] owed_by(node2, item) <= owed_by(node_at(cb, i), item),
        ca == land(cb, i, node_pid(i), at, node_result(node2, Seq::empty())),
    ensures
        matches(abstract_model(), config, ab, Seq::<BoundaryEvent>::empty(), ab),
        related(fleet, ca, ab),
{
    lemma_empty_matches(config, ab);
    let node0 = node_at(cb, i);
    let store = store_at(fleet, cb);
    assert(node2.flight == node0.flight);
    assert(node2.documents == node0.documents);
    assert(node2.next_op == node0.next_op);
    assert(node2.address == node0.address);
    assert(node2.nodes == node0.nodes);
    assert(shaped(fleet, cb));
    assert(cb.process[i].0 == CPid::Node(i as u64));
    lemma_land_node(fleet, cb, i, at, node2, Seq::empty());
    assert(envelopes(node_pid(i), Seq::<(CPid, CMessage)>::empty()) =~= Seq::<Envelope<CPid, CMessage>>::empty());
    assert(ca.network =~= cb.network);
    // invariant
    assert forall|k: int| 0 <= k < fleet.nodes implies #[trigger] node_ok(k, node_at(ca, k), store_at(fleet, ca)) by {
        if k == i {
            assert(node_ok(i, node0, store));
            lemma_node_ok_pending(i, node0, node2, store);
        }
    };
    assert forall|k: int| 0 <= k < ca.network.len() implies match (#[trigger] ca.network[k]).message {
        CMessage::StoreReq { op, request } => {
            let env = ca.network[k];
            &&& env.recipient == CPid::Store
            &&& env.sender is Node
            &&& {
                let n = env.sender->Node_0 as int;
                let node = node_at(ca, n);
                &&& 0 <= n < fleet.nodes
                &&& op < node.next_op
                &&& (flight_op(node) == Some(op) ==> request == request_of(node.flight.unwrap()))
                &&& (!store_at(fleet, ca).seen.contains((env.sender, op)) ==> flight_op(node) == Some(op))
            }
        },
        _ => true,
    } by {
        assert(ca.network[k] == cb.network[k]);
        match cb.network[k].message {
            CMessage::StoreReq { op, request } => {
                let n = cb.network[k].sender->Node_0 as int;
                if n == i {
                    assert(node_at(ca, n).flight == node_at(cb, n).flight);
                    assert(node_at(ca, n).next_op == node_at(cb, n).next_op);
                }
            },
            _ => {},
        }
    };
    assert forall|k: int| 0 <= k < ca.network.len() implies match (#[trigger] ca.network[k]).message {
        CMessage::StoreRes { op, response } => {
            let env = ca.network[k];
            &&& env.sender == CPid::Store
            &&& env.recipient is Node
            &&& {
                let n = env.recipient->Node_0 as int;
                let node = node_at(ca, n);
                &&& 0 <= n < fleet.nodes
                &&& store_at(fleet, ca).seen.contains((env.recipient, op))
                &&& (flight_op(node) == Some(op) ==> response == outcome_of(node.flight.unwrap()))
            }
        },
        _ => true,
    } by {
        assert(ca.network[k] == cb.network[k]);
        match cb.network[k].message {
            CMessage::StoreRes { op, response } => {
                let n = cb.network[k].recipient->Node_0 as int;
                if n == i {
                    assert(node_at(ca, n).flight == node_at(cb, n).flight);
                    assert(node_at(ca, n).next_op == node_at(cb, n).next_op);
                }
            },
            _ => {},
        }
    };
    assert forall|pair: (CPid, u64)| #[trigger] store_at(fleet, ca).seen.contains(pair) implies requested(
        ca,
        pair.0,
        pair.1,
    ) by {
        lemma_requested_grows(cb, ca, pair.0, pair.1);
    };
    assert(inv(fleet, ca));
    // the store, read through the nodes
    assert forall|key: Seq<char>| #[trigger] doc_rel(key, effective(fleet, ca, key), astate(ab).store) by {
        let o = owner(fleet, key);
        if o == i {
            assert(intended(node2, key) == intended(node0, key));
        }
        assert(effective(fleet, ca, key) == effective(fleet, cb, key));
    };
    // the occurrences
    assert forall|item: Sched<InternalV>| #[trigger] owed(fleet, ca, item, 0) <= astate(ab).pending.to_multiset().count(item) by {
        lemma_owed_update(fleet, cb, ca, i, item, 0);
        lemma_owed_nonneg(fleet, cb, item, i, 0);
    };
    assert forall|k: int| 0 <= k < fleet.nodes implies flight_outputs_covered(#[trigger] node_at(ca, k), ab.network) by {
        if k == i {
            assert(flight_outputs_covered(node0, ab.network));
            match node2.flight {
                None => {},
                Some(flight) => {
                    assert(loaded(node2, flight.key) == loaded(node0, flight.key));
                },
            }
        }
    };
    lemma_extends_refl(ab.network);
    assert(requests_covered(ca.network, ab.network));
    assert(outputs_covered(ca.network, ab.network));
    assert(related(fleet, ca, ab));
}

/// A node step that changed nothing of the work and sent nothing.
pub(crate) proof fn lemma_same_work(
    fleet: ConcreteConfig,
    config: AbstractConfig,
    cb: State<CModel>,
    ab: State<AModel>,
    i: int,
    at: Time,
    node2: NodeV,
    ca: State<CModel>,
)
    requires
        related(fleet, cb, ab),
        0 <= i < fleet.nodes,
        cb.now <= at,
        same_work(node2, node_at(cb, i)),
        ca == land(cb, i, node_pid(i), at, node_result(node2, Seq::empty())),
    ensures
        matches(abstract_model(), config, ab, Seq::<BoundaryEvent>::empty(), ab),
        related(fleet, ca, ab),
{
    let node0 = node_at(cb, i);
    assert forall|item: Sched<InternalV>| #[trigger] owed_by(node2, item) <= owed_by(node0, item) by {
        assert(occurrences(node2) == occurrences(node0));
    };
    lemma_silent(fleet, config, cb, ab, i, at, node2, ca);
}

/// The relation does not read a node's shell: a world that differs from a
/// related one in the `logic`, `wake`, `next_request` of one node is related
/// to the same abstract world.
pub(crate) proof fn lemma_shell(
    fleet: ConcreteConfig,
    config: AbstractConfig,
    ca: State<CModel>,
    aa: State<AModel>,
    i: int,
    node2: NodeV,
    cs: State<CModel>,
)
    requires
        related(fleet, ca, aa),
        0 <= i < fleet.nodes,
        same_work(node2, node_at(ca, i)),
        cs.process == ca.process.update(i, (node_pid(i), CProc::Node(node2))),
        cs.network == ca.network,
        cs.now == ca.now,
    ensures
        related(fleet, cs, aa),
{
    assert(envelopes(node_pid(i), Seq::<(CPid, CMessage)>::empty()) =~= Seq::<Envelope<CPid, CMessage>>::empty());
    assert(ca.network + envelopes(node_pid(i), Seq::<(CPid, CMessage)>::empty()) =~= ca.network);
    assert(cs == land(ca, i, node_pid(i), ca.now, node_result(node2, Seq::empty())));
    lemma_same_work(fleet, config, ca, aa, i, ca.now, node2, cs);
}

/// A node step lands `node2` where the work lemmas landed `next`, the same
/// work under a new shell: the landed worlds are related to the same
/// abstract world.
pub(crate) proof fn lemma_reshell(
    fleet: ConcreteConfig,
    config: AbstractConfig,
    cb: State<CModel>,
    aa: State<AModel>,
    i: int,
    at: Time,
    next: NodeV,
    node2: NodeV,
    send: Seq<(CPid, CMessage)>,
    ca: State<CModel>,
)
    requires
        related(fleet, land(cb, i, node_pid(i), at, node_result(next, send)), aa),
        0 <= i < fleet.nodes,
        same_work(node2, next),
        ca == land(cb, i, node_pid(i), at, node_result(node2, send)),
    ensures
        related(fleet, ca, aa),
{
    let cw = land(cb, i, node_pid(i), at, node_result(next, send));
    assert(shaped(fleet, cw));
    assert(cw.process[i] == (node_pid(i), CProc::Node(next)));
    assert(node_at(cw, i) == next);
    assert(ca.process =~= cw.process.update(i, (node_pid(i), CProc::Node(node2))));
    lemma_shell(fleet, config, cw, aa, i, node2, ca);
}

/// A node step that dropped the head of its pending list and sent nothing.
pub(crate) proof fn lemma_pop_silent(
    fleet: ConcreteConfig,
    config: AbstractConfig,
    cb: State<CModel>,
    ab: State<AModel>,
    i: int,
    at: Time,
    node2: NodeV,
    ca: State<CModel>,
)
    requires
        related(fleet, cb, ab),
        0 <= i < fleet.nodes,
        cb.now <= at,
        node_at(cb, i).pending.len() > 0,
        same_work(node2, NodeV { pending: node_at(cb, i).pending.skip(1), ..node_at(cb, i) }),
        ca == land(cb, i, node_pid(i), at, node_result(node2, Seq::empty())),
    ensures
        matches(abstract_model(), config, ab, Seq::<BoundaryEvent>::empty(), ab),
        related(fleet, ca, ab),
{
    let node0 = node_at(cb, i);
    let pending = node0.pending;
    assert forall|item: Sched<InternalV>| #[trigger] owed_by(node2, item) <= owed_by(node0, item) by {
        assert(born_of(node2) == born_of(node0));
        lemma_items_add(pending, born_of(node0));
        lemma_items_add(pending.skip(1), born_of(node0));
        lemma_add_multiset(items(pending), items(born_of(node0)));
        lemma_add_multiset(items(pending.skip(1)), items(born_of(node0)));
        lemma_pending_head(pending, item);
    };
    lemma_silent(fleet, config, cb, ab, i, at, node2, ca);
}

// ---------------------------------------------------------------------------
// A flight begins
// ---------------------------------------------------------------------------

/// The job a begin is given names the key and carries a caller as the
/// flight will.
pub(crate) open spec fn begin_keyed(key: Seq<char>, job: JobV, caller: Option<(Seq<char>, u64)>) -> bool {
    match job {
        JobV::External(request) => caller is Some && spec_key(request) == Some(key),
        JobV::Due => caller is None,
        JobV::Occurrence(pending) => caller is None && key == echod_concrete_spec::state::spec_origin_key(
            origin(pending.promise),
        ),
    }
}

/// No op the node has not issued is one the store has seen.
pub(crate) proof fn lemma_fresh_op(fleet: ConcreteConfig, world: State<CModel>, i: int, op: u64)
    requires
        inv(fleet, world),
        0 <= i < fleet.nodes,
        op >= node_at(world, i).next_op,
    ensures
        !store_at(fleet, world).seen.contains((node_pid(i), op)),
        !requested(world, node_pid(i), op),
{
    if requested(world, node_pid(i), op) {
        let k = choose|k: int|
            #![trigger world.network[k]]
            0 <= k < world.network.len() && world.network[k].sender == node_pid(i)
                && world.network[k].recipient == CPid::Store && world.network[k].message is StoreReq
                && world.network[k].message->StoreReq_op == op;
        assert(op < node_at(world, i).next_op);
        assert(false);
    }
    if store_at(fleet, world).seen.contains((node_pid(i), op)) {
        assert(requested(world, node_pid(i), op));
        assert(false);
    }
}

/// Every op a node without a flight has issued, the store has seen.
pub(crate) proof fn lemma_idle_answered(fleet: ConcreteConfig, world: State<CModel>, i: int, op: u64)
    requires
        inv(fleet, world),
        0 <= i < fleet.nodes,
        node_at(world, i).flight is None,
        requested(world, node_pid(i), op),
    ensures
        store_at(fleet, world).seen.contains((node_pid(i), op)),
{
    let k = choose|k: int|
        #![trigger world.network[k]]
        0 <= k < world.network.len() && world.network[k].sender == node_pid(i)
            && world.network[k].recipient == CPid::Store && world.network[k].message is StoreReq
            && world.network[k].message->StoreReq_op == op;
    assert(flight_op(node_at(world, i)) is None);
}

/// Every op a node with a flight has issued, other than the flight's, the
/// store has seen.
pub(crate) proof fn lemma_busy_answered(fleet: ConcreteConfig, world: State<CModel>, i: int, op: u64)
    requires
        inv(fleet, world),
        0 <= i < fleet.nodes,
        node_at(world, i).flight is Some,
        node_at(world, i).flight.unwrap().op != op,
        requested(world, node_pid(i), op),
    ensures
        store_at(fleet, world).seen.contains((node_pid(i), op)),
{
    let k = choose|k: int|
        #![trigger world.network[k]]
        0 <= k < world.network.len() && world.network[k].sender == node_pid(i)
            && world.network[k].recipient == CPid::Store && world.network[k].message is StoreReq
            && world.network[k].message->StoreReq_op == op;
}

/// A seen op of a node is below its next op.
pub(crate) proof fn lemma_seen_issued(fleet: ConcreteConfig, world: State<CModel>, i: int, op: u64)
    requires
        inv(fleet, world),
        0 <= i < fleet.nodes,
        store_at(fleet, world).seen.contains((node_pid(i), op)),
    ensures
        op < node_at(world, i).next_op,
{
    assert(requested(world, node_pid(i), op));
    let k = choose|k: int|
        #![trigger world.network[k]]
        0 <= k < world.network.len() && world.network[k].sender == node_pid(i)
            && world.network[k].recipient == CPid::Store && world.network[k].message is StoreReq
            && world.network[k].message->StoreReq_op == op;
}

/// Store traffic on the network stays right when node `i` moves on and
/// every op it issued before is answered: the new node's next op is at
/// least the old one, its flight, if any, is on a fresh op, and the
/// envelopes added are that flight's request or no store traffic.
pub(crate) proof fn lemma_traffic_ok(
    fleet: ConcreteConfig,
    cb: State<CModel>,
    ca: State<CModel>,
    i: int,
    node2: NodeV,
)
    requires
        inv(fleet, cb),
        0 <= i < fleet.nodes,
        shaped(fleet, ca),
        node_at(ca, i) == node2,
        forall|k: int| 0 <= k < fleet.nodes && k != i ==> #[trigger] node_at(ca, k) == node_at(cb, k),
        store_at(fleet, ca) == store_at(fleet, cb),
        extends(ca.network, cb.network),
        node2.next_op >= node_at(cb, i).next_op,
        forall|op: u64| requested(cb, node_pid(i), op) ==> store_at(fleet, cb).seen.contains((node_pid(i), op)),
        match node2.flight {
            Some(flight) => flight.op >= node_at(cb, i).next_op && flight.op < node2.next_op,
            None => true,
        },
        forall|k: int|
            cb.network.len() <= k < ca.network.len() ==> no_store_traffic(#[trigger] ca.network[k]) || (
            node2.flight is Some && ca.network[k] == Envelope {
                sender: node_pid(i),
                recipient: CPid::Store,
                message: CMessage::StoreReq {
                    op: node2.flight.unwrap().op,
                    request: request_of(node2.flight.unwrap()),
                },
            }),
    ensures
        requests_ok(fleet, ca),
        replies_ok(fleet, ca),
        seen_ok(fleet, ca),
{
    let node0 = node_at(cb, i);
    let store = store_at(fleet, cb);
    assert forall|k: int| 0 <= k < ca.network.len() implies match (#[trigger] ca.network[k]).message {
        CMessage::StoreReq { op, request } => {
            let env = ca.network[k];
            &&& env.recipient == CPid::Store
            &&& env.sender is Node
            &&& {
                let n = env.sender->Node_0 as int;
                let node = node_at(ca, n);
                &&& 0 <= n < fleet.nodes
                &&& op < node.next_op
                &&& (flight_op(node) == Some(op) ==> request == request_of(node.flight.unwrap()))
                &&& (!store_at(fleet, ca).seen.contains((env.sender, op)) ==> flight_op(node) == Some(op))
            }
        },
        _ => true,
    } by {
        if k < cb.network.len() {
            assert(ca.network[k] == cb.network[k]);
            match cb.network[k].message {
                CMessage::StoreReq { op, request } => {
                    let n = cb.network[k].sender->Node_0 as int;
                    if n == i {
                        assert(requested(cb, node_pid(i), op));
                        assert(store.seen.contains((node_pid(i), op)));
                        assert(op < node0.next_op);
                        match node2.flight {
                            Some(flight) => {
                                assert(flight.op != op);
                            },
                            None => {},
                        }
                    }
                },
                _ => {},
            }
        } else {
            if !no_store_traffic(ca.network[k]) {
                let flight = node2.flight.unwrap();
                assert(ca.network[k].message == CMessage::StoreReq { op: flight.op, request: request_of(flight) });
                assert(flight_op(node2) == Some(flight.op));
            }
        }
    };
    assert forall|k: int| 0 <= k < ca.network.len() implies match (#[trigger] ca.network[k]).message {
        CMessage::StoreRes { op, response } => {
            let env = ca.network[k];
            &&& env.sender == CPid::Store
            &&& env.recipient is Node
            &&& {
                let n = env.recipient->Node_0 as int;
                let node = node_at(ca, n);
                &&& 0 <= n < fleet.nodes
                &&& store_at(fleet, ca).seen.contains((env.recipient, op))
                &&& (flight_op(node) == Some(op) ==> response == outcome_of(node.flight.unwrap()))
            }
        },
        _ => true,
    } by {
        if k < cb.network.len() {
            assert(ca.network[k] == cb.network[k]);
            match cb.network[k].message {
                CMessage::StoreRes { op, response } => {
                    let n = cb.network[k].recipient->Node_0 as int;
                    if n == i {
                        lemma_seen_issued(fleet, cb, i, op);
                        match node2.flight {
                            Some(flight) => {
                                assert(flight.op != op);
                            },
                            None => {},
                        }
                    }
                },
                _ => {},
            }
        } else {
            assert(!(ca.network[k].message is StoreRes));
        }
    };
    assert forall|pair: (CPid, u64)| #[trigger] store_at(fleet, ca).seen.contains(pair) implies requested(
        ca,
        pair.0,
        pair.1,
    ) by {
        lemma_requested_grows(cb, ca, pair.0, pair.1);
    };
}

/// The store, read through the nodes, after node `i` changed what it stands
/// for under `key` and nothing else.
pub(crate) proof fn lemma_interpreted_update(
    fleet: ConcreteConfig,
    cb: State<CModel>,
    ca: State<CModel>,
    i: int,
    key: Seq<char>,
    s: AStore,
    next: AStore,
)
    requires
        shaped(fleet, cb),
        shaped(fleet, ca),
        0 <= i < fleet.nodes,
        store_interpreted(fleet, cb, s),
        forall|k: int| 0 <= k < fleet.nodes && k != i ==> #[trigger] node_at(ca, k) == node_at(cb, k),
        spec_owns(node_at(cb, i), key),
        doc_rel(key, effective(fleet, ca, key), next),
        forall|other: Seq<char>|
            other != key && spec_owns(node_at(cb, i), other) ==> #[trigger] intended(node_at(ca, i), other)
                == intended(node_at(cb, i), other),
        others_kept(key, s, next),
    ensures
        store_interpreted(fleet, ca, next),
{
    lemma_owner(fleet, cb, i, key);
    assert forall|other: Seq<char>| #[trigger] doc_rel(other, effective(fleet, ca, other), next) by {
        if other == key {
        } else {
            let o = owner(fleet, other);
            if o == i {
                lemma_owner(fleet, cb, i, other);
                assert(spec_owns(node_at(cb, i), other));
                assert(effective(fleet, ca, other) == effective(fleet, cb, other));
            } else {
                assert(effective(fleet, ca, other) == effective(fleet, cb, other));
            }
            assert(doc_rel(other, effective(fleet, cb, other), s));
        }
    };
}

/// After a flight began at node `i`, the two worlds are related: the
/// abstract world took the step the begin stands for.
pub(crate) proof fn lemma_begin_related(
    fleet: ConcreteConfig,
    cb: State<CModel>,
    ab: State<AModel>,
    ca: State<CModel>,
    aa: State<AModel>,
    i: int,
    at: Time,
    node1: NodeV,
    key: Seq<char>,
    job: JobV,
    caller: Option<(Seq<char>, u64)>,
    node2: NodeV,
    send: Seq<(CPid, CMessage)>,
)
    requires
        related(fleet, cb, ab),
        0 <= i < fleet.nodes,
        cb.now <= at,
        node_at(cb, i).flight is None,
        node_at(cb, i).next_op < u64::MAX,
        node1 == (NodeV { pending: node1.pending, ..node_at(cb, i) }),
        spec_owns(node1, key),
        begin_keyed(key, job, caller),
        (node2, send) == spec_begin(node1, key, job, at, caller),
        ca == land(cb, i, node_pid(i), at, node_result(node2, send)),
        single(aa),
        aa.now <= at,
        extends(aa.network, ab.network),
        finite_store(astate(aa).store),
        ({
            let doc = held(node1, key);
            let (next, reply, born, notes) = decision(probe(key, at, caller, job), doc, node1.retry_timeout);
            &&& doc_rel(key, next, astate(aa).store)
            &&& others_kept(key, astate(ab).store, astate(aa).store)
            &&& forall|item: Sched<InternalV>|
                owed(fleet, cb, item, 0) - owed_by(node_at(cb, i), item) + items(node1.pending + born).to_multiset().count(item)
                    <= #[trigger] astate(aa).pending.to_multiset().count(item)
            &&& match flight_reply(probe(key, at, caller, job), reply) {
                Some((client, id, response)) => service_output(aa.network, reply_output(client, id, response)),
                None => true,
            }
            &&& forall|k: int| 0 <= k < notes.len() ==> service_output(aa.network, note_output(#[trigger] notes[k]))
        }),
    ensures
        related(fleet, ca, aa),
{
    lemma_node_facts(fleet, cb, ab, i);
    let node0 = node_at(cb, i);
    let store = store_at(fleet, cb);
    let s = astate(ab).store;
    let next_store = astate(aa).store;
    let doc = held(node1, key);
    let probe_flight = probe(key, at, caller, job);
    let (next, reply, born, notes) = decision(probe_flight, doc, node0.retry_timeout);
    let op = node0.next_op;
    assert(node1.documents == node0.documents);
    assert(node1.next_op == op);
    assert(node1.flight is None);
    assert(doc == loaded(node0, key));
    assert(spec_owns(node0, key));
    lemma_owner(fleet, cb, i, key);
    assert(effective(fleet, cb, key) == doc);
    assert(doc_rel(key, doc, s));
    lemma_land_node(fleet, cb, i, at, node2, send);
    assert(node_at(ca, i) == node2);
    assert(store_at(fleet, ca) == store);
    lemma_fresh_op(fleet, cb, i, op);
    assert forall|o: u64| requested(cb, node_pid(i), o) implies store.seen.contains((node_pid(i), o)) by {
        lemma_idle_answered(fleet, cb, i, o);
    };
    // the node after the begin
    let cached = spec_cached(node1, key);
    match cached {
        None => {
            let r = spec_flight(op, key, None, at, caller, job);
            assert(node2 == NodeV { flight: Some(r), next_op: (op + 1) as u64, ..node1 });
            assert(send == seq![spec_get(op, key)]);
            assert(request_of(r) == StoreReq::Get { key: spec_string(key) });
            lemma_decision_same(r, probe_flight, doc, node0.retry_timeout);
            lemma_reply_same(r, probe_flight, reply);
            assert(loaded(node2, key) == doc);
            assert(doc == spec_empty_body(key));
            // facts of the node
            assert(flight_ok(node2));
            assert(cache_owned(node2));
            assert forall|k: Seq<char>| spec_owns(node2, k) implies (if applied_write(i, node2, store, k) {
                physical(store, k) == node2.flight.unwrap().decided
            } else {
                match #[trigger] spec_cached(node2, k) {
                    Some(c) => cache_entry_ok(k, c, store),
                    None => physical(store, k) is None,
                }
            }) by {
                assert(!applied_write(i, node2, store, k));
                assert(spec_owns(node0, k));
                assert(!applied_write(i, node0, store, k));
                assert(spec_cached(node2, k) == spec_cached(node0, k));
            };
            assert(node_ok(i, node2, store));
            lemma_envelope_at(node_pid(i), send, 0);
            assert forall|k: int| cb.network.len() <= k < ca.network.len() implies no_store_traffic(#[trigger] ca.network[k]) || (
                node2.flight is Some && ca.network[k] == Envelope {
                    sender: node_pid(i),
                    recipient: CPid::Store,
                    message: CMessage::StoreReq {
                        op: node2.flight.unwrap().op,
                        request: request_of(node2.flight.unwrap()),
                    },
                }) by {
                assert(k == cb.network.len());
                assert(ca.network[k] == envelopes(node_pid(i), send)[0]);
            };
            lemma_traffic_ok(fleet, cb, ca, i, node2);
            // the store, read through the nodes
            assert(intended(node2, key) == next);
            assert forall|other: Seq<char>| other != key && spec_owns(node0, other) implies #[trigger] intended(node2, other)
                == intended(node0, other) by {
                assert(spec_cached(node2, other) == spec_cached(node0, other));
            };
            lemma_interpreted_update(fleet, cb, ca, i, key, s, next_store);
            // the occurrences
            assert(born_of(node2) == born);
            assert(occurrences(node2) == node1.pending + born);
            // the outputs of the flight
            assert(flight_outputs_covered(node2, aa.network));
            // coverage of the new envelope
            assert forall|k: int|
                #![trigger send[k]]
                0 <= k < envelopes(node_pid(i), send).len() implies carried_request(
                envelopes(node_pid(i), send)[k],
                aa.network,
            ) && carried_output(envelopes(node_pid(i), send)[k], aa.network) by {
                assert(k == 0);
            };
            lemma_append_keeps_coverage(cb.network, envelopes(node_pid(i), send), ab.network, aa.network);
        },
        Some(c) => {
            let f = spec_flight(0, key, c.etag, at, caller, job);
            assert(doc == spec_read(key, c.body));
            assert((node2, send) == spec_decide(node1, f, doc));
            lemma_decision_same(f, probe_flight, doc, node0.retry_timeout);
            lemma_reply_same(f, probe_flight, reply);
            lemma_decide(node1, f, doc);
            assert(held(node1, key) == doc);
            assert(cache_entry_ok(key, c, store));
            assert(c.body == spec_encode_body(doc));
            if next == doc && born.len() == 0 {
                // the node keeps the document and answers
                assert(node2 == NodeV {
                    flight: None,
                    documents: spec_keep(node1.documents, key, next, c.etag),
                    ..node1
                });
                assert(send == reply_send(flight_reply(probe_flight, reply)) + spec_notes(notes));
                lemma_keep(node1.documents, key, next, c.etag);
                let docs2 = node2.documents;
                assert(flight_ok(node2));
                assert forall|k: int| 0 <= k < docs2.len() implies spec_owns(node2, #[trigger] docs2[k].key) by {
                    if docs2[k].key == key {
                    } else {
                        let m = choose|m: int| 0 <= m < node1.documents.len() && #[trigger] node1.documents[m] == docs2[k];
                        assert(spec_owns(node0, node0.documents[m].key));
                    }
                };
                assert(cache_owned(node2));
                assert(spec_cached(node0, key) == Some(c));
                assert forall|other: Seq<char>| other != key implies #[trigger] spec_cached(node2, other)
                    == spec_cached(node0, other) by {
                    assert(spec_cached_from(docs2, other, 0) == spec_cached_from(node1.documents, other, 0));
                };
                lemma_cache_ok_keep(i, node0, node2, store, key, c, next);
                assert(node_ok(i, node2, store));
                // the envelopes are outputs
                lemma_notes(notes);
                let sent = envelopes(node_pid(i), send);
                assert forall|k: int| cb.network.len() <= k < ca.network.len() implies no_store_traffic(#[trigger] ca.network[k]) || (
                    node2.flight is Some && ca.network[k] == Envelope {
                        sender: node_pid(i),
                        recipient: CPid::Store,
                        message: CMessage::StoreReq {
                            op: node2.flight.unwrap().op,
                            request: request_of(node2.flight.unwrap()),
                        },
                    }) by {
                    let m = k - cb.network.len();
                    lemma_envelope_at(node_pid(i), send, m);
                    assert(ca.network[k] == sent[m]);
                    let head = reply_send(flight_reply(probe_flight, reply));
                    if m < head.len() {
                        assert(send[m] == head[m]);
                        assert(send[m].1 is Output);
                    } else {
                        assert(send[m] == spec_notes(notes)[m - head.len()]);
                        assert(send[m].1 is Output);
                    }
                };
                lemma_traffic_ok(fleet, cb, ca, i, node2);
                // the store, read through the nodes
                if spec_body_is_empty(next) && c.etag is None {
                    assert(intended(node2, key) == spec_empty_body(key));
                    lemma_empty_body_rel(key, next, next_store);
                } else {
                    axiom_decode_encode_body(next);
                    assert(intended(node2, key) == spec_read(key, spec_encode_body(next)));
                    assert(intended(node2, key) == next);
                }
                assert(doc_rel(key, effective(fleet, ca, key), next_store));
                assert forall|other: Seq<char>| other != key && spec_owns(node0, other) implies #[trigger] intended(node2, other)
                    == intended(node0, other) by {
                    assert(spec_cached(node2, other) == spec_cached(node0, other));
                };
                lemma_interpreted_update(fleet, cb, ca, i, key, s, next_store);
                // the occurrences
                assert(born =~= Seq::<PendingV>::empty());
                assert(occurrences(node2) =~= node1.pending + born);
                assert(flight_outputs_covered(node2, aa.network));
                // coverage of the new envelopes: each is an output the service sent
                assert forall|k: int|
                    #![trigger sent[k]]
                    0 <= k < sent.len() implies carried_request(sent[k], aa.network) && carried_output(
                    sent[k],
                    aa.network,
                ) by {
                    lemma_envelope_at(node_pid(i), send, k);
                    let head = reply_send(flight_reply(probe_flight, reply));
                    if k < head.len() {
                        let (client, id, response) = flight_reply(probe_flight, reply).unwrap();
                        assert(send[k] == spec_reply(client, id, response));
                        assert(sent[k].message == CMessage::Output(reply_output(client, id, response)));
                    } else {
                        let n = k - head.len();
                        assert(send[k] == spec_notes(notes)[n]);
                        assert(sent[k].message == CMessage::Output(note_output(notes[n])));
                    }
                };
                lemma_append_keeps_coverage(cb.network, sent, ab.network, aa.network);
            } else {
                // the node opens the write
                let w = written(node1, f, doc);
                assert(node2 == NodeV { flight: Some(w), next_op: (op + 1) as u64, ..node1 });
                assert(send == seq![(CPid::Store, CMessage::StoreReq { op, request: request_of(w) })]);
                assert(w.op == op);
                assert(w.key == key);
                assert(w.job == job);
                assert(w.now == at);
                assert(w.caller == caller);
                assert(w.etag == c.etag);
                lemma_decision_same(w, probe_flight, doc, node0.retry_timeout);
                lemma_reply_same(w, probe_flight, reply);
                assert(loaded(node2, key) == doc);
                assert(cached_etag(node2, key) == c.etag);
                assert(flight_ok(node2));
                assert(cache_owned(node2));
                assert forall|k: Seq<char>| spec_owns(node2, k) implies (if applied_write(i, node2, store, k) {
                    physical(store, k) == node2.flight.unwrap().decided
                } else {
                    match #[trigger] spec_cached(node2, k) {
                        Some(cc) => cache_entry_ok(k, cc, store),
                        None => physical(store, k) is None,
                    }
                }) by {
                    assert(!store.seen.contains((node_pid(i), op)));
                    assert(!applied_write(i, node2, store, k));
                    assert(spec_owns(node0, k));
                    assert(!applied_write(i, node0, store, k));
                    assert(spec_cached(node2, k) == spec_cached(node0, k));
                };
                assert(node_ok(i, node2, store));
                lemma_envelope_at(node_pid(i), send, 0);
                assert forall|k: int| cb.network.len() <= k < ca.network.len() implies no_store_traffic(#[trigger] ca.network[k]) || (
                    node2.flight is Some && ca.network[k] == Envelope {
                        sender: node_pid(i),
                        recipient: CPid::Store,
                        message: CMessage::StoreReq {
                            op: node2.flight.unwrap().op,
                            request: request_of(node2.flight.unwrap()),
                        },
                    }) by {
                    assert(k == cb.network.len());
                    assert(ca.network[k] == envelopes(node_pid(i), send)[0]);
                };
                lemma_traffic_ok(fleet, cb, ca, i, node2);
                assert(intended(node2, key) == next);
                assert forall|other: Seq<char>| other != key && spec_owns(node0, other) implies #[trigger] intended(node2, other)
                    == intended(node0, other) by {
                    assert(spec_cached(node2, other) == spec_cached(node0, other));
                };
                lemma_interpreted_update(fleet, cb, ca, i, key, s, next_store);
                assert(born_of(node2) == born);
                assert(occurrences(node2) == node1.pending + born);
                assert(flight_outputs_covered(node2, aa.network));
                assert forall|k: int|
                    #![trigger send[k]]
                    0 <= k < envelopes(node_pid(i), send).len() implies carried_request(
                    envelopes(node_pid(i), send)[k],
                    aa.network,
                ) && carried_output(envelopes(node_pid(i), send)[k], aa.network) by {
                    assert(k == 0);
                };
                lemma_append_keeps_coverage(cb.network, envelopes(node_pid(i), send), ab.network, aa.network);
            }
        },
    }
    // what the cases share
    assert(inv(fleet, ca)) by {
        assert forall|k: int| 0 <= k < fleet.nodes implies #[trigger] node_ok(k, node_at(ca, k), store_at(fleet, ca)) by {
            if k != i {
                assert(node_at(ca, k) == node_at(cb, k));
            }
        };
    };
    assert forall|item: Sched<InternalV>| #[trigger] owed(fleet, ca, item, 0) <= astate(aa).pending.to_multiset().count(item) by {
        lemma_owed_update(fleet, cb, ca, i, item, 0);
        lemma_owed_nonneg(fleet, cb, item, i, 0);
        assert(owed_by(node2, item) == items(node1.pending + born).to_multiset().count(item));
    };
    assert forall|k: int| 0 <= k < fleet.nodes implies flight_outputs_covered(#[trigger] node_at(ca, k), aa.network) by {
        if k != i {
            lemma_flight_outputs_monotone(node_at(cb, k), ab.network, aa.network);
        }
    };
    assert(coupled(ca, aa));
    assert(related(fleet, ca, aa));
}

// ---------------------------------------------------------------------------
// A client request
// ---------------------------------------------------------------------------

/// The one send of a served or shed request is the service's output of its reply.
pub(crate) proof fn lemma_send_is_reply(network: Seq<Envelope<APid, AMessage>>, request: Call, response: Response)
    ensures
        ({
            let send = spec_send(request, response, Seq::empty());
            &&& send.len() == 1
            &&& service_output(network + envelopes(APid::Service, send), reply_output(request.client@, request.id, response))
        }),
{
    let send = spec_send(request, response, Seq::empty());
    let output = Output::Response { client: request.client, id: request.id, response };
    assert(Seq::<echod_abstract_spec::state::DispatchV>::empty().map_values(
        |dispatch: echod_abstract_spec::state::DispatchV| (
            APid::Outside,
            AMessage::Output(Output::Dispatch(echod_abstract_spec::state::lift_dispatch(dispatch))),
        ),
    ) =~= Seq::<(APid, AMessage)>::empty());
    assert(send =~= seq![(APid::Outside, AMessage::Output(output))]);
    assert(send[0] == (APid::Outside, AMessage::Output(output)));
    lemma_sent_outputs(network, send, 0);
    lemma_reply_is_output(request, response);
}

/// A node that answered a request without a flight, against an abstract world
/// whose state stayed and whose network carries that reply.
pub(crate) proof fn lemma_answered_idle(
    fleet: ConcreteConfig,
    config: AbstractConfig,
    cb: State<CModel>,
    ab: State<AModel>,
    ca: State<CModel>,
    aa: State<AModel>,
    i: int,
    at: Time,
    node2: NodeV,
    request: Call,
    response: Response,
)
    requires
        related(fleet, cb, ab),
        0 <= i < fleet.nodes,
        cb.now <= at,
        node2 == node_at(cb, i),
        ca == land(cb, i, node_pid(i), at, node_result(node2, seq![spec_reply(request.client@, request.id, response)])),
        single(aa),
        aa.process == ab.process,
        aa.now <= at,
        extends(aa.network, ab.network),
        service_output(aa.network, reply_output(request.client@, request.id, response)),
    ensures
        related(fleet, ca, aa),
{
    let send = seq![spec_reply(request.client@, request.id, response)];
    let cm = land(cb, i, node_pid(i), at, node_result(node2, Seq::empty()));
    lemma_same_work(fleet, config, cb, ab, i, at, node2, cm);
    assert(ca.process == cm.process);
    assert(envelopes(node_pid(i), Seq::<(CPid, CMessage)>::empty()) =~= Seq::<Envelope<CPid, CMessage>>::empty());
    assert(cm.network =~= cb.network);
    let sent = envelopes(node_pid(i), send);
    assert(ca.network == cm.network + sent);
    lemma_extends_add(cm.network, sent);
    lemma_envelope_at(node_pid(i), send, 0);
    assert(sent[0].message == CMessage::Output(reply_output(request.client@, request.id, response)));
    assert forall|k: int| cm.network.len() <= k < ca.network.len() implies no_store_traffic(#[trigger] ca.network[k]) by {
        assert(ca.network[k] == sent[0]);
    };
    lemma_invariant_grow(fleet, cm, ca);
    assert forall|k: int|
        #![trigger sent[k]]
        0 <= k < sent.len() implies carried_request(sent[k], aa.network) && carried_output(sent[k], aa.network) by {
        assert(k == 0);
    };
    lemma_append_keeps_coverage(cm.network, sent, ab.network, aa.network);
    lemma_carry(fleet, cm, ab, ca, aa);
}

/// A request whose handler the node runs: the service serves it, with the
/// first response, at the same time, on the store the node's document reads as.
pub(crate) proof fn lemma_request_served(
    fleet: ConcreteConfig,
    config: AbstractConfig,
    cb: State<CModel>,
    ab: State<AModel>,
    i: int,
    at: Time,
    request: Call,
    key: Seq<char>,
    node2: NodeV,
    send: Seq<(CPid, CMessage)>,
    ca: State<CModel>,
) -> (aa: State<AModel>)
    requires
        agreement(config),
        related(fleet, cb, ab),
        0 <= i < fleet.nodes,
        cb.now <= at,
        service_request(ab.network, request),
        node_at(cb, i).flight is None,
        node_at(cb, i).next_op < u64::MAX,
        spec_key(request.request) == Some(key),
        spec_owns(node_at(cb, i), key),
        (node2, send) == spec_begin(
            node_at(cb, i),
            key,
            JobV::External(request.request),
            at,
            Some((request.client@, request.id)),
        ),
        ca == land(cb, i, node_pid(i), at, node_result(node2, send)),
    ensures
        matches(abstract_model(), config, ab, Seq::<BoundaryEvent>::empty(), aa),
        related(fleet, ca, aa),
{
    reveal(decision);
    let node0 = node_at(cb, i);
    let state = astate(ab);
    let s = state.store;
    let caller = Some((request.client@, request.id));
    let job = JobV::External(request.request);
    let doc = held(node0, key);
    lemma_owner(fleet, cb, i, key);
    assert(effective(fleet, cb, key) == doc);
    assert(doc_rel(key, doc, s));
    assert(request_agrees(config, request.request, key, doc, s, at));
    let (next, response) = spec_handle(doc, request.request, at);
    let outs = spec_handler(config, request.request, s, at);
    assert(outs.len() == 1);
    assert(outs[0].resp == response);
    let event = ProcessEvent::Receive { sender: APid::Outside, message: AMessage::Request(request) };
    assert(event_valid(ab, APid::Service, event));
    let outcomes = state.on_event(config, at, event);
    let served = spec_run(config, state, request, at);
    assert(served.len() == 1);
    assert(served[0] == spec_request_outcome(state, request, outs[0]));
    assert(outcomes == served + echod_abstract_spec::rover::spec_losses(state, request, outs) + seq![spec_shed(state, request)]);
    assert(outcomes[0] == served[0]);
    let aa = lemma_service_step(config, ab, at, event, 0);
    let step_result = outcomes[0];
    assert(outs[0].work =~= Seq::<Sched<InternalV>>::empty());
    assert(outs[0].send =~= Seq::<echod_abstract_spec::state::DispatchV>::empty());
    assert(astate(aa).pending =~= state.pending);
    assert(astate(aa).store == outs[0].next);
    assert(finite_store(astate(aa).store));
    assert(step_result.send == spec_send(request, response, Seq::empty()));
    lemma_send_is_reply(ab.network, request, response);
    // the decision the flight stands for
    let probe_flight = probe(key, at, caller, job);
    let (dnext, dreply, born, notes) = decision(probe_flight, doc, node0.retry_timeout);
    assert(dnext == next);
    assert(dreply == Some(response));
    assert(born.len() == 0);
    assert(notes.len() == 0);
    assert(flight_reply(probe_flight, dreply) == Some((request.client@, request.id, response)));
    // the occurrences: nothing changes
    assert forall|item: Sched<InternalV>|
        owed(fleet, cb, item, 0) - owed_by(node0, item) + items(node0.pending + born).to_multiset().count(item)
            <= #[trigger] astate(aa).pending.to_multiset().count(item) by {
        assert(born =~= Seq::<PendingV>::empty());
        assert(born_of(node0) =~= Seq::<PendingV>::empty());
        assert(occurrences(node0) == node0.pending + born);
        assert(owed_by(node0, item) == items(node0.pending + born).to_multiset().count(item));
    };
    lemma_begin_related(fleet, cb, ab, ca, aa, i, at, node0, key, job, caller, node2, send);
    aa
}

/// A client request at an idle node.
pub(crate) proof fn lemma_request(
    fleet: ConcreteConfig,
    config: AbstractConfig,
    cb: State<CModel>,
    ab: State<AModel>,
    i: int,
    at: Time,
    request: Call,
    node2: NodeV,
    send: Seq<(CPid, CMessage)>,
    ca: State<CModel>,
) -> (aa: State<AModel>)
    requires
        agreement(config),
        related(fleet, cb, ab),
        0 <= i < fleet.nodes,
        cb.now <= at,
        event_valid(cb, node_pid(i), ProcessEvent::Receive { sender: CPid::Outside, message: CMessage::Request(request) }),
        node_at(cb, i).flight is None,
        node_at(cb, i).next_op < u64::MAX,
        (node2, send) == spec_request(node_at(cb, i), at, request),
        ca == land(cb, i, node_pid(i), at, node_result(node2, send)),
    ensures
        matches(abstract_model(), config, ab, Seq::<BoundaryEvent>::empty(), aa),
        related(fleet, ca, aa),
{
    let node0 = node_at(cb, i);
    let state = astate(ab);
    let event = ProcessEvent::Receive { sender: APid::Outside, message: AMessage::Request(request) };
    let wanted = Envelope { sender: CPid::Outside, recipient: node_pid(i), message: CMessage::Request(request) };
    let k = choose|k: int| 0 <= k < cb.network.len() && #[trigger] cb.network[k] == wanted;
    assert(carried_request(cb.network[k], ab.network));
    assert(service_request(ab.network, request));
    let m = choose|m: int|
        #![trigger ab.network[m]]
        0 <= m < ab.network.len() && ab.network[m] == Envelope {
            sender: APid::Outside,
            recipient: APid::Service,
            message: AMessage::Request(request),
        };
    assert(event_valid(ab, APid::Service, event));
    let outcomes = state.on_event(config, at, event);
    match spec_key(request.request) {
        None => {
            assert(node2 == node0);
            let response = spec_pure(request.request);
            assert(send == seq![spec_reply(request.client@, request.id, response)]);
            if empty_heartbeat(request) {
                lemma_empty_heartbeat_is_first(config, state, at, request);
                let aa = lemma_service_step(config, ab, at, event, 0);
                assert(response == Response::Status(echod_types::StatusRes { status: 200 }));
                assert(astate(aa) == state);
                assert(aa.process =~= ab.process);
                lemma_send_is_reply(ab.network, request, response);
                lemma_answered_idle(fleet, config, cb, ab, ca, aa, i, at, node2, request, response);
                aa
            } else {
                lemma_shed_is_last(config, state, at, request);
                let last = outcomes.len() as int - 1;
                let aa = lemma_service_step(config, ab, at, event, last);
                assert(outcomes[last] == spec_shed(state, request));
                assert(response == spec_unavailable(request.request));
                assert(astate(aa) == state);
                assert(aa.process =~= ab.process);
                lemma_send_is_reply(ab.network, request, response);
                lemma_answered_idle(fleet, config, cb, ab, ca, aa, i, at, node2, request, response);
                aa
            }
        },
        Some(key) => {
            if !spec_owns(node0, key) {
                assert(node2 == node0);
                let response = spec_unavailable(request.request);
                assert(send == seq![spec_reply(request.client@, request.id, response)]);
                lemma_shed_is_last(config, state, at, request);
                let last = outcomes.len() as int - 1;
                let aa = lemma_service_step(config, ab, at, event, last);
                assert(outcomes[last] == spec_shed(state, request));
                assert(astate(aa) == state);
                assert(aa.process =~= ab.process);
                lemma_send_is_reply(ab.network, request, response);
                lemma_answered_idle(fleet, config, cb, ab, ca, aa, i, at, node2, request, response);
                aa
            } else {
                lemma_request_served(fleet, config, cb, ab, i, at, request, key, node2, send, ca)
            }
        },
    }
}

// ---------------------------------------------------------------------------
// A timeout: an occurrence, or a due step
// ---------------------------------------------------------------------------

/// One abstract step removed the item at `k` and queued nothing.
pub(crate) proof fn lemma_removed_count(pending: Seq<Sched<InternalV>>, k: int, item: Sched<InternalV>)
    requires
        0 <= k < pending.len(),
    ensures
        (remove_at(pending, k) + Seq::<Sched<InternalV>>::empty()).to_multiset().count(item) == pending.to_multiset().count(item) - (
        if item == pending[k] {
            1int
        } else {
            0int
        }),
{
    lemma_remove_at(pending, k);
    assert(remove_at(pending, k) + Seq::<Sched<InternalV>>::empty() =~= pending.remove(k));
    assert(pending.remove(k).to_multiset() == pending.to_multiset().remove(pending[k]));
    assert(pending.contains(pending[k]));
    assert(pending.to_multiset().count(pending[k]) >= 1);
}

/// A queued occurrence at an idle node that owns its origin.
pub(crate) proof fn lemma_occurrence_begin(
    fleet: ConcreteConfig,
    config: AbstractConfig,
    cb: State<CModel>,
    ab: State<AModel>,
    i: int,
    at: Time,
    node2: NodeV,
    send: Seq<(CPid, CMessage)>,
    ca: State<CModel>,
) -> (aa: State<AModel>)
    requires
        agreement(config),
        related(fleet, cb, ab),
        0 <= i < fleet.nodes,
        cb.now <= at,
        node_at(cb, i).flight is None,
        node_at(cb, i).next_op < u64::MAX,
        node_at(cb, i).pending.len() > 0,
        ({
            let node0 = node_at(cb, i);
            let p = node0.pending[0];
            let node1 = NodeV { pending: node0.pending.skip(1), ..node0 };
            let key = echod_concrete_spec::state::spec_origin_key(origin(p.promise));
            &&& spec_owns(node1, key)
            &&& (node2, send) == spec_begin(node1, key, JobV::Occurrence(p), at, None)
        }),
        ca == land(cb, i, node_pid(i), at, node_result(node2, send)),
    ensures
        matches(abstract_model(), config, ab, Seq::<BoundaryEvent>::empty(), aa),
        related(fleet, ca, aa),
{
    reveal(decision);
    lemma_node_facts(fleet, cb, ab, i);
    let node0 = node_at(cb, i);
    let pending = node0.pending;
    let p = pending[0];
    let node1 = NodeV { pending: pending.skip(1), ..node0 };
    let key = echod_concrete_spec::state::spec_origin_key(origin(p.promise));
    let job = JobV::Occurrence(p);
    let caller = None::<(Seq<char>, u64)>;
    let state = astate(ab);
    let s = state.store;
    let doc = held(node1, key);
    assert(doc == held(node0, key));
    assert(spec_owns(node0, key));
    lemma_owner(fleet, cb, i, key);
    assert(effective(fleet, cb, key) == doc);
    assert(doc_rel(key, doc, s));
    let next = spec_occurrence(doc, p, at);
    let probe_flight = probe(key, at, caller, job);
    let (dnext, dreply, born, notes) = decision(probe_flight, doc, node1.retry_timeout);
    assert(dnext == next);
    assert(dreply is None);
    assert(born.len() == 0);
    assert(notes.len() == 0);
    assert(flight_reply(probe_flight, dreply) is None);
    assert(occurrence_agrees(p, doc, s, at));
    assert(born_of(node0) =~= Seq::<PendingV>::empty());
    assert(born =~= Seq::<PendingV>::empty());
    assert(occurrences(node0) =~= pending);
    assert(node1.pending + born =~= pending.skip(1));
    let item_of = as_item(p);
    if next == doc {
        lemma_empty_matches(config, ab);
        lemma_others_same(key, s);
        lemma_extends_refl(ab.network);
        assert forall|item: Sched<InternalV>|
            owed(fleet, cb, item, 0) - owed_by(node0, item) + items(node1.pending + born).to_multiset().count(item)
                <= #[trigger] astate(ab).pending.to_multiset().count(item) by {
            lemma_pending_head(pending, item);
            assert(owed_by(node0, item) == items(pending).to_multiset().count(item));
            assert(owed(fleet, cb, item, 0) <= state.pending.to_multiset().count(item));
        };
        lemma_begin_related(fleet, cb, ab, ca, ab, i, at, node1, key, job, caller, node2, send);
        ab
    } else {
        let out = spec_create_if_absent(s, p.promise, p.at, p.timeout, p.param, p.tags, at);
        assert(!out.not_due);
        assert(out.work.len() == 0);
        assert(out.send.len() == 0);
        assert(doc_rel(key, next, out.next));
        assert(others_kept(key, s, out.next));
        assert(p.at <= at);
        lemma_owed_present(fleet, ab, cb, i, p);
        let k = choose|k: int| 0 <= k < state.pending.len() && state.pending[k] == item_of;
        let work = InternalV::Occurrence {
            promise: p.promise,
            at: p.at,
            timeout: p.timeout,
            param: p.param,
            tags: p.tags,
        };
        assert(spec_body(state.pending[k]) == work);
        assert(spec_ready(work, at));
        assert(spec_process_work(config, work, s, at) == out);
        let j = lemma_queue_offers(config, state, at, k);
        let aa = lemma_service_step(config, ab, at, ProcessEvent::Timeout, j);
        let response = state.on_event(config, at, ProcessEvent::Timeout)[j];
        assert(response == spec_internal_result(state, k, out));
        assert(astate(aa).store == out.next);
        assert(finite_store(astate(aa).store));
        assert(astate(aa).pending == remove_at(state.pending, k) + out.work);
        assert(out.work =~= Seq::<Sched<InternalV>>::empty());
        assert(response.send =~= Seq::<(APid, AMessage)>::empty());
        assert forall|item: Sched<InternalV>|
            owed(fleet, cb, item, 0) - owed_by(node0, item) + items(node1.pending + born).to_multiset().count(item)
                <= #[trigger] astate(aa).pending.to_multiset().count(item) by {
            lemma_pending_head(pending, item);
            lemma_removed_count(state.pending, k, item);
            assert(owed_by(node0, item) == items(pending).to_multiset().count(item));
            assert(owed(fleet, cb, item, 0) <= state.pending.to_multiset().count(item));
        };
        lemma_begin_related(fleet, cb, ab, ca, aa, i, at, node1, key, job, caller, node2, send);
        aa
    }
}

/// The notes an abstract timeout result sends are on the network it lands on.
pub(crate) proof fn lemma_note_sends(network: Seq<Envelope<APid, AMessage>>, notes: Seq<NoteV>)
    ensures
        forall|k: int|
            0 <= k < notes.len() ==> service_output(
                network + envelopes(APid::Service, note_sends(notes)),
                note_output(#[trigger] notes[k]),
            ),
{
    let send = note_sends(notes);
    assert forall|k: int| 0 <= k < notes.len() implies service_output(
        network + envelopes(APid::Service, send),
        note_output(#[trigger] notes[k]),
    ) by {
        assert(send[k] == (APid::Outside, AMessage::Output(note_output(notes[k]))));
        lemma_sent_outputs(network, send, k);
    };
}

/// The due step of the earliest cached key at an idle node.
pub(crate) proof fn lemma_due_begin(
    fleet: ConcreteConfig,
    config: AbstractConfig,
    cb: State<CModel>,
    ab: State<AModel>,
    i: int,
    at: Time,
    key: Seq<char>,
    node2: NodeV,
    send: Seq<(CPid, CMessage)>,
    ca: State<CModel>,
) -> (aa: State<AModel>)
    requires
        config == abstract_config(fleet),
        agreement(config),
        related(fleet, cb, ab),
        0 <= i < fleet.nodes,
        cb.now <= at,
        node_at(cb, i).flight is None,
        node_at(cb, i).next_op < u64::MAX,
        node_at(cb, i).pending.len() == 0,
        spec_earliest_key(node_at(cb, i), at) == Some(key),
        (node2, send) == spec_begin(node_at(cb, i), key, JobV::Due, at, None),
        ca == land(cb, i, node_pid(i), at, node_result(node2, send)),
    ensures
        matches(abstract_model(), config, ab, Seq::<BoundaryEvent>::empty(), aa),
        related(fleet, ca, aa),
{
    reveal(decision);
    lemma_node_facts(fleet, cb, ab, i);
    let node0 = node_at(cb, i);
    let state = astate(ab);
    let s = state.store;
    let job = JobV::Due;
    let caller = None::<(Seq<char>, u64)>;
    lemma_earliest_cached(node0, at, key);
    lemma_owner(fleet, cb, i, key);
    let doc = held(node0, key);
    assert(effective(fleet, cb, key) == doc);
    assert(doc_rel(key, doc, s));
    let probe_flight = probe(key, at, caller, job);
    let (next, reply, born, notes) = decision(probe_flight, doc, node0.retry_timeout);
    assert(node0.retry_timeout == config.retry_timeout);
    assert((next, reply, born, notes) == spec_run_due(doc, at, config.retry_timeout));
    assert(flight_reply(probe_flight, reply) is None);
    assert(due_agrees(config, key, doc, state, at));
    assert(born_of(node0) =~= Seq::<PendingV>::empty());
    assert(occurrences(node0) =~= Seq::<PendingV>::empty());
    assert(items(Seq::<PendingV>::empty()) =~= Seq::<Sched<InternalV>>::empty());
    assert(node0.pending + born =~= born);
    if next == doc && born.len() == 0 && notes.len() == 0 {
        lemma_empty_matches(config, ab);
        lemma_others_same(key, s);
        lemma_extends_refl(ab.network);
        assert forall|item: Sched<InternalV>|
            owed(fleet, cb, item, 0) - owed_by(node0, item) + items(node0.pending + born).to_multiset().count(item)
                <= #[trigger] astate(ab).pending.to_multiset().count(item) by {
            assert(owed_by(node0, item) == 0);
            assert(born =~= Seq::<PendingV>::empty());
            assert(items(born).to_multiset().count(item) == 0);
            assert(owed(fleet, cb, item, 0) <= state.pending.to_multiset().count(item));
        };
        lemma_begin_related(fleet, cb, ab, ca, ab, i, at, node0, key, job, caller, node2, send);
        ab
    } else {
        let results = spec_run_timeout(config, state, at);
        let j = choose|j: int|
            {
                &&& 0 <= j < results.len()
                &&& (#[trigger] results[j]).send == note_sends(notes)
                &&& results[j].state.pending == state.pending + items(born)
                &&& doc_rel(key, next, results[j].state.store)
                &&& others_kept(key, state.store, results[j].state.store)
                &&& finite_store(results[j].state.store)
            };
        lemma_timeout_offers(config, state, at, j);
        let aa = lemma_service_step(config, ab, at, ProcessEvent::Timeout, j);
        assert(astate(aa) == results[j].state);
        assert(finite_store(astate(aa).store));
        assert(aa.network == ab.network + envelopes(APid::Service, note_sends(notes)));
        lemma_note_sends(ab.network, notes);
        assert forall|item: Sched<InternalV>|
            owed(fleet, cb, item, 0) - owed_by(node0, item) + items(node0.pending + born).to_multiset().count(item)
                <= #[trigger] astate(aa).pending.to_multiset().count(item) by {
            assert(owed_by(node0, item) == 0);
            lemma_add_multiset(state.pending, items(born));
            assert(owed(fleet, cb, item, 0) <= state.pending.to_multiset().count(item));
        };
        lemma_begin_related(fleet, cb, ab, ca, aa, i, at, node0, key, job, caller, node2, send);
        aa
    }
}

// ---------------------------------------------------------------------------
// The store answers
// ---------------------------------------------------------------------------

/// Every op a busy node issued, the store has seen, once its flight's op is.
pub(crate) proof fn lemma_all_answered(fleet: ConcreteConfig, world: State<CModel>, i: int)
    requires
        inv(fleet, world),
        0 <= i < fleet.nodes,
        node_at(world, i).flight is Some,
        store_at(fleet, world).seen.contains((node_pid(i), node_at(world, i).flight.unwrap().op)),
    ensures
        forall|op: u64| requested(world, node_pid(i), op) ==> store_at(fleet, world).seen.contains((node_pid(i), op)),
{
    let flight = node_at(world, i).flight.unwrap();
    assert forall|op: u64| requested(world, node_pid(i), op) implies store_at(fleet, world).seen.contains((node_pid(i), op)) by {
        if op != flight.op {
            lemma_busy_answered(fleet, world, i, op);
        }
    };
}

/// The sends of a closing flight are outputs the service already sent.
pub(crate) proof fn lemma_closing_sends(
    node: NodeV,
    network: Seq<Envelope<APid, AMessage>>,
    i: int,
    send: Seq<(CPid, CMessage)>,
)
    requires
        node.flight is Some,
        flight_outputs_covered(node, network),
        ({
            let flight = node.flight.unwrap();
            let (_, reply, _, notes) = decision(flight, loaded(node, flight.key), node.retry_timeout);
            send == reply_send(flight_reply(flight, reply)) + spec_notes(notes)
        }),
    ensures
        forall|k: int|
            #![trigger envelopes(node_pid(i), send)[k]]
            0 <= k < send.len() ==> no_store_traffic(envelopes(node_pid(i), send)[k]) && carried_request(
                envelopes(node_pid(i), send)[k],
                network,
            ) && carried_output(envelopes(node_pid(i), send)[k], network),
{
    let flight = node.flight.unwrap();
    let (_, reply, _, notes) = decision(flight, loaded(node, flight.key), node.retry_timeout);
    let head = reply_send(flight_reply(flight, reply));
    let sent = envelopes(node_pid(i), send);
    lemma_notes(notes);
    assert forall|k: int|
        #![trigger sent[k]]
        0 <= k < send.len() implies no_store_traffic(sent[k]) && carried_request(sent[k], network) && carried_output(
        sent[k],
        network,
    ) by {
        lemma_envelope_at(node_pid(i), send, k);
        if k < head.len() {
            let (client, id, response) = flight_reply(flight, reply).unwrap();
            assert(send[k] == spec_reply(client, id, response));
            assert(sent[k].message == CMessage::Output(reply_output(client, id, response)));
        } else {
            let n = k - head.len();
            assert(send[k] == spec_notes(notes)[n]);
            assert(sent[k].message == CMessage::Output(note_output(notes[n])));
        }
    };
}

/// A flight closes: the node holds what the flight decided, owes what it
/// bore, and sends what the service already sent. An empty abstract execution.
pub(crate) proof fn lemma_flight_closed(
    fleet: ConcreteConfig,
    config: AbstractConfig,
    cb: State<CModel>,
    ab: State<AModel>,
    i: int,
    at: Time,
    node2: NodeV,
    send: Seq<(CPid, CMessage)>,
    ca: State<CModel>,
)
    requires
        related(fleet, cb, ab),
        0 <= i < fleet.nodes,
        cb.now <= at,
        node_at(cb, i).flight is Some,
        store_at(fleet, cb).seen.contains((node_pid(i), node_at(cb, i).flight.unwrap().op)),
        node2.flight is None,
        node2.next_op == node_at(cb, i).next_op,
        node2.address == node_at(cb, i).address,
        node2.nodes == node_at(cb, i).nodes,
        node2.retry_timeout == node_at(cb, i).retry_timeout,
        ({
            let node0 = node_at(cb, i);
                    let flight = node0.flight.unwrap();
            let key = flight.key;
            let (next, reply, born, notes) = decision(flight, loaded(node0, key), node0.retry_timeout);
            let docs2 = node2.documents;
            &&& node2.pending == node0.pending + born
            &&& forall|j: int, k: int| 0 <= j < k < docs2.len() ==> #[trigger] docs2[j].key != #[trigger] docs2[k].key
            &&& forall|other: Seq<char>| other != key ==> #[trigger] spec_cached(node2, other) == spec_cached(node0, other)
            &&& forall|k: int| 0 <= k < docs2.len() ==> #[trigger] docs2[k].key == key || exists|m: int|
                0 <= m < node0.documents.len() && #[trigger] node0.documents[m] == docs2[k]
            &&& loaded(node2, key) == next
            &&& match spec_cached(node2, key) {
                Some(c) => cache_entry_ok(key, c, store_at(fleet, cb)),
                None => physical(store_at(fleet, cb), key) is None,
            }
            &&& send == reply_send(flight_reply(flight, reply)) + spec_notes(notes)
        }),
        ca == land(cb, i, node_pid(i), at, node_result(node2, send)),
    ensures
        matches(abstract_model(), config, ab, Seq::<BoundaryEvent>::empty(), ab),
        related(fleet, ca, ab),
{
    lemma_empty_matches(config, ab);
    lemma_node_facts(fleet, cb, ab, i);
    let node0 = node_at(cb, i);
    let flight = node0.flight.unwrap();
    let key = flight.key;
    let store = store_at(fleet, cb);
    let s = astate(ab).store;
    let (next, reply, born, notes) = decision(flight, loaded(node0, key), node0.retry_timeout);
    let docs2 = node2.documents;
    assert(flight_ok(node0));
    assert(spec_owns(node0, key));
    lemma_owner(fleet, cb, i, key);
    lemma_land_node(fleet, cb, i, at, node2, send);
    lemma_all_answered(fleet, cb, i);
    // the node
    assert(flight_ok(node2));
    assert forall|k: int| 0 <= k < docs2.len() implies spec_owns(node2, #[trigger] docs2[k].key) by {
        if docs2[k].key == key {
        } else {
            let m = choose|m: int| 0 <= m < node0.documents.len() && #[trigger] node0.documents[m] == docs2[k];
            assert(spec_owns(node0, node0.documents[m].key));
        }
    };
    assert(cache_owned(node2));
    assert forall|k: Seq<char>| spec_owns(node2, k) implies (if applied_write(i, node2, store, k) {
        physical(store, k) == node2.flight.unwrap().decided
    } else {
        match #[trigger] spec_cached(node2, k) {
            Some(c) => cache_entry_ok(k, c, store),
            None => physical(store, k) is None,
        }
    }) by {
        assert(!applied_write(i, node2, store, k));
        assert(spec_owns(node0, k));
        if k == key {
        } else {
            assert(!applied_write(i, node0, store, k));
            assert(spec_cached(node2, k) == spec_cached(node0, k));
        }
    };
    assert(node_ok(i, node2, store));
    // the traffic
    lemma_closing_sends(node0, ab.network, i, send);
    let sent = envelopes(node_pid(i), send);
    assert forall|k: int| cb.network.len() <= k < ca.network.len() implies no_store_traffic(#[trigger] ca.network[k]) by {
        let m = k - cb.network.len();
        assert(ca.network[k] == sent[m]);
    };
    lemma_traffic_ok(fleet, cb, ca, i, node2);
    assert(inv(fleet, ca)) by {
        assert forall|k: int| 0 <= k < fleet.nodes implies #[trigger] node_ok(k, node_at(ca, k), store_at(fleet, ca)) by {
            if k != i {
                assert(node_at(ca, k) == node_at(cb, k));
            }
        };
    };
    // the store, read through the nodes
    assert(intended(node0, key) == next);
    assert(effective(fleet, cb, key) == next);
    assert(intended(node2, key) == next);
    assert(doc_rel(key, effective(fleet, ca, key), s));
    assert forall|other: Seq<char>| other != key && spec_owns(node0, other) implies #[trigger] intended(node2, other)
        == intended(node0, other) by {
        assert(spec_cached(node2, other) == spec_cached(node0, other));
    };
    lemma_others_same(key, s);
    lemma_interpreted_update(fleet, cb, ca, i, key, s, s);
    // the occurrences
    assert(born_of(node0) == born);
    assert(born_of(node2) =~= Seq::<PendingV>::empty());
    assert(occurrences(node2) =~= occurrences(node0));
    assert forall|item: Sched<InternalV>| #[trigger] owed(fleet, ca, item, 0) <= astate(ab).pending.to_multiset().count(item) by {
        assert(owed_by(node2, item) == owed_by(node0, item));
        lemma_owed_update(fleet, cb, ca, i, item, 0);
    };
    assert forall|k: int| 0 <= k < fleet.nodes implies flight_outputs_covered(#[trigger] node_at(ca, k), ab.network) by {
        if k != i {
            assert(node_at(ca, k) == node_at(cb, k));
        }
    };
    lemma_extends_refl(ab.network);
    lemma_append_keeps_coverage(cb.network, sent, ab.network, ab.network);
    assert(coupled(ca, ab));
    assert(related(fleet, ca, ab));
}

/// A read came back empty and the flight decided to write: the node opens
/// the write of the same decision. An empty abstract execution.
pub(crate) proof fn lemma_write_after_read(
    fleet: ConcreteConfig,
    config: AbstractConfig,
    cb: State<CModel>,
    ab: State<AModel>,
    i: int,
    at: Time,
    node2: NodeV,
    send: Seq<(CPid, CMessage)>,
    ca: State<CModel>,
)
    requires
        related(fleet, cb, ab),
        0 <= i < fleet.nodes,
        cb.now <= at,
        node_at(cb, i).flight is Some,
        node_at(cb, i).next_op < u64::MAX,
        !node_at(cb, i).flight.unwrap().writing,
        store_at(fleet, cb).seen.contains((node_pid(i), node_at(cb, i).flight.unwrap().op)),
        ({
            let node0 = node_at(cb, i);
            let flight = node0.flight.unwrap();
            let rest = NodeV { flight: None, ..node0 };
            let w = written(rest, flight, spec_empty_body(flight.key));
            &&& node2 == NodeV { flight: Some(w), next_op: (node0.next_op + 1) as u64, ..rest }
            &&& send == seq![(CPid::Store, CMessage::StoreReq { op: node0.next_op, request: request_of(w) })]
        }),
        ca == land(cb, i, node_pid(i), at, node_result(node2, send)),
    ensures
        matches(abstract_model(), config, ab, Seq::<BoundaryEvent>::empty(), ab),
        related(fleet, ca, ab),
{
    lemma_empty_matches(config, ab);
    lemma_node_facts(fleet, cb, ab, i);
    let node0 = node_at(cb, i);
    let flight = node0.flight.unwrap();
    let key = flight.key;
    let store = store_at(fleet, cb);
    let s = astate(ab).store;
    let op = node0.next_op;
    let rest = NodeV { flight: None, ..node0 };
    let doc = spec_empty_body(key);
    let w = written(rest, flight, doc);
    assert(flight_ok(node0));
    assert(spec_cached(node0, key) is None);
    assert(loaded(node0, key) == doc);
    let (next, reply, born, notes) = decision(flight, doc, node0.retry_timeout);
    assert(spec_owns(node0, key));
    lemma_owner(fleet, cb, i, key);
    lemma_land_node(fleet, cb, i, at, node2, send);
    lemma_all_answered(fleet, cb, i);
    lemma_fresh_op(fleet, cb, i, op);
    assert(w.op == op);
    assert(w.key == key);
    assert(w.job == flight.job);
    assert(w.now == flight.now);
    assert(w.caller == flight.caller);
    assert(w.etag == flight.etag);
    assert(w.writing);
    assert(w.decided == Some(spec_encode_body(next)));
    assert(w.born == born);
    assert(w.notify == notes);
    assert(w.reply == flight_reply(flight, reply));
    lemma_decision_same(w, flight, doc, node0.retry_timeout);
    lemma_reply_same(w, flight, reply);
    assert(decision(w, doc, node0.retry_timeout) == decision(flight, doc, node0.retry_timeout));
    assert(flight_reply(w, reply) == flight_reply(flight, reply));
    assert(job_keyed(w));
    assert(node2.documents == node0.documents);
    assert(loaded(node2, key) == doc);
    assert(cached_etag(node2, key) is None);
    // the node
    assert(flight_ok(node2));
    assert(cache_owned(node2));
    assert forall|k: Seq<char>| spec_owns(node2, k) implies (if applied_write(i, node2, store, k) {
        physical(store, k) == node2.flight.unwrap().decided
    } else {
        match #[trigger] spec_cached(node2, k) {
            Some(c) => cache_entry_ok(k, c, store),
            None => physical(store, k) is None,
        }
    }) by {
        assert(!applied_write(i, node2, store, k));
        assert(spec_owns(node0, k));
        assert(!applied_write(i, node0, store, k));
        assert(spec_cached(node2, k) == spec_cached(node0, k));
    };
    assert(node_ok(i, node2, store));
    // the traffic
    lemma_envelope_at(node_pid(i), send, 0);
    assert forall|k: int| cb.network.len() <= k < ca.network.len() implies no_store_traffic(#[trigger] ca.network[k]) || (
        node2.flight is Some && ca.network[k] == Envelope {
            sender: node_pid(i),
            recipient: CPid::Store,
            message: CMessage::StoreReq {
                op: node2.flight.unwrap().op,
                request: request_of(node2.flight.unwrap()),
            },
        }) by {
        assert(k == cb.network.len());
        assert(ca.network[k] == envelopes(node_pid(i), send)[0]);
    };
    lemma_traffic_ok(fleet, cb, ca, i, node2);
    assert(inv(fleet, ca)) by {
        assert forall|k: int| 0 <= k < fleet.nodes implies #[trigger] node_ok(k, node_at(ca, k), store_at(fleet, ca)) by {
            if k != i {
                assert(node_at(ca, k) == node_at(cb, k));
            }
        };
    };
    // the store, read through the nodes
    assert(intended(node0, key) == next);
    assert(intended(node2, key) == next);
    assert(effective(fleet, cb, key) == next);
    assert(doc_rel(key, effective(fleet, ca, key), s));
    assert forall|other: Seq<char>| other != key && spec_owns(node0, other) implies #[trigger] intended(node2, other)
        == intended(node0, other) by {
        assert(spec_cached(node2, other) == spec_cached(node0, other));
    };
    lemma_others_same(key, s);
    lemma_interpreted_update(fleet, cb, ca, i, key, s, s);
    // the occurrences
    assert(born_of(node0) == born);
    assert(born_of(node2) == born);
    assert(occurrences(node2) == occurrences(node0));
    assert forall|item: Sched<InternalV>| #[trigger] owed(fleet, ca, item, 0) <= astate(ab).pending.to_multiset().count(item) by {
        assert(owed_by(node2, item) == owed_by(node0, item));
        lemma_owed_update(fleet, cb, ca, i, item, 0);
    };
    assert forall|k: int| 0 <= k < fleet.nodes implies flight_outputs_covered(#[trigger] node_at(ca, k), ab.network) by {
        if k != i {
            assert(node_at(ca, k) == node_at(cb, k));
        } else {
            assert(flight_outputs_covered(node0, ab.network));
        }
    };
    lemma_extends_refl(ab.network);
    let sent = envelopes(node_pid(i), send);
    assert forall|k: int|
        #![trigger sent[k]]
        0 <= k < sent.len() implies carried_request(sent[k], ab.network) && carried_output(sent[k], ab.network) by {
        assert(k == 0);
    };
    lemma_append_keeps_coverage(cb.network, sent, ab.network, ab.network);
    assert(coupled(ca, ab));
    assert(related(fleet, ca, ab));
}

/// A store reply at a busy node.
pub(crate) proof fn lemma_store_reply(
    fleet: ConcreteConfig,
    config: AbstractConfig,
    cb: State<CModel>,
    ab: State<AModel>,
    i: int,
    at: Time,
    op: u64,
    response: StoreRes,
    node2: NodeV,
    send: Seq<(CPid, CMessage)>,
    ca: State<CModel>,
)
    requires
        related(fleet, cb, ab),
        0 <= i < fleet.nodes,
        cb.now <= at,
        event_valid(cb, node_pid(i), ProcessEvent::Receive { sender: CPid::Store, message: CMessage::StoreRes { op, response } }),
        node_at(cb, i).flight is Some,
        node_at(cb, i).next_op < u64::MAX,
        (node2, send) == spec_store_reply(node_at(cb, i), op, response),
        ca == land(cb, i, node_pid(i), at, node_result(node2, send)),
    ensures
        matches(abstract_model(), config, ab, Seq::<BoundaryEvent>::empty(), ab),
        related(fleet, ca, ab),
{
    lemma_node_facts(fleet, cb, ab, i);
    let node0 = node_at(cb, i);
    let flight = node0.flight.unwrap();
    let key = flight.key;
    let store = store_at(fleet, cb);
    if flight.op != op {
        assert(node2 == node0);
        assert(send =~= Seq::<(CPid, CMessage)>::empty());
        lemma_same_work(fleet, config, cb, ab, i, at, node2, ca);
    } else {
        let wanted = Envelope {
            sender: CPid::Store,
            recipient: node_pid(i),
            message: CMessage::StoreRes { op, response },
        };
        let k = choose|k: int| 0 <= k < cb.network.len() && #[trigger] cb.network[k] == wanted;
        assert(store.seen.contains((node_pid(i), op)));
        assert(flight_op(node0) == Some(op));
        assert(response == outcome_of(flight));
        assert(flight_ok(node0));
        let doc0 = loaded(node0, key);
        let (next, reply, born, notes) = decision(flight, doc0, node0.retry_timeout);
        if !flight.writing {
            assert(response == StoreRes::Get { result: Ok(None) });
            assert(flight.etag is None);
            assert(spec_cached(node0, key) is None);
            assert(doc0 == spec_empty_body(key));
            let rest = NodeV { flight: None, ..node0 };
            assert(FlightV { etag: None, ..flight } == flight);
            assert((node2, send) == spec_decide(rest, flight, doc0));
            lemma_decide(rest, flight, doc0);
            assert(held(rest, key) == doc0);
            if next == doc0 && born.len() == 0 {
                lemma_empty_is_empty(key);
                assert(spec_body_is_empty(next));
                assert(spec_keep(rest.documents, key, next, None) == spec_forget(rest.documents, key, 0));
                lemma_cached_from(node0.documents, key, 0);
                lemma_forget_absent(node0.documents, key, 0);
                assert(node2.documents == node0.documents);
                assert(node2.flight is None);
                assert(node2.pending == node0.pending);
                assert(born =~= Seq::<PendingV>::empty());
                assert(node2.pending == node0.pending + born);
                assert(loaded(node2, key) == doc0);
                assert(spec_cached(node2, key) is None);
                assert(!applied_write(i, node0, store, key));
                assert(physical(store, key) is None);
                assert forall|a: int, b: int| 0 <= a < b < node2.documents.len() implies #[trigger] node2.documents[a].key
                    != #[trigger] node2.documents[b].key by {
                    assert(cache_owned(node0));
                };
                assert forall|m: int| 0 <= m < node2.documents.len() implies #[trigger] node2.documents[m].key == key
                    || exists|n: int| 0 <= n < node0.documents.len() && #[trigger] node0.documents[n] == node2.documents[m] by {
                    assert(node0.documents[m] == node2.documents[m]);
                };
                lemma_flight_closed(fleet, config, cb, ab, i, at, node2, send, ca);
            } else {
                lemma_write_after_read(fleet, config, cb, ab, i, at, node2, send, ca);
            }
        } else {
            let decided = flight.decided.unwrap();
            assert(decided == spec_encode_body(next));
            let tag = spec_etag(decided);
            assert(response == if flight.etag is Some { StoreRes::PutIfMatch { result: Ok(tag) } } else { StoreRes::PutIfNoneMatch { result: Ok(tag) } });
            assert((node2, send) == spec_commit(node0, flight, tag));
            lemma_string(spec_etag_chars(decided));
            let chars = spec_etag_chars(decided);
            assert(tag.0@ == chars);
            assert(node2.documents == spec_remember(node0.documents, key, decided, Some(chars), 0));
            assert(cache_owned(node0));
            lemma_remember(node0.documents, key, decided, Some(chars), 0);
            let entry = CachedV { key, body: decided, etag: Some(chars) };
            assert(spec_cached(node2, key) == Some(entry));
            axiom_decode_encode_body(next);
            assert(spec_read(key, decided) == next);
            assert(loaded(node2, key) == next);
            assert(applied_write(i, node0, store, key));
            assert(physical(store, key) == Some(decided));
            assert(cache_entry_ok(key, entry, store));
            assert(node2.pending == node0.pending + flight.born);
            assert(flight.born == born);
            assert(flight.reply == flight_reply(flight, reply));
            assert(flight.notify == notes);
            assert(send == reply_send(flight_reply(flight, reply)) + spec_notes(notes));
            lemma_flight_closed(fleet, config, cb, ab, i, at, node2, send, ca);
        }
    }
}

// ---------------------------------------------------------------------------
// The store
// ---------------------------------------------------------------------------

pub(crate) proof fn lemma_push_contains<A>(s: Seq<A>, x: A, y: A)
    ensures
        s.push(x).contains(y) == (s.contains(y) || y == x),
{
    let pushed = s.push(x);
    if pushed.contains(y) {
        let k = choose|k: int| 0 <= k < pushed.len() && pushed[k] == y;
        if k < s.len() {
            assert(s[k] == y);
        } else {
            assert(k == s.len());
        }
    }
    if s.contains(y) {
        let k = choose|k: int| 0 <= k < s.len() && s[k] == y;
        assert(pushed[k] == y);
    }
    if y == x {
        assert(pushed[s.len() as int] == x);
    }
}

/// The store's answer to the live flight's request: a read of an absent key,
/// or a write that lands.
pub(crate) proof fn lemma_store_answers(fleet: ConcreteConfig, world: State<CModel>, n: int)
    requires
        inv(fleet, world),
        0 <= n < fleet.nodes,
        node_at(world, n).flight is Some,
        !store_at(fleet, world).seen.contains((node_pid(n), node_at(world, n).flight.unwrap().op)),
    ensures
        ({
            let flight = node_at(world, n).flight.unwrap();
            let store = store_at(fleet, world);
            let (next, response) = spec_apply(store, request_of(flight));
            &&& response == outcome_of(flight)
            &&& entries_distinct(next)
            &&& next.seen == store.seen
            &&& if flight.writing {
                &&& physical(next, flight.key) == flight.decided
                &&& forall|other: Seq<char>| other != flight.key ==> #[trigger] physical(next, other) == physical(store, other)
            } else {
                next == store
            }
        }),
{
    let node = node_at(world, n);
    let flight = node.flight.unwrap();
    let key = flight.key;
    let store = store_at(fleet, world);
    assert(node_ok(n, node, store));
    assert(flight_ok(node));
    assert(spec_owns(node, key));
    assert(!applied_write(n, node, store, key));
    lemma_string(key);
    if !flight.writing {
        assert(spec_cached(node, key) is None);
        assert(physical(store, key) is None);
        assert(spec_find(store.entries, key, 0) is None);
        assert(request_of(flight) == StoreReq::Get { key: spec_string(key) });
    } else {
        let decided = flight.decided.unwrap();
        lemma_bytes(decided);
        match flight.etag {
            None => {
                assert(request_of(flight) == StoreReq::PutIfNoneMatch {
                    key: spec_string(key),
                    body: spec_bytes(decided),
                });
                match spec_cached(node, key) {
                    Some(c) => {
                        assert(c.etag is None);
                        assert(physical(store, key) is None);
                    },
                    None => {
                        assert(physical(store, key) is None);
                    },
                }
                assert(spec_find(store.entries, key, 0) is None);
                let entry = EntryV { key, body: decided, version: 1 };
                lemma_put(store, entry);
            },
            Some(chars) => {
                assert(request_of(flight) == StoreReq::PutIfMatch {
                    key: spec_string(key),
                    body: spec_bytes(decided),
                    etag: Etag(spec_string(chars)),
                });
                let c = spec_cached(node, key).unwrap();
                assert(c.etag == Some(chars));
                assert(physical(store, key) == Some(c.body));
                assert(chars == spec_etag_chars(c.body));
                let idx = spec_find(store.entries, key, 0).unwrap();
                assert(store.entries[idx].body == c.body);
                assert(spec_etag(c.body) == Etag(spec_string(chars)));
                assert(spec_etag(store.entries[idx].body) == Etag(spec_string(chars)));
                let entry = EntryV { key, body: decided, version: echod_concrete_spec::state::spec_bump(store.entries[idx].version) };
                let (next, response) = spec_apply(store, request_of(flight));
                assert(next == (CStore { entries: spec_put(store.entries, entry), ..store }));
                assert(response == StoreRes::PutIfMatch { result: Ok(spec_etag(decided)) });
                lemma_put(store, entry);
                assert(physical(next, key) == Some(decided));
                assert(entries_distinct(next));
            },
        }
    }
}

/// A store step.
pub(crate) proof fn lemma_store(
    fleet: ConcreteConfig,
    config: AbstractConfig,
    cb: State<CModel>,
    ab: State<AModel>,
    at: Time,
    event: ProcessEvent<CPid, CMessage>,
    j: int,
    ca: State<CModel>,
)
    requires
        related(fleet, cb, ab),
        cb.now <= at,
        event_valid(cb, CPid::Store, event),
        0 <= j < spec_store(store_at(fleet, cb), event).len(),
        ca == land(cb, fleet.nodes as int, CPid::Store, at, spec_store(store_at(fleet, cb), event)[j]),
    ensures
        matches(abstract_model(), config, ab, Seq::<BoundaryEvent>::empty(), ab),
        related(fleet, ca, ab),
{
    lemma_empty_matches(config, ab);
    lemma_extends_refl(ab.network);
    let store = store_at(fleet, cb);
    let slot = fleet.nodes as int;
    match event {
        ProcessEvent::Receive { sender, message: CMessage::StoreReq { op, request } } => {
            let wanted = Envelope { sender, recipient: CPid::Store, message: CMessage::StoreReq { op, request } };
            let k = choose|k: int| 0 <= k < cb.network.len() && #[trigger] cb.network[k] == wanted;
            assert(sender is Node);
            let n = sender->Node_0 as int;
            assert(0 <= n < fleet.nodes);
            assert(sender == node_pid(n));
            let node = node_at(cb, n);
            if store.seen.contains((sender, op)) {
                assert(spec_store(store, event) == spec_one(CProc::Store(store), Seq::empty()));
                assert(j == 0);
                assert(ca == land(cb, slot, CPid::Store, at, store_result(store, Seq::empty())));
                lemma_land_store(fleet, cb, at, store, Seq::empty());
                assert(cb.process[slot] == (CPid::Store, CProc::Store(store)));
                assert(ca.process =~= cb.process);
                assert(envelopes(CPid::Store, Seq::<(CPid, CMessage)>::empty()) =~= Seq::<Envelope<CPid, CMessage>>::empty());
                assert(ca.network =~= cb.network);
                lemma_invariant_grow(fleet, cb, ca);
                lemma_carry(fleet, cb, ab, ca, ab);
            } else {
                assert(flight_op(node) == Some(op));
                let flight = node.flight.unwrap();
                assert(flight.op == op);
                assert(request == request_of(flight));
                let key = flight.key;
                assert(node_ok(n, node, store));
                assert(flight_ok(node));
                assert(spec_owns(node, key));
                let (next, response) = spec_apply(store, request);
                let store2 = CStore { seen: store.seen.push((sender, op)), ..next };
                let send = seq![(sender, CMessage::StoreRes { op, response })];
                assert(spec_store(store, event) == spec_one(CProc::Store(store2), send));
                assert(j == 0);
                assert(ca == land(cb, slot, CPid::Store, at, store_result(store2, send)));
                lemma_land_store(fleet, cb, at, store2, send);
                lemma_store_answers(fleet, cb, n);
                assert(response == outcome_of(flight));
                assert(entries_distinct(store2));
                assert forall|other: Seq<char>| #[trigger] physical(store2, other) == physical(next, other) by {};
                assert forall|x: (CPid, u64)| #[trigger] store2.seen.contains(x) == (store.seen.contains(x) || x == (sender, op)) by {
                    lemma_push_contains(store.seen, (sender, op), x);
                };
                // every node still agrees with the store
                assert forall|m: int| 0 <= m < fleet.nodes implies #[trigger] node_ok(m, node_at(ca, m), store2) by {
                    let nm = node_at(cb, m);
                    assert(node_at(ca, m) == nm);
                    assert(node_ok(m, nm, store));
                    assert forall|key2: Seq<char>| spec_owns(nm, key2) implies (if applied_write(m, nm, store2, key2) {
                        physical(store2, key2) == nm.flight.unwrap().decided
                    } else {
                        match #[trigger] spec_cached(nm, key2) {
                            Some(c) => cache_entry_ok(key2, c, store2),
                            None => physical(store2, key2) is None,
                        }
                    }) by {
                        if m == n && key2 == key {
                            if flight.writing {
                                assert(applied_write(n, node, store2, key));
                                assert(physical(store2, key) == flight.decided);
                            } else {
                                assert(!applied_write(n, node, store2, key));
                                assert(!applied_write(n, node, store, key));
                                assert(physical(store2, key) == physical(store, key));
                            }
                        } else {
                            if m != n {
                                lemma_owner(fleet, cb, m, key2);
                                lemma_owner(fleet, cb, n, key);
                                assert(key2 != key);
                                assert(applied_write(m, nm, store2, key2) == applied_write(m, nm, store, key2));
                            } else {
                                assert(key2 != key);
                                assert(applied_write(m, nm, store2, key2) == applied_write(m, nm, store, key2));
                            }
                            assert(physical(store2, key2) == physical(store, key2));
                            match spec_cached(nm, key2) {
                                Some(c) => {
                                    assert(cache_entry_ok(key2, c, store2) == cache_entry_ok(key2, c, store));
                                },
                                None => {},
                            }
                        }
                    };
                };
                // the traffic
                lemma_envelope_at(CPid::Store, send, 0);
                let sent = envelopes(CPid::Store, send);
                assert(sent[0] == Envelope { sender: CPid::Store, recipient: sender, message: CMessage::StoreRes { op, response } });
                assert forall|m: int| 0 <= m < ca.network.len() implies match (#[trigger] ca.network[m]).message {
                    CMessage::StoreReq { op: op2, request: call2 } => {
                        let env = ca.network[m];
                        &&& env.recipient == CPid::Store
                        &&& env.sender is Node
                        &&& {
                            let q = env.sender->Node_0 as int;
                            let nq = node_at(ca, q);
                            &&& 0 <= q < fleet.nodes
                            &&& op2 < nq.next_op
                            &&& (flight_op(nq) == Some(op2) ==> call2 == request_of(nq.flight.unwrap()))
                            &&& (!store_at(fleet, ca).seen.contains((env.sender, op2)) ==> flight_op(nq) == Some(op2))
                        }
                    },
                    _ => true,
                } by {
                    if m < cb.network.len() {
                        assert(ca.network[m] == cb.network[m]);
                        match cb.network[m].message {
                            CMessage::StoreReq { op: op2, request: call2 } => {
                                let q = cb.network[m].sender->Node_0 as int;
                                assert(node_at(ca, q) == node_at(cb, q));
                                if !store2.seen.contains((cb.network[m].sender, op2)) {
                                    assert(!store.seen.contains((cb.network[m].sender, op2)));
                                }
                            },
                            _ => {},
                        }
                    } else {
                        assert(ca.network[m] == sent[0]);
                    }
                };
                assert forall|m: int| 0 <= m < ca.network.len() implies match (#[trigger] ca.network[m]).message {
                    CMessage::StoreRes { op: op2, response: outcome2 } => {
                        let env = ca.network[m];
                        &&& env.sender == CPid::Store
                        &&& env.recipient is Node
                        &&& {
                            let q = env.recipient->Node_0 as int;
                            let nq = node_at(ca, q);
                            &&& 0 <= q < fleet.nodes
                            &&& store_at(fleet, ca).seen.contains((env.recipient, op2))
                            &&& (flight_op(nq) == Some(op2) ==> outcome2 == outcome_of(nq.flight.unwrap()))
                        }
                    },
                    _ => true,
                } by {
                    if m < cb.network.len() {
                        assert(ca.network[m] == cb.network[m]);
                        match cb.network[m].message {
                            CMessage::StoreRes { op: op2, response: outcome2 } => {
                                let q = cb.network[m].recipient->Node_0 as int;
                                assert(node_at(ca, q) == node_at(cb, q));
                                assert(store.seen.contains((cb.network[m].recipient, op2)));
                            },
                            _ => {},
                        }
                    } else {
                        assert(ca.network[m] == sent[0]);
                        assert(store2.seen.contains((sender, op)));
                        assert(node_at(ca, n) == node);
                    }
                };
                assert forall|pair: (CPid, u64)| #[trigger] store2.seen.contains(pair) implies requested(ca, pair.0, pair.1) by {
                    if store.seen.contains(pair) {
                        lemma_requested_grows(cb, ca, pair.0, pair.1);
                    } else {
                        assert(pair == (sender, op));
                        assert(ca.network[k] == wanted);
                    }
                };
                assert(inv(fleet, ca));
                // the rest reads the nodes, which did not move
                assert forall|key2: Seq<char>| #[trigger] doc_rel(key2, effective(fleet, ca, key2), astate(ab).store) by {
                    assert(effective(fleet, ca, key2) == effective(fleet, cb, key2));
                };
                assert forall|item: Sched<InternalV>| #[trigger] owed(fleet, ca, item, 0) <= astate(ab).pending.to_multiset().count(item) by {
                    lemma_owed_same(fleet, cb, ca, item, 0);
                };
                assert forall|m: int| 0 <= m < fleet.nodes implies flight_outputs_covered(#[trigger] node_at(ca, m), ab.network) by {
                    assert(node_at(ca, m) == node_at(cb, m));
                };
                assert forall|m: int|
                    #![trigger sent[m]]
                    0 <= m < sent.len() implies carried_request(sent[m], ab.network) && carried_output(sent[m], ab.network) by {
                    assert(m == 0);
                };
                lemma_append_keeps_coverage(cb.network, sent, ab.network, ab.network);
                assert(coupled(ca, ab));
                assert(related(fleet, ca, ab));
            }
        },
        _ => {
            assert(spec_store(store, event).len() == 0);
            assert(false);
        },
    }
}

// ---------------------------------------------------------------------------
// A node step
// ---------------------------------------------------------------------------

pub(crate) proof fn lemma_node(
    fleet: ConcreteConfig,
    config: AbstractConfig,
    cb: State<CModel>,
    ab: State<AModel>,
    i: int,
    at: Time,
    event: ProcessEvent<CPid, CMessage>,
    j: int,
    ca: State<CModel>,
) -> (aa: State<AModel>)
    requires
        config == abstract_config(fleet),
        agreement(config),
        related(fleet, cb, ab),
        0 <= i < fleet.nodes,
        cb.now <= at,
        event_valid(cb, node_pid(i), event),
        0 <= j < spec_node_step(node_at(cb, i), at, event).len(),
        ca == land(cb, i, node_pid(i), at, spec_node_step(node_at(cb, i), at, event)[j]),
    ensures
        matches(abstract_model(), config, ab, Seq::<BoundaryEvent>::empty(), aa),
        related(fleet, ca, aa),
{
    let node = node_at(cb, i);
    let results = spec_node_step(node, at, event);
    match event {
        ProcessEvent::Timeout => {
            match node.wake {
                Some(w) => {
                    if w <= at as nat && node.flight is None && node.next_op < u64::MAX {
                        let (next, send) = spec_timeout(node, at);
                        let node2 = NodeV {
                            logic: echod_concrete_spec::rover::LogicV { clock: at as nat, last_wake: None, ..node.logic },
                            wake: echod_concrete_spec::state::spec_wake(next),
                            ..next
                        };
                        assert(results == spec_one(CProc::Node(node2), send));
                        assert(j == 0);
                        assert(results[0] == node_result(node2, send));
                        let cw = land(cb, i, node_pid(i), at, node_result(next, send));
                        let aa = lemma_timeout(fleet, config, cb, ab, i, at, next, send, cw);
                        lemma_reshell(fleet, config, cb, aa, i, at, next, node2, send, ca);
                        aa
                    } else if w <= at as nat {
                        assert(results == spec_one(CProc::Node(node), Seq::empty()));
                        assert(j == 0);
                        assert(results[0] == node_result(node, Seq::empty()));
                        lemma_same_work(fleet, config, cb, ab, i, at, node, ca);
                        ab
                    } else {
                        assert(results.len() == 0);
                        assert(false);
                        ab
                    }
                },
                None => {
                    assert(results.len() == 0);
                    assert(false);
                    ab
                },
            }
        },
        ProcessEvent::Receive { sender: CPid::Outside, message: CMessage::Request(request) } => {
            if node.flight is Some || node.next_op == u64::MAX {
                assert(results == spec_one(CProc::Node(node), Seq::empty()));
                assert(j == 0);
                assert(results[0] == node_result(node, Seq::empty()));
                lemma_same_work(fleet, config, cb, ab, i, at, node, ca);
                ab
            } else {
                let (next, send) = spec_request(node, at, request);
                let node2 = NodeV {
                    logic: echod_concrete_spec::rover::spec_clock(node.logic, at),
                    next_request: (node.next_request + 1) as u64,
                    wake: echod_concrete_spec::state::spec_wake(next),
                    ..next
                };
                assert(results == spec_one(CProc::Node(node2), send));
                assert(j == 0);
                assert(results[0] == node_result(node2, send));
                let cw = land(cb, i, node_pid(i), at, node_result(next, send));
                let aa = lemma_request(fleet, config, cb, ab, i, at, request, next, send, cw);
                lemma_reshell(fleet, config, cb, aa, i, at, next, node2, send, ca);
                aa
            }
        },
        ProcessEvent::Receive { sender: CPid::Store, message: CMessage::StoreRes { op, response } } => {
            if node.flight is None || node.next_op == u64::MAX {
                assert(results == spec_one(CProc::Node(node), Seq::empty()));
                assert(j == 0);
                assert(results[0] == node_result(node, Seq::empty()));
                lemma_same_work(fleet, config, cb, ab, i, at, node, ca);
                ab
            } else {
                let (next, send) = spec_store_reply(node, op, response);
                let node2 = NodeV {
                    logic: echod_concrete_spec::rover::spec_clock(node.logic, at),
                    wake: echod_concrete_spec::state::spec_wake(next),
                    ..next
                };
                assert(results == spec_one(CProc::Node(node2), send));
                assert(j == 0);
                assert(results[0] == node_result(node2, send));
                let cw = land(cb, i, node_pid(i), at, node_result(next, send));
                lemma_store_reply(fleet, config, cb, ab, i, at, op, response, next, send, cw);
                lemma_reshell(fleet, config, cb, ab, i, at, next, node2, send, ca);
                ab
            }
        },
        ProcessEvent::Receive { sender: CPid::Outside, message: CMessage::Stop } => {
            let node2 = NodeV {
                logic: echod_concrete_spec::rover::LogicV { clock: at as nat, loops: false, stopping: true, ..node.logic },
                ..node
            };
            assert(results == spec_one(CProc::Node(node2), Seq::empty()));
            assert(j == 0);
            assert(results[0] == node_result(node2, Seq::empty()));
            lemma_same_work(fleet, config, cb, ab, i, at, node2, ca);
            ab
        },
        _ => {
            assert(results.len() == 0);
            assert(false);
            ab
        },
    }
}

// ---------------------------------------------------------------------------
// The three labels
// ---------------------------------------------------------------------------

pub(crate) proof fn lemma_input(
    fleet: ConcreteConfig,
    config: AbstractConfig,
    cb: State<CModel>,
    ab: State<AModel>,
    recipient: CPid,
    at: Time,
    message: CMessage,
    ca: State<CModel>,
) -> (aa: State<AModel>)
    requires
        related(fleet, cb, ab),
        cb.step(concrete_model(), fleet, Label::Input { recipient, at, message }, ca),
    ensures
        matches(abstract_model(), config, ab, concrete_model().observe(Label::Input { recipient, at, message }), aa),
        related(fleet, ca, aa),
{
    reveal(State::step);
    let label = Label::<CPid, CMessage>::Input { recipient, at, message };
    assert(cb.now <= at);
    assert(concrete_model().injectable(fleet, message));
    assert(ca == inject(cb, CPid::Outside, recipient, at, message));
    let added = Envelope { sender: CPid::Outside, recipient, message };
    assert(ca.process == cb.process);
    assert(ca.network == cb.network.push(added));
    assert(ca.now == at);
    lemma_extends_push(cb.network, added);
    assert forall|k: int| cb.network.len() <= k < ca.network.len() implies no_store_traffic(#[trigger] ca.network[k]) by {
        assert(ca.network[k] == added);
    };
    lemma_invariant_grow(fleet, cb, ca);
    match message {
        CMessage::Request(request) => {
            let amessage = AMessage::Request(request);
            let alabel = Label::<APid, AMessage>::Input { recipient: APid::Service, at, message: amessage };
            let aa = inject(ab, APid::Outside, APid::Service, at, amessage);
            lemma_single_present(ab);
            assert(abstract_model().injectable(config, amessage));
            assert(ab.step(abstract_model(), config, alabel, aa));
            let visible = seq![BoundaryEvent::Input { at, call: request }];
            assert(abstract_model().observe(alabel) =~= visible);
            assert(concrete_model().observe(label) =~= visible);
            lemma_matched_step(config, ab, alabel, aa, visible);
            lemma_matches_same_visible(config, ab, visible, concrete_model().observe(label), aa);
            let aenv = Envelope { sender: APid::Outside, recipient: APid::Service, message: amessage };
            assert(aa.network == ab.network.push(aenv));
            lemma_extends_push(ab.network, aenv);
            lemma_pushed_request(ab.network, request);
            assert(carried_request(added, aa.network));
            assert(carried_output(added, aa.network));
            lemma_push_keeps_coverage(cb.network, added, ab.network, aa.network);
            assert(aa.process == ab.process);
            lemma_carry(fleet, cb, ab, ca, aa);
            aa
        },
        _ => {
            lemma_empty_matches(config, ab);
            assert(concrete_model().observe(label) =~= Seq::<BoundaryEvent>::empty());
            lemma_matches_same_visible(config, ab, Seq::<BoundaryEvent>::empty(), concrete_model().observe(label), ab);
            lemma_extends_refl(ab.network);
            assert(carried_request(added, ab.network));
            assert(carried_output(added, ab.network));
            lemma_push_keeps_coverage(cb.network, added, ab.network, ab.network);
            lemma_carry(fleet, cb, ab, ca, ab);
            ab
        },
    }
}

pub(crate) proof fn lemma_outside(
    fleet: ConcreteConfig,
    config: AbstractConfig,
    cb: State<CModel>,
    ab: State<AModel>,
    sender: CPid,
    at: Time,
    message: CMessage,
    ca: State<CModel>,
) -> (aa: State<AModel>)
    requires
        related(fleet, cb, ab),
        cb.step(concrete_model(), fleet, Label::Outside { sender, at, message }, ca),
    ensures
        matches(abstract_model(), config, ab, concrete_model().observe(Label::Outside { sender, at, message }), aa),
        related(fleet, ca, aa),
{
    reveal(State::step);
    let label = Label::<CPid, CMessage>::Outside { sender, at, message };
    assert(cb.now <= at);
    assert(ca == observe_outside(cb, at));
    assert(ca.process == cb.process);
    assert(ca.network == cb.network);
    assert(ca.now == at);
    lemma_extends_refl(cb.network);
    lemma_invariant_grow(fleet, cb, ca);
    let wanted = Envelope { sender, recipient: CPid::Outside, message };
    let k = choose|k: int| 0 <= k < cb.network.len() && #[trigger] cb.network[k] == wanted;
    match message {
        CMessage::Output(output) => {
            assert(carried_output(cb.network[k], ab.network));
            assert(service_output(ab.network, output));
            let m = choose|m: int|
                #![trigger ab.network[m]]
                0 <= m < ab.network.len() && ab.network[m] == Envelope {
                    sender: APid::Service,
                    recipient: APid::Outside,
                    message: AMessage::Output(output),
                };
            let alabel = Label::<APid, AMessage>::Outside { sender: APid::Service, at, message: AMessage::Output(output) };
            let aa = observe_outside(ab, at);
            assert(ab.step(abstract_model(), config, alabel, aa));
            let visible = seq![BoundaryEvent::Output { at, output }];
            assert(abstract_model().observe(alabel) =~= visible);
            assert(concrete_model().observe(label) =~= visible);
            lemma_matched_step(config, ab, alabel, aa, visible);
            lemma_matches_same_visible(config, ab, visible, concrete_model().observe(label), aa);
            assert(aa.process == ab.process);
            assert(aa.network == ab.network);
            lemma_extends_refl(ab.network);
            lemma_carry(fleet, cb, ab, ca, aa);
            aa
        },
        _ => {
            lemma_empty_matches(config, ab);
            assert(concrete_model().observe(label) =~= Seq::<BoundaryEvent>::empty());
            lemma_matches_same_visible(config, ab, Seq::<BoundaryEvent>::empty(), concrete_model().observe(label), ab);
            lemma_extends_refl(ab.network);
            lemma_carry(fleet, cb, ab, ca, ab);
            ab
        },
    }
}

pub(crate) proof fn lemma_process(
    fleet: ConcreteConfig,
    config: AbstractConfig,
    cb: State<CModel>,
    ab: State<AModel>,
    process: CPid,
    at: Time,
    event: ProcessEvent<CPid, CMessage>,
    send: Seq<(CPid, CMessage)>,
    ca: State<CModel>,
) -> (aa: State<AModel>)
    requires
        config == abstract_config(fleet),
        agreement(config),
        related(fleet, cb, ab),
        cb.step(concrete_model(), fleet, Label::Process { process, at, event, send }, ca),
    ensures
        matches(abstract_model(), config, ab, concrete_model().observe(Label::Process { process, at, event, send }), aa),
        related(fleet, ca, aa),
{
    reveal(State::step);
    let label = Label::<CPid, CMessage>::Process { process, at, event, send };
    assert(cb.now <= at);
    assert(event_valid(cb, process, event));
    let i = choose|i: int|
        #![trigger cb.process[i]]
        exists|j: int|
            #![trigger cb.process[i].1.on_event(fleet, at, event)[j]]
            {
                &&& 0 <= i < cb.process.len()
                &&& cb.process[i].0 == process
                &&& {
                    let outcomes = cb.process[i].1.on_event(fleet, at, event);
                    &&& 0 <= j < outcomes.len()
                    &&& outcomes[j].send == send
                    &&& ca == land(cb, i, process, at, outcomes[j])
                }
            };
    let j = choose|j: int|
        #![trigger cb.process[i].1.on_event(fleet, at, event)[j]]
        {
            &&& 0 <= i < cb.process.len()
            &&& cb.process[i].0 == process
            &&& {
                let outcomes = cb.process[i].1.on_event(fleet, at, event);
                &&& 0 <= j < outcomes.len()
                &&& outcomes[j].send == send
                &&& ca == land(cb, i, process, at, outcomes[j])
            }
        };
    let outcomes = cb.process[i].1.on_event(fleet, at, event);
    assert(concrete_model().observe(label) =~= Seq::<BoundaryEvent>::empty());
    assert(shaped(fleet, cb));
    if i < fleet.nodes {
        assert(process == node_pid(i));
        let node = node_at(cb, i);
        assert(cb.process[i].1 == CProc::Node(node));
        assert(outcomes == spec_node_step(node, at, event));
        let aa = lemma_node(fleet, config, cb, ab, i, at, event, j, ca);
        lemma_matches_same_visible(config, ab, Seq::<BoundaryEvent>::empty(), concrete_model().observe(label), aa);
        aa
    } else {
        assert(i == fleet.nodes);
        assert(process == CPid::Store);
        let store = store_at(fleet, cb);
        assert(cb.process[i].1 == CProc::Store(store));
        assert(outcomes == spec_store(store, event));
        lemma_store(fleet, config, cb, ab, at, event, j, ca);
        lemma_matches_same_visible(config, ab, Seq::<BoundaryEvent>::empty(), concrete_model().observe(label), ab);
        ab
    }
}

/// One concrete step, matched.
pub(crate) proof fn lemma_step(
    fleet: ConcreteConfig,
    config: AbstractConfig,
    cb: State<CModel>,
    label: Label<CPid, CMessage>,
    ca: State<CModel>,
    ab: State<AModel>,
) -> (aa: State<AModel>)
    requires
        config == abstract_config(fleet),
        agreement(config),
        related(fleet, cb, ab),
        cb.step(concrete_model(), fleet, label, ca),
    ensures
        matches(abstract_model(), config, ab, concrete_model().observe(label), aa),
        related(fleet, ca, aa),
{
    match label {
        Label::Input { recipient, at, message } => lemma_input(fleet, config, cb, ab, recipient, at, message, ca),
        Label::Process { process, at, event, send } => lemma_process(
            fleet,
            config,
            cb,
            ab,
            process,
            at,
            event,
            send,
            ca,
        ),
        Label::Outside { sender, at, message } => lemma_outside(fleet, config, cb, ab, sender, at, message, ca),
        Label::Clock { .. } => {
            reveal(State::step);
            assert(ca.process == cb.process);
            assert(ca.network == cb.network);
            lemma_empty_matches(config, ab);
            assert(concrete_model().observe(label) =~= Seq::<BoundaryEvent>::empty());
            lemma_matches_same_visible(
                config,
                ab,
                Seq::<BoundaryEvent>::empty(),
                concrete_model().observe(label),
                ab,
            );
            lemma_extends_refl(ab.network);
            lemma_extends_refl(cb.network);
            lemma_invariant_grow(fleet, cb, ca);
            lemma_carry(fleet, cb, ab, ca, ab);
            ab
        },
    }
}

// ---------------------------------------------------------------------------
// The initial worlds
// ---------------------------------------------------------------------------

pub(crate) proof fn lemma_owed_zero(fleet: ConcreteConfig, world: State<CModel>, item: Sched<InternalV>, k: int)
    requires
        forall|i: int| 0 <= i < fleet.nodes ==> #[trigger] occurrences(node_at(world, i)).len() == 0,
    ensures
        owed(fleet, world, item, k) == 0,
    decreases fleet.nodes - k,
{
    if k < 0 || k >= fleet.nodes {
    } else {
        lemma_owed_zero(fleet, world, item, k + 1);
        assert(items(occurrences(node_at(world, k))) =~= Seq::<Sched<InternalV>>::empty());
        assert(Seq::<Sched<InternalV>>::empty().to_multiset() =~= Multiset::<Sched<InternalV>>::empty());
    }
}

/// The empty document reads as the empty store under every key.
pub(crate) proof fn lemma_empty_reads(key: Seq<char>)
    ensures
        doc_rel(key, spec_empty_body(key), empty_store()),
{
    let s = empty_store();
    if echod_concrete_spec::state::spec_starts(key, seq!['s', '/']) {
        assert(spec_empty_body(key) == DocumentBodyV::Schedule(None::<echod_types::Schedule>));
        assert(!s.schedules.contains_key(key.skip(2)));
    } else {
        let map = Map::<Seq<char>, echod_concrete_spec::state::ObjV>::empty();
        assert(spec_empty_body(key) == DocumentBodyV::Workflow(map));
        assert(map.dom() =~= Set::<Seq<char>>::empty());
        assert(Set::<Seq<char>>::empty().len() == 0);
        if echod_concrete_spec::state::spec_starts(key, super::interpretation::origin_prefix()) {
            let o = key.skip(2);
            assert forall|id: Seq<char>| #![trigger origin(id)] origin(id) == o implies {
                &&& s.promises.contains_key(id) == map.contains_key(id)
                &&& (map.contains_key(id) ==> super::interpretation::object_rel(
                    map[id],
                    s.promises[id],
                    super::interpretation::abstract_task(s, id),
                ))
                &&& (!map.contains_key(id) ==> !s.tasks.contains_key(id))
            } by {
                assert(!s.promises.contains_key(id));
                assert(!s.tasks.contains_key(id));
                assert(!map.contains_key(id));
            };
        }
    }
}

pub(crate) proof fn lemma_initial(fleet: ConcreteConfig, config: AbstractConfig)
    ensures
        related(
            fleet,
            State::<CModel>::init(concrete_model(), fleet),
            State::<AModel>::init(abstract_model(), config),
        ),
{
    let cw = State::<CModel>::init(concrete_model(), fleet);
    let aw = State::<AModel>::init(abstract_model(), config);
    assert(cw.process == spec_world(fleet));
    assert(cw.network =~= Seq::<Envelope<CPid, CMessage>>::empty());
    assert(cw.now == 0);
    assert(aw.process == seq![(APid::Service, AProc { store: empty_store(), pending: Seq::empty() })]);
    assert(aw.network =~= Seq::<Envelope<APid, AMessage>>::empty());
    assert(single(aw));
    assert(astate(aw) == AProc { store: empty_store(), pending: Seq::empty() });
    assert(empty_store().promises.dom() =~= Set::<Seq<char>>::empty());
    assert(empty_store().tasks.dom() =~= Set::<Seq<char>>::empty());
    assert(empty_store().schedules.dom() =~= Set::<Seq<char>>::empty());
    assert(finite_store(empty_store()));
    // shape
    lemma_spec_nodes(fleet, 0);
    let nodes = spec_nodes(fleet, 0);
    let store = CStore { entries: Seq::empty(), appendable: fleet.appendable, seen: Seq::empty() };
    let tail = seq![(CPid::Store, CProc::Store(store))];
    assert(cw.process == nodes + tail);
    assert(cw.process.len() == fleet.nodes + 1);
    assert forall|i: int| 0 <= i < fleet.nodes implies #[trigger] cw.process[i] == (
        node_pid(i),
        CProc::Node(initial_node(fleet, i as u64)),
    ) by {
        assert(cw.process[i] == nodes[i]);
    };
    assert(cw.process[fleet.nodes as int] == tail[0]);
    assert(shaped(fleet, cw));
    assert(store_at(fleet, cw) == store);
    // the facts
    assert(entries_distinct(store));
    assert forall|i: int| 0 <= i < fleet.nodes implies #[trigger] node_ok(i, node_at(cw, i), store) by {
        let node = node_at(cw, i);
        assert(node == initial_node(fleet, i as u64));
        assert(node.flight is None);
        assert(node.documents.len() == 0);
        assert(cache_owned(node));
        assert forall|key: Seq<char>| spec_owns(node, key) implies (if applied_write(i, node, store, key) {
            physical(store, key) == node.flight.unwrap().decided
        } else {
            match #[trigger] spec_cached(node, key) {
                Some(c) => cache_entry_ok(key, c, store),
                None => physical(store, key) is None,
            }
        }) by {
            assert(spec_cached(node, key) is None);
            assert(physical(store, key) is None);
        };
    };
    assert(requests_ok(fleet, cw));
    assert(replies_ok(fleet, cw));
    assert forall|pair: (CPid, u64)| #[trigger] store.seen.contains(pair) implies requested(cw, pair.0, pair.1) by {
        assert(false);
    };
    assert(inv(fleet, cw));
    // the store, read through the nodes
    assert forall|key: Seq<char>| #[trigger] doc_rel(key, effective(fleet, cw, key), empty_store()) by {
        if fleet.nodes == 0 {
        } else {
            let o = owner(fleet, key);
            let node = node_at(cw, o);
            assert(node.flight is None);
            assert(spec_cached(node, key) is None);
            assert(effective(fleet, cw, key) == spec_empty_body(key));
        }
        lemma_empty_reads(key);
    };
    // nothing owed
    assert forall|i: int| 0 <= i < fleet.nodes implies #[trigger] occurrences(node_at(cw, i)).len() == 0 by {
        let node = node_at(cw, i);
        assert(born_of(node) =~= Seq::<PendingV>::empty());
        assert(occurrences(node) =~= Seq::<PendingV>::empty());
    };
    assert forall|item: Sched<InternalV>| #[trigger] owed(fleet, cw, item, 0) <= astate(aw).pending.to_multiset().count(item) by {
        lemma_owed_zero(fleet, cw, item, 0);
    };
    assert forall|i: int| 0 <= i < fleet.nodes implies flight_outputs_covered(#[trigger] node_at(cw, i), aw.network) by {
        assert(node_at(cw, i).flight is None);
    };
    assert(requests_covered(cw.network, aw.network));
    assert(outputs_covered(cw.network, aw.network));
    assert(coupled(cw, aw));
    assert(related(fleet, cw, aw));
}

/// A timeout at an idle node.
pub(crate) proof fn lemma_timeout(
    fleet: ConcreteConfig,
    config: AbstractConfig,
    cb: State<CModel>,
    ab: State<AModel>,
    i: int,
    at: Time,
    node2: NodeV,
    send: Seq<(CPid, CMessage)>,
    ca: State<CModel>,
) -> (aa: State<AModel>)
    requires
        config == abstract_config(fleet),
        agreement(config),
        related(fleet, cb, ab),
        0 <= i < fleet.nodes,
        cb.now <= at,
        node_at(cb, i).flight is None,
        node_at(cb, i).next_op < u64::MAX,
        (node2, send) == spec_timeout(node_at(cb, i), at),
        ca == land(cb, i, node_pid(i), at, node_result(node2, send)),
    ensures
        matches(abstract_model(), config, ab, Seq::<BoundaryEvent>::empty(), aa),
        related(fleet, ca, aa),
{
    let node0 = node_at(cb, i);
    if node0.pending.len() > 0 {
        let p = node0.pending[0];
        let node1 = NodeV { pending: node0.pending.skip(1), ..node0 };
        let key = echod_concrete_spec::state::spec_origin_key(origin(p.promise));
        if !spec_owns(node1, key) {
            assert(node2 == node1);
            assert(send =~= Seq::<(CPid, CMessage)>::empty());
            lemma_pop_silent(fleet, config, cb, ab, i, at, node2, ca);
            ab
        } else {
            lemma_occurrence_begin(fleet, config, cb, ab, i, at, node2, send, ca)
        }
    } else {
        match spec_earliest_key(node0, at) {
            Some(key) => lemma_due_begin(fleet, config, cb, ab, i, at, key, node2, send, ca),
            None => {
                assert(node2 == node0);
                assert(send =~= Seq::<(CPid, CMessage)>::empty());
                lemma_same_work(fleet, config, cb, ab, i, at, node2, ca);
                ab
            },
        }
    }
}

// ---------------------------------------------------------------------------
// The theorem
// ---------------------------------------------------------------------------

/// Every concrete step is matched: the forward simulation.
pub(crate) proof fn lemma_simulation(fleet: ConcreteConfig, config: AbstractConfig)
    requires
        config == abstract_config(fleet),
        agreement(config),
    ensures
        simulation(concrete_model(), fleet, abstract_model(), config, link(fleet)),
{
    let relation = link(fleet);
    assert forall|cb: State<CModel>, label: Label<CPid, CMessage>, ca: State<CModel>, ab: State<AModel>|
        #![trigger relation(cb, ab), cb.step(concrete_model(), fleet, label, ca)]
        relation(cb, ab) && cb.step(concrete_model(), fleet, label, ca) implies exists|aa: State<AModel>|
            #[trigger] matches(abstract_model(), config, ab, concrete_model().observe(label), aa) && relation(ca, aa) by {
        lemma_link(fleet, cb, ab);
        let aa = lemma_step(fleet, config, cb, label, ca, ab);
        lemma_link(fleet, ca, aa);
        assert(matches(abstract_model(), config, ab, concrete_model().observe(label), aa) && relation(ca, aa));
    };
}

/// Trace inclusion: every boundary trace of the concrete world is one of
/// the abstract world, at the abstract configuration the fleet implements:
/// the same retry timeout. The handlers, the due step, and the occurrence
/// agree by `work::lemma_agreement`.
pub(crate) proof fn prove_refinement(concrete_config: ConcreteConfig)
    ensures
        crate::concrete_refines_abstract(concrete_config),
{
    let fleet = concrete_config;
    let config = abstract_config(fleet);
    super::work::lemma_agreement(config);
    lemma_initial(fleet, config);
    lemma_link(
        fleet,
        State::<CModel>::init(concrete_model(), fleet),
        State::<AModel>::init(abstract_model(), config),
    );
    lemma_simulation(fleet, config);
    concrete_refines_abstract(concrete_model(), fleet, abstract_model(), config, link(fleet));
}

} // verus!

}

verus! {

/// Proves the complete concrete-to-abstract trace-refinement claim.
pub proof fn refinement_proof(concrete_config: ConcreteConfig)
    ensures
        crate::concrete_refines_abstract(concrete_config),
{
    simulation::prove_refinement(concrete_config);
}

} // verus!

mod effects_proof {
//! Local correspondence between imperative notifications and document effects.

use vstd::prelude::*;

use echod_types::{PromiseRecord, Request};

#[cfg(verus_keep_ghost)]
use echod_concrete_spec::document::{
    document_effects, well_formed, workflow_effects, ObjV, PromiseEffectV, ProtocolEffectKeyV,
    ProtocolEffectV, StoredDocumentV,
};
#[cfg(verus_keep_ghost)]
use echod_concrete_spec::state::{
    spec_committed_notes, spec_execute_notes, spec_keyed_notes, spec_note_key,
    spec_request_commits, spec_request_transition, spec_sorted_present, spec_stored_body,
    spec_stored_committed_at, spec_unavailable, spec_unblock_notes, spec_unblock_notes_for,
    DocumentBodyV, NoteV,
};
#[cfg(verus_keep_ghost)]
use echod_concrete_spec::request_claim::{on_request, routed};


use echod_concrete_spec::effects_claim::*;

use super::requests::*;
verus! {


proof fn lemma_note_keys_agree(left: NoteV, right: NoteV)
    ensures
        spec_note_key(left) == spec_note_key(right)
            <==> echod_concrete_spec::document::protocol_effect_key(note_effect(left))
                == echod_concrete_spec::document::protocol_effect_key(note_effect(right)),
{
}


/// Keyed-note filtering both removes duplicates and preserves that property
/// while discarding Executes consumed by the same atomic request.
pub proof fn lemma_keyed_notes_no_duplicate_effect_keys(
    doc: DocumentBodyV,
    notes: Seq<NoteV>,
    count: nat,
)
    requires
        count <= notes.len(),
    ensures
        note_effect_keys(spec_keyed_notes(doc, notes, count)).no_duplicates(),
    decreases count,
{
    if count > 0 {
        let prior = spec_keyed_notes(doc, notes, (count - 1) as nat);
        let note = notes[count as int - 1];
        lemma_keyed_notes_no_duplicate_effect_keys(
            doc,
            notes,
            (count - 1) as nat,
        );
        if echod_concrete_spec::state::spec_note_relevant(doc, note)
            && !(exists|i: int| 0 <= i < prior.len()
                && spec_note_key(prior[i]) == spec_note_key(note))
        {
            assert forall|i: int| 0 <= i < prior.len() implies
                echod_concrete_spec::document::protocol_effect_key(note_effect(prior[i]))
                    != echod_concrete_spec::document::protocol_effect_key(note_effect(note)) by {
                lemma_note_keys_agree(prior[i], note);
            }
            assert(note_effect_keys(prior.push(note))
                == note_effect_keys(prior).push(
                    echod_concrete_spec::document::protocol_effect_key(note_effect(note)),
                ));
        }
    }
}


proof fn lemma_note_effects_add(first: Seq<NoteV>, second: Seq<NoteV>)
    ensures
        forall|effect: ProtocolEffectV|
            note_effects(first + second).contains(effect)
                <==> note_effects(first).contains(effect)
                    || note_effects(second).contains(effect),
{
    assert forall|effect: ProtocolEffectV|
        note_effects(first + second).contains(effect)
            <==> note_effects(first).contains(effect)
                || note_effects(second).contains(effect) by {
        if note_effects(first + second).contains(effect) {
            let i = choose|i: int| 0 <= i < (first + second).len()
                && note_effect((first + second)[i]) == effect;
            if i < first.len() {
                assert((first + second)[i] == first[i]);
                assert(note_effects(first).contains(effect));
            } else {
                assert((first + second)[i] == second[i - first.len()]);
                assert(note_effects(second).contains(effect));
            }
        }
        if note_effects(first).contains(effect) {
            let i = choose|i: int| 0 <= i < first.len()
                && note_effect(first[i]) == effect;
            assert((first + second)[i] == first[i]);
            assert(note_effects(first + second).contains(effect));
        }
        if note_effects(second).contains(effect) {
            let i = choose|i: int| 0 <= i < second.len()
                && note_effect(second[i]) == effect;
            assert((first + second)[first.len() + i] == second[i]);
            assert(note_effects(first + second).contains(effect));
        }
    };
}


proof fn lemma_note_effects_push(notes: Seq<NoteV>, note: NoteV)
    ensures
        forall|effect: ProtocolEffectV|
            note_effects(notes.push(note)).contains(effect)
                <==> note_effects(notes).contains(effect)
                    || effect == note_effect(note),
{
    lemma_note_effects_add(notes, seq![note]);
    assert(notes.push(note) =~= notes + seq![note]);
    assert forall|effect: ProtocolEffectV|
        note_effects(seq![note]).contains(effect)
            <==> effect == note_effect(note) by {
        if note_effects(seq![note]).contains(effect) {
            let i = choose|i: int| 0 <= i < 1
                && note_effect(seq![note][i]) == effect;
            assert(i == 0);
        }
        if effect == note_effect(note) {
            assert(seq![note][0] == note);
            assert(0 <= 0 < seq![note].len());
            assert(note_effects(seq![note]).contains(effect));
        }
    };
}


proof fn lemma_nodup_last_not_in_prefix<A>(values: Seq<A>, count: nat)
    requires
        0 < count <= values.len(),
        values.take(count as int).no_duplicates(),
    ensures
        !values.take(count as int - 1).contains(values[count as int - 1]),
{
    if values.take(count as int - 1).contains(values[count as int - 1]) {
        let i = choose|i: int| 0 <= i < values.take(count as int - 1).len()
            && #[trigger] values.take(count as int - 1)[i]
                == values[count as int - 1];
        assert(values.take(count as int)[i]
            == values.take(count as int)[count as int - 1]);
        assert(i != count as int - 1);
    }
}


proof fn lemma_execute_notes(
    before: Map<Seq<char>, ObjV>,
    after: Map<Seq<char>, ObjV>,
    committed_at: u64,
    keys: Seq<Seq<char>>,
    count: nat,
)
    requires
        count <= keys.len(),
        keys.take(count as int).no_duplicates(),
        forall|i: int| 0 <= i < count ==> after.contains_key(#[trigger] keys[i]),
    ensures
        ({
            let notes = spec_execute_notes(before, after, committed_at, keys, count);
            &&& forall|effect: ProtocolEffectV|
                note_effects(notes).contains(effect) <==> match effect {
                    ProtocolEffectV::Execute { id, version } =>
                        keys.take(count as int).contains(id)
                            && echod_concrete_spec::document::offer_committed(
                                before,
                                after,
                                id,
                                committed_at,
                            )
                            && after[id].task.unwrap().version == version,
                    ProtocolEffectV::Unblock { .. } => false,
                }
            &&& note_effect_keys(notes).no_duplicates()
        }),
    decreases count,
{
    if count > 0 {
        let prior = spec_execute_notes(
            before,
            after,
            committed_at,
            keys,
            (count - 1) as nat,
        );
        let id = keys[count as int - 1];
        lemma_execute_notes(before, after, committed_at, keys, (count - 1) as nat);
        lemma_nodup_last_not_in_prefix(keys, count);
        assert(keys.take(count as int)
            == keys.take(count as int - 1).push(id));
        if echod_concrete_spec::document::offer_committed(before, after, id, committed_at) {
            let note = NoteV::Execute {
                id,
                version: after[id].task.unwrap().version,
            };
            lemma_note_effects_push(prior, note);
            lemma_note_effects_add(prior, seq![note]);
            assert(prior + seq![note] =~= prior.push(note));
            assert(spec_execute_notes(before, after, committed_at, keys, count)
                == prior.push(note));
            assert(note_effect_keys(prior.push(note))
                == note_effect_keys(prior).push(
                    ProtocolEffectKeyV::Execute { id },
                ));
            assert(!note_effect_keys(prior).contains(
                ProtocolEffectKeyV::Execute { id },
            )) by {
                if note_effect_keys(prior).contains(
                    ProtocolEffectKeyV::Execute { id },
                ) {
                    let i = choose|i: int| 0 <= i < prior.len()
                        && note_effect_keys(prior)[i]
                            == ProtocolEffectKeyV::Execute { id };
                    assert(note_effect_keys(prior)[i]
                        == echod_concrete_spec::document::protocol_effect_key(note_effect(prior[i])));
                    assert(note_effects(prior).contains(note_effect(prior[i])));
                    match note_effect(prior[i]) {
                        ProtocolEffectV::Execute { id: prior_id, .. } => {
                            assert(prior_id == id);
                            assert(keys.take(count as int - 1).contains(prior_id));
                        },
                        ProtocolEffectV::Unblock { .. } => {
                            assert(false);
                        },
                    }
                }
            };
        } else {
            assert(spec_execute_notes(before, after, committed_at, keys, count)
                == prior);
        }
        assert forall|candidate: Seq<char>|
            keys.take(count as int).contains(candidate)
                <==> keys.take(count as int - 1).contains(candidate)
                    || candidate == id by {
            super::simulation::lemma_push_contains(
                keys.take(count as int - 1),
                id,
                candidate,
            );
            if keys.take(count as int).contains(candidate) {
                let i = choose|i: int| 0 <= i < keys.take(count as int).len()
                    && keys.take(count as int)[i] == candidate;
                if i < count as int - 1 {
                    assert(keys.take(count as int - 1)[i] == candidate);
                } else {
                    assert(i == count as int - 1);
                }
            }
            if keys.take(count as int - 1).contains(candidate) {
                let i = choose|i: int| 0 <= i < keys.take(count as int - 1).len()
                    && #[trigger] keys.take(count as int - 1)[i] == candidate;
                assert(keys.take(count as int)[i] == candidate);
            }
        };
        assert forall|effect: ProtocolEffectV|
            note_effects(spec_execute_notes(before, after, committed_at, keys, count))
                .contains(effect) <==> match effect {
                ProtocolEffectV::Execute { id, version } =>
                    keys.take(count as int).contains(id)
                        && echod_concrete_spec::document::offer_committed(
                            before,
                            after,
                            id,
                            committed_at,
                        )
                        && after[id].task.unwrap().version == version,
                ProtocolEffectV::Unblock { .. } => false,
            } by {
            assert(note_effects(prior).contains(effect) <==> match effect {
                ProtocolEffectV::Execute { id, version } =>
                    keys.take(count as int - 1).contains(id)
                        && echod_concrete_spec::document::offer_committed(
                            before,
                            after,
                            id,
                            committed_at,
                        )
                        && after[id].task.unwrap().version == version,
                ProtocolEffectV::Unblock { .. } => false,
            });
            match effect {
                ProtocolEffectV::Execute { id: effect_id, version } => {
                    if echod_concrete_spec::document::offer_committed(
                        before,
                        after,
                        id,
                        committed_at,
                    ) {
                        let note = NoteV::Execute {
                            id,
                            version: after[id].task.unwrap().version,
                        };
                        lemma_note_effects_push(prior, note);
                        assert(spec_execute_notes(
                            before,
                            after,
                            committed_at,
                            keys,
                            count,
                        ) == prior.push(note));
                        assert(note_effects(prior.push(note)).contains(effect)
                            <==> note_effects(prior).contains(effect)
                                || effect == note_effect(note));
                        assert(effect == note_effect(note)
                            <==> effect_id == id
                                && version == after[id].task.unwrap().version);
                    } else {
                        assert(spec_execute_notes(
                            before,
                            after,
                            committed_at,
                            keys,
                            count,
                        ) == prior);
                    }
                    if effect_id == id
                        && echod_concrete_spec::document::offer_committed(
                            before,
                            after,
                            id,
                            committed_at,
                        )
                    {
                        assert(!keys.take(count as int - 1).contains(id));
                    }
                },
                ProtocolEffectV::Unblock { .. } => {},
            }
        };
    }
}


proof fn lemma_unblock_notes_for(
    before: Map<Seq<char>, ObjV>,
    after: Map<Seq<char>, ObjV>,
    promise: Seq<char>,
    listeners: Seq<Seq<char>>,
    count: nat,
)
    requires
        count <= listeners.len(),
        listeners.take(count as int).no_duplicates(),
    ensures
        ({
            let notes =
                spec_unblock_notes_for(before, after, promise, listeners, count);
            &&& forall|effect: ProtocolEffectV|
                note_effects(notes).contains(effect) <==> match effect {
                    ProtocolEffectV::Execute { .. } => false,
                    ProtocolEffectV::Unblock {
                        promise: effect_promise,
                        address,
                        record,
                    } =>
                        effect_promise == promise
                            && listeners.take(count as int).contains(address)
                            && echod_concrete_spec::document::listener_committed(
                                before,
                                after,
                                promise,
                                address,
                            )
                            && record == echod_concrete_spec::document::promise_effect(
                                promise,
                                after[promise].promise,
                            ),
                }
            &&& note_effect_keys(notes).no_duplicates()
        }),
    decreases count,
{
    if count > 0 {
        let prior = spec_unblock_notes_for(
            before,
            after,
            promise,
            listeners,
            (count - 1) as nat,
        );
        let address = listeners[count as int - 1];
        lemma_unblock_notes_for(
            before,
            after,
            promise,
            listeners,
            (count - 1) as nat,
        );
        lemma_nodup_last_not_in_prefix(listeners, count);
        assert(listeners.take(count as int)
            == listeners.take(count as int - 1).push(address));
        if echod_concrete_spec::document::listener_committed(
            before,
            after,
            promise,
            address,
        ) {
            super::interpretation::lemma_string_view(promise);
            let note = NoteV::Unblock {
                address,
                promise: echod_concrete_spec::state::spec_record(
                    echod_concrete_spec::rover::spec_string(promise),
                    after[promise].promise,
                ),
            };
            lemma_note_effects_push(prior, note);
            assert(record_effect(echod_concrete_spec::state::spec_record(
                echod_concrete_spec::rover::spec_string(promise),
                after[promise].promise,
            )) == echod_concrete_spec::document::promise_effect(
                promise,
                after[promise].promise,
            ));
            lemma_note_effects_add(prior, seq![note]);
            assert(prior + seq![note] =~= prior.push(note));
            assert(spec_unblock_notes_for(
                before,
                after,
                promise,
                listeners,
                count,
            ) == prior.push(note));
            assert(note_effect_keys(prior.push(note))
                == note_effect_keys(prior).push(
                    ProtocolEffectKeyV::Unblock { promise, address },
                ));
            assert(!note_effect_keys(prior).contains(
                ProtocolEffectKeyV::Unblock { promise, address },
            )) by {
                if note_effect_keys(prior).contains(
                    ProtocolEffectKeyV::Unblock { promise, address },
                ) {
                    let i = choose|i: int| 0 <= i < prior.len()
                        && note_effect_keys(prior)[i]
                            == ProtocolEffectKeyV::Unblock { promise, address };
                    assert(note_effect_keys(prior)[i]
                        == echod_concrete_spec::document::protocol_effect_key(note_effect(prior[i])));
                    assert(note_effects(prior).contains(note_effect(prior[i])));
                    match note_effect(prior[i]) {
                        ProtocolEffectV::Unblock {
                            promise: prior_promise,
                            address: prior_address,
                            ..
                        } => {
                            assert(prior_promise == promise);
                            assert(prior_address == address);
                            assert(listeners.take(count as int - 1)
                                .contains(prior_address));
                        },
                        ProtocolEffectV::Execute { .. } => {
                            assert(false);
                        },
                    }
                }
            };
        } else {
            assert(spec_unblock_notes_for(
                before,
                after,
                promise,
                listeners,
                count,
            ) == prior);
        }
        assert forall|candidate: Seq<char>|
            listeners.take(count as int).contains(candidate)
                <==> listeners.take(count as int - 1).contains(candidate)
                    || candidate == address by {
            super::simulation::lemma_push_contains(
                listeners.take(count as int - 1),
                address,
                candidate,
            );
            if listeners.take(count as int).contains(candidate) {
                let i = choose|i: int| 0 <= i < listeners.take(count as int).len()
                    && listeners.take(count as int)[i] == candidate;
                if i < count as int - 1 {
                    assert(listeners.take(count as int - 1)[i] == candidate);
                } else {
                    assert(i == count as int - 1);
                }
            }
            if listeners.take(count as int - 1).contains(candidate) {
                let i = choose|i: int|
                    0 <= i < listeners.take(count as int - 1).len()
                        && #[trigger] listeners.take(count as int - 1)[i] == candidate;
                assert(listeners.take(count as int)[i] == candidate);
            }
        };
        assert forall|effect: ProtocolEffectV|
            note_effects(spec_unblock_notes_for(
                before,
                after,
                promise,
                listeners,
                count,
            )).contains(effect) <==> match effect {
                ProtocolEffectV::Execute { .. } => false,
                ProtocolEffectV::Unblock {
                    promise: effect_promise,
                    address: effect_address,
                    record,
                } =>
                    effect_promise == promise
                        && listeners.take(count as int).contains(effect_address)
                        && echod_concrete_spec::document::listener_committed(
                            before,
                            after,
                            promise,
                            effect_address,
                        )
                        && record == echod_concrete_spec::document::promise_effect(
                            promise,
                            after[promise].promise,
                        ),
            } by {
            assert(note_effects(prior).contains(effect) <==> match effect {
                ProtocolEffectV::Execute { .. } => false,
                ProtocolEffectV::Unblock {
                    promise: effect_promise,
                    address: effect_address,
                    record,
                } =>
                    effect_promise == promise
                        && listeners.take(count as int - 1).contains(effect_address)
                        && echod_concrete_spec::document::listener_committed(
                            before,
                            after,
                            promise,
                            effect_address,
                        )
                        && record == echod_concrete_spec::document::promise_effect(
                            promise,
                            after[promise].promise,
                        ),
            });
            match effect {
                ProtocolEffectV::Execute { .. } => {},
                ProtocolEffectV::Unblock {
                    promise: effect_promise,
                    address: effect_address,
                    record,
                } => {
                    if echod_concrete_spec::document::listener_committed(
                        before,
                        after,
                        promise,
                        address,
                    ) {
                        super::interpretation::lemma_string_view(promise);
                        let note = NoteV::Unblock {
                            address,
                            promise: echod_concrete_spec::state::spec_record(
                                echod_concrete_spec::rover::spec_string(promise),
                                after[promise].promise,
                            ),
                        };
                        lemma_note_effects_push(prior, note);
                        assert(spec_unblock_notes_for(
                            before,
                            after,
                            promise,
                            listeners,
                            count,
                        ) == prior.push(note));
                        assert(note_effects(prior.push(note)).contains(effect)
                            <==> note_effects(prior).contains(effect)
                                || effect == note_effect(note));
                        assert(effect == note_effect(note) <==> {
                            &&& effect_promise == promise
                            &&& effect_address == address
                            &&& record == echod_concrete_spec::document::promise_effect(
                                promise,
                                after[promise].promise,
                            )
                        });
                    } else {
                        assert(spec_unblock_notes_for(
                            before,
                            after,
                            promise,
                            listeners,
                            count,
                        ) == prior);
                    }
                },
            }
        }
    }
}


proof fn lemma_add_no_duplicates<A>(first: Seq<A>, second: Seq<A>)
    requires
        first.no_duplicates(),
        second.no_duplicates(),
        forall|i: int, j: int|
            0 <= i < first.len() && 0 <= j < second.len()
                ==> first[i] != second[j],
    ensures
        (first + second).no_duplicates(),
{
    assert forall|i: int, j: int|
        0 <= i < (first + second).len()
            && 0 <= j < (first + second).len()
            && (first + second)[i] == (first + second)[j]
                implies i == j by {
        if i < first.len() && j < first.len() {
            assert((first + second)[i] == first[i]);
            assert((first + second)[j] == first[j]);
        } else if i >= first.len() && j >= first.len() {
            assert((first + second)[i] == second[i - first.len()]);
            assert((first + second)[j] == second[j - first.len()]);
        } else if i < first.len() {
            assert((first + second)[i] == first[i]);
            assert((first + second)[j] == second[j - first.len()]);
        } else {
            assert((first + second)[j] == first[j]);
            assert((first + second)[i] == second[i - first.len()]);
        }
    };
}


proof fn lemma_unblock_notes(
    before: Map<Seq<char>, ObjV>,
    after: Map<Seq<char>, ObjV>,
    keys: Seq<Seq<char>>,
    count: nat,
)
    requires
        count <= keys.len(),
        keys.take(count as int).no_duplicates(),
        forall|i: int| 0 <= i < count ==> {
            &&& before.contains_key(#[trigger] keys[i])
            &&& before[keys[i]].promise.listeners.no_duplicates()
        },
    ensures
        ({
            let notes = spec_unblock_notes(before, after, keys, count);
            &&& forall|effect: ProtocolEffectV|
                note_effects(notes).contains(effect) <==> match effect {
                    ProtocolEffectV::Execute { .. } => false,
                    ProtocolEffectV::Unblock {
                        promise,
                        address,
                        record,
                    } =>
                        keys.take(count as int).contains(promise)
                            && echod_concrete_spec::document::listener_committed(
                                before,
                                after,
                                promise,
                                address,
                            )
                            && record == echod_concrete_spec::document::promise_effect(
                                promise,
                                after[promise].promise,
                            ),
                }
            &&& note_effect_keys(notes).no_duplicates()
        }),
    decreases count,
{
    if count > 0 {
        let prior = spec_unblock_notes(before, after, keys, (count - 1) as nat);
        let promise = keys[count as int - 1];
        let listeners = before[promise].promise.listeners;
        let current = spec_unblock_notes_for(
            before,
            after,
            promise,
            listeners,
            listeners.len(),
        );
        lemma_unblock_notes(before, after, keys, (count - 1) as nat);
        lemma_unblock_notes_for(
            before,
            after,
            promise,
            listeners,
            listeners.len(),
        );
        lemma_nodup_last_not_in_prefix(keys, count);
        assert(keys.take(count as int)
            == keys.take(count as int - 1).push(promise));
        assert(spec_unblock_notes(before, after, keys, count) == prior + current);
        lemma_note_effects_add(prior, current);
        assert(note_effect_keys(prior + current)
            == note_effect_keys(prior) + note_effect_keys(current));
        assert forall|i: int, j: int|
            0 <= i < note_effect_keys(prior).len()
                && 0 <= j < note_effect_keys(current).len()
                implies note_effect_keys(prior)[i] != note_effect_keys(current)[j] by {
            assert(note_effect_keys(prior)[i]
                == echod_concrete_spec::document::protocol_effect_key(note_effect(prior[i])));
            assert(note_effect_keys(current)[j]
                == echod_concrete_spec::document::protocol_effect_key(note_effect(current[j])));
            assert(note_effects(prior).contains(note_effect(prior[i])));
            assert(note_effects(current).contains(note_effect(current[j])));
            match (note_effect(prior[i]), note_effect(current[j])) {
                (
                    ProtocolEffectV::Unblock { promise: left, .. },
                    ProtocolEffectV::Unblock { promise: right, .. },
                ) => {
                    assert(keys.take(count as int - 1).contains(left));
                    assert(right == promise);
                    assert(left != right);
                },
                _ => {},
            }
        };
        lemma_add_no_duplicates(
            note_effect_keys(prior),
            note_effect_keys(current),
        );
        assert forall|candidate: Seq<char>|
            keys.take(count as int).contains(candidate)
                <==> keys.take(count as int - 1).contains(candidate)
                    || candidate == promise by {
            super::simulation::lemma_push_contains(
                keys.take(count as int - 1),
                promise,
                candidate,
            );
        };
        assert forall|effect: ProtocolEffectV|
            note_effects(spec_unblock_notes(before, after, keys, count))
                .contains(effect) <==> match effect {
                ProtocolEffectV::Execute { .. } => false,
                ProtocolEffectV::Unblock {
                    promise: effect_promise,
                    address,
                    record,
                } =>
                    keys.take(count as int).contains(effect_promise)
                        && echod_concrete_spec::document::listener_committed(
                            before,
                            after,
                            effect_promise,
                            address,
                        )
                        && record == echod_concrete_spec::document::promise_effect(
                            effect_promise,
                            after[effect_promise].promise,
                        ),
            } by {
            assert(note_effects(prior + current).contains(effect)
                <==> note_effects(prior).contains(effect)
                    || note_effects(current).contains(effect));
            lemma_note_effects_add(prior, current);
            assert(note_effects(prior).contains(effect) <==> match effect {
                ProtocolEffectV::Execute { .. } => false,
                ProtocolEffectV::Unblock {
                    promise,
                    address,
                    record,
                } =>
                    keys.take(count as int - 1).contains(promise)
                        && echod_concrete_spec::document::listener_committed(
                            before,
                            after,
                            promise,
                            address,
                        )
                        && record == echod_concrete_spec::document::promise_effect(
                            promise,
                            after[promise].promise,
                        ),
            });
            assert(listeners.take(listeners.len() as int) == listeners);
            assert(note_effects(current).contains(effect) <==> match effect {
                ProtocolEffectV::Execute { .. } => false,
                ProtocolEffectV::Unblock {
                    promise: effect_promise,
                    address,
                    record,
                } =>
                    effect_promise == promise
                        && listeners.contains(address)
                        && echod_concrete_spec::document::listener_committed(
                            before,
                            after,
                            promise,
                            address,
                        )
                        && record == echod_concrete_spec::document::promise_effect(
                            promise,
                            after[promise].promise,
                        ),
            });
            match effect {
                ProtocolEffectV::Execute { .. } => {},
                ProtocolEffectV::Unblock {
                    promise: effect_promise,
                    address,
                    ..
                } => {
                    if effect_promise == promise
                        && echod_concrete_spec::document::listener_committed(
                            before,
                            after,
                            promise,
                            address,
                        )
                    {
                        assert(listeners.contains(address));
                    }
                },
            }
        }
    }
}


proof fn lemma_sorted_no_duplicates(keys: Set<Seq<char>>)
    ensures
        echod_concrete_spec::state::spec_sorted(keys).no_duplicates(),
    decreases keys.len(),
{
    if keys.len() > 0 {
        super::work::lemma_min_key(keys);
        let first = echod_concrete_spec::state::spec_min_key(keys);
        let rest = keys.remove(first);
        lemma_sorted_no_duplicates(rest);
        super::work::lemma_sorted(rest);
        assert(!echod_concrete_spec::state::spec_sorted(rest).contains(first)) by {
            if echod_concrete_spec::state::spec_sorted(rest).contains(first) {
                let i = choose|i: int|
                    0 <= i < echod_concrete_spec::state::spec_sorted(rest).len()
                        && #[trigger] echod_concrete_spec::state::spec_sorted(rest)[i] == first;
                assert(rest.contains(first));
            }
        };
        assert(echod_concrete_spec::state::spec_sorted(keys)
            == seq![first] + echod_concrete_spec::state::spec_sorted(rest));
    }
}


proof fn lemma_committed_notes_match(
    before: DocumentBodyV,
    after: DocumentBodyV,
    committed_at: u64,
)
    requires
        match before {
            DocumentBodyV::Workflow(old) =>
                forall|id: Seq<char>| old.contains_key(id) ==>
                    old[id].promise.listeners.no_duplicates(),
            DocumentBodyV::Schedule(_) => true,
        },
    ensures
        ({
            let notes = spec_committed_notes(before, after, committed_at);
            &&& note_effects(notes) == match (before, after) {
                (DocumentBodyV::Workflow(old), DocumentBodyV::Workflow(new)) =>
                    workflow_effects(old, new, committed_at),
                _ => ISet::empty(),
            }
            &&& note_effect_keys(notes).no_duplicates()
        }),
{
    match (before, after) {
        (DocumentBodyV::Workflow(old), DocumentBodyV::Workflow(new)) => {
            let new_keys = spec_sorted_present(new);
            let old_keys = spec_sorted_present(old);
            super::work::lemma_sorted(new.dom());
            super::work::lemma_sorted(old.dom());
            lemma_sorted_no_duplicates(new.dom());
            lemma_sorted_no_duplicates(old.dom());
            lemma_execute_notes(
                old,
                new,
                committed_at,
                new_keys,
                new_keys.len(),
            );
            lemma_unblock_notes(old, new, old_keys, old_keys.len());
            let executes = spec_execute_notes(
                old,
                new,
                committed_at,
                new_keys,
                new_keys.len(),
            );
            let unblocks =
                spec_unblock_notes(old, new, old_keys, old_keys.len());
            lemma_note_effects_add(executes, unblocks);
            assert(new_keys.take(new_keys.len() as int) == new_keys);
            assert(old_keys.take(old_keys.len() as int) == old_keys);
            assert(note_effect_keys(executes + unblocks)
                == note_effect_keys(executes) + note_effect_keys(unblocks));
            assert forall|i: int, j: int|
                0 <= i < note_effect_keys(executes).len()
                    && 0 <= j < note_effect_keys(unblocks).len()
                    implies note_effect_keys(executes)[i]
                        != note_effect_keys(unblocks)[j] by {
                assert(note_effect_keys(executes)[i]
                    == echod_concrete_spec::document::protocol_effect_key(
                        note_effect(executes[i]),
                    ));
                assert(note_effect_keys(unblocks)[j]
                    == echod_concrete_spec::document::protocol_effect_key(
                        note_effect(unblocks[j]),
                    ));
                assert(note_effects(executes).contains(note_effect(executes[i])));
                assert(note_effects(unblocks).contains(note_effect(unblocks[j])));
            };
            lemma_add_no_duplicates(
                note_effect_keys(executes),
                note_effect_keys(unblocks),
            );
            assert forall|effect: ProtocolEffectV|
                note_effects(executes + unblocks).contains(effect)
                    <==> workflow_effects(old, new, committed_at).contains(effect) by {
                assert(note_effects(executes + unblocks).contains(effect)
                    <==> note_effects(executes).contains(effect)
                        || note_effects(unblocks).contains(effect));
                assert(note_effects(executes).contains(effect) <==> match effect {
                    ProtocolEffectV::Execute { id, version } =>
                        new_keys.contains(id)
                            && echod_concrete_spec::document::offer_committed(
                                old,
                                new,
                                id,
                                committed_at,
                            )
                            && new[id].task.unwrap().version == version,
                    ProtocolEffectV::Unblock { .. } => false,
                });
                assert(note_effects(unblocks).contains(effect) <==> match effect {
                    ProtocolEffectV::Execute { .. } => false,
                    ProtocolEffectV::Unblock {
                        promise,
                        address,
                        record,
                    } =>
                        old_keys.contains(promise)
                            && echod_concrete_spec::document::listener_committed(
                                old,
                                new,
                                promise,
                                address,
                            )
                            && record == echod_concrete_spec::document::promise_effect(
                                promise,
                                new[promise].promise,
                            ),
                });
                match effect {
                    ProtocolEffectV::Execute { id, .. } => {
                        if new.contains_key(id) {
                            assert(new_keys.contains(id));
                        }
                        if new_keys.contains(id) {
                            let i = choose|i: int| 0 <= i < new_keys.len()
                                && #[trigger] new_keys[i] == id;
                            assert(new.dom().contains(new_keys[i]));
                            assert(new.contains_key(id));
                        }
                    },
                    ProtocolEffectV::Unblock { promise, .. } => {
                        if old.contains_key(promise) {
                            assert(old_keys.contains(promise));
                        }
                        if old_keys.contains(promise) {
                            let i = choose|i: int| 0 <= i < old_keys.len()
                                && #[trigger] old_keys[i] == promise;
                            assert(old.dom().contains(old_keys[i]));
                            assert(old.contains_key(promise));
                        }
                    },
                }
            };
            assert(note_effects(executes + unblocks)
                =~= workflow_effects(old, new, committed_at));
        },
        _ => {
            assert(spec_committed_notes(before, after, committed_at)
                =~= Seq::<NoteV>::empty());
            assert(note_effects(Seq::<NoteV>::empty())
                =~= ISet::<ProtocolEffectV>::empty());
        },
    }
}


/// Complete endpoint correspondence for one atomic request transition.
#[verifier::rlimit(20)]
pub proof fn lemma_request_transition_effects(
    document: StoredDocumentV,
    request: Request,
    now: u64,
    retry_timeout: u64,
    limit: nat,
)
    requires
        well_formed(document),
        routed(document, request),
        spec_stored_committed_at(document) <= now,
        safe_effect_config(now, retry_timeout),
    ensures
        ({
            let final_document =
                on_request(document, request, now, retry_timeout, limit);
            let (_, _, _, notes) = spec_request_transition(
                spec_stored_body(document),
                request,
                now,
                retry_timeout,
                limit,
            );
            effects_match(document, final_document, notes)
        }),
{
    let initial_body = spec_stored_body(document);
    let (final_body, response, _, notes) = spec_request_transition(
        initial_body,
        request,
        now,
        retry_timeout,
        limit,
    );
    assert(match initial_body {
        DocumentBodyV::Workflow(old) =>
            forall|id: Seq<char>| old.contains_key(id) ==>
                old[id].promise.listeners.no_duplicates(),
        DocumentBodyV::Schedule(_) => true,
    }) by {
        match document {
            StoredDocumentV::Workflow(workflow) => {
                reveal(echod_concrete_spec::document::workflow_well_formed);
                reveal(echod_concrete_spec::document::workflow_body_well_formed);
                assert(echod_concrete_spec::document::workflow_well_formed(workflow));
                assert(echod_concrete_spec::document::workflow_body_well_formed(
                    workflow.document,
                    workflow.objects,
                    workflow.committed_at,
                ));
                assert forall|id: Seq<char>|
                    workflow.objects.contains_key(id) implies
                        workflow.objects[id].promise.listeners.no_duplicates() by {
                    assert({
                        &&& echod_types::origin(id) == workflow.document
                        &&& echod_concrete_spec::document::promise_well_formed(
                            id,
                            workflow.objects[id],
                            workflow.committed_at,
                        )
                        &&& echod_concrete_spec::document::task_well_formed(
                            workflow.objects[id],
                            workflow.committed_at,
                        )
                        &&& echod_concrete_spec::document::callback_targets_well_formed(
                            workflow.objects,
                            workflow.objects[id],
                        )
                        &&& echod_concrete_spec::document::suspended_rung_well_formed(
                            workflow.objects,
                            id,
                            workflow.objects[id],
                        )
                    });
                    assert(echod_concrete_spec::document::promise_well_formed(
                        id,
                        workflow.objects[id],
                        workflow.committed_at,
                    ));
                }
            },
            StoredDocumentV::Schedule(_) => {},
        }
    };
    if spec_request_commits(
        initial_body,
        request,
        now,
        retry_timeout,
        limit,
    ) {
        assert(notes == spec_committed_notes(initial_body, final_body, now));
        lemma_committed_notes_match(initial_body, final_body, now);
        match (document, final_body) {
            (StoredDocumentV::Workflow(old), DocumentBodyV::Workflow(new)) => {
                assert(on_request(
                    StoredDocumentV::Workflow(old),
                    request,
                    now,
                    retry_timeout,
                    limit,
                ) == echod_concrete_spec::state::spec_advance_stored(
                    StoredDocumentV::Workflow(old),
                    DocumentBodyV::Workflow(new),
                    now,
                ));
                assert(document_effects(
                    StoredDocumentV::Workflow(old),
                    on_request(
                        StoredDocumentV::Workflow(old),
                        request,
                        now,
                        retry_timeout,
                        limit,
                    ),
                ) == workflow_effects(old.objects, new, now));
            },
            (StoredDocumentV::Schedule(old), DocumentBodyV::Schedule(new)) => {
                assert(document_effects(
                    StoredDocumentV::Schedule(old),
                    on_request(
                        StoredDocumentV::Schedule(old),
                        request,
                        now,
                        retry_timeout,
                        limit,
                    ),
                ) == ISet::<ProtocolEffectV>::empty());
            },
            _ => {},
        }
    } else {
        assert(final_body == initial_body);
        if response == spec_unavailable(request) {
            assert(notes =~= Seq::<NoteV>::empty());
            assert(note_effects(notes) =~= ISet::<ProtocolEffectV>::empty());
            assert(note_effect_keys(notes) =~= Seq::<ProtocolEffectKeyV>::empty());
        } else {
            match initial_body {
                DocumentBodyV::Workflow(_) => {
                    assert(notes == spec_committed_notes(initial_body, final_body, now));
                },
                DocumentBodyV::Schedule(_) => {
                    assert(notes =~= Seq::<NoteV>::empty());
                    assert(spec_committed_notes(initial_body, final_body, now)
                        =~= Seq::<NoteV>::empty());
                },
            }
            lemma_committed_notes_match(initial_body, final_body, now);
        }
        assert(on_request(document, request, now, retry_timeout, limit) == document);
        assert(document_effects(document, document)
            =~= ISet::<ProtocolEffectV>::empty()) by {
            match document {
                StoredDocumentV::Workflow(workflow) => {
                    assert forall|effect: ProtocolEffectV|
                        !workflow_effects(
                            workflow.objects,
                            workflow.objects,
                            workflow.committed_at,
                        ).contains(effect) by {
                        match effect {
                            ProtocolEffectV::Execute { .. } => {},
                            ProtocolEffectV::Unblock { .. } => {},
                        }
                    };
                },
                StoredDocumentV::Schedule(_) => {},
            }
        };
    }
    assert(note_effects(notes)
        == document_effects(
            document,
            on_request(document, request, now, retry_timeout, limit),
        ));
    assert(note_effect_keys(notes).no_duplicates());
}

} // verus!

}
