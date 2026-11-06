//! The relation: an `AState` read as a `DocV`, object by object through the
//! projection at `now`; the tag readers of the two sides agree; the records
//! a response carries agree.

use vstd::prelude::*;

use echod_types::spec::*;
use echod_types::{PromiseState, Request, Response, Schedule, Tags, TaskState, Value};

use echod_document::state::AState;
use echod_document::tags::{is_timer, otype, tags_get, tags_has, OType};
use echod_document::types::{APromise, ATask, MAX_TIME, MAX_VERSION};

use echod_concrete::interpret::lemma_string_view;
use echod_concrete::node::{
    spec_awaitable, spec_delay, spec_parse_u64, spec_project_obj, spec_record, spec_tag_is,
    spec_tag_key, spec_targeted, spec_task_record, spec_timer, DocV, ObjV, PromV, TkV,
};

verus! {

broadcast use {vstd::seq::group_seq_lemmas, vstd::map::group_map_lemmas};

// ---------------------------------------------------------------------------
// One object, read as the process's row
// ---------------------------------------------------------------------------

pub open spec fn to_task(t: TkV) -> ATask {
    ATask {
        state: t.state,
        version: t.version,
        ttl: t.ttl,
        pid: t.pid,
        lease_timeout_at: t.lease_timeout_at,
        retry_timeout_at: t.retry_timeout_at,
        resumes: t.resumes,
    }
}

pub open spec fn to_prom(id: Seq<char>, o: ObjV) -> APromise {
    APromise {
        id,
        state: o.promise.state,
        tags: o.promise.tags.deep_view(),
        param: o.promise.param@,
        value: o.promise.value@,
        timeout_at: o.promise.timeout_at,
        created_at: o.promise.created_at,
        settled_at: o.promise.settled_at,
        callbacks: o.promise.callbacks,
        listeners: o.promise.listeners,
        task: match o.task {
            Some(t) => Some(to_task(t)),
            None => None,
        },
    }
}

/// The map of a model document, read as the process's objects.
pub open spec fn to_objects(map: Map<Seq<char>, ObjV>) -> Map<Seq<char>, APromise> {
    Map::new(map.dom(), |id: Seq<char>| to_prom(id, map[id]))
}

// ---------------------------------------------------------------------------
// Tags: first match wins on both sides
// ---------------------------------------------------------------------------

pub proof fn lemma_tag_is(tags: Tags, key: Seq<char>, value: Seq<char>, i: int)
    requires
        0 <= i <= tags@.len(),
    ensures
        spec_tag_is(tags, key, value, i) == (tags_get(tags.deep_view().skip(i), key) == Some(value)),
    decreases tags@.len() - i,
{
    let v = tags.deep_view();
    assert(v.len() == tags@.len());
    if i < tags@.len() {
        assert(v.skip(i).len() == v.len() - i);
        assert(v.skip(i)[0] == v[i]);
        assert(v[i] == (tags@[i].0@, tags@[i].1@));
        assert(v.skip(i).drop_first() =~= v.skip(i + 1));
        lemma_tag_is(tags, key, value, i + 1);
    } else {
        assert(v.skip(i).len() == 0);
    }
}

pub proof fn lemma_tag_key(tags: Tags, key: Seq<char>, i: int)
    requires
        0 <= i <= tags@.len(),
    ensures
        spec_tag_key(tags, key, i) == tags_has(tags.deep_view().skip(i), key),
    decreases tags@.len() - i,
{
    let v = tags.deep_view();
    assert(v.len() == tags@.len());
    if i < tags@.len() {
        assert(v.skip(i).len() == v.len() - i);
        assert(v.skip(i)[0] == v[i]);
        assert(v[i] == (tags@[i].0@, tags@[i].1@));
        assert(v.skip(i).drop_first() =~= v.skip(i + 1));
        lemma_tag_key(tags, key, i + 1);
    } else {
        assert(v.skip(i).len() == 0);
    }
}

/// `spec_delay` is the first `resonate:delay` tag, parsed.
pub proof fn lemma_delay(tags: Tags, i: int)
    requires
        0 <= i <= tags@.len(),
    ensures
        spec_delay(tags, i) == match tags_get(tags.deep_view().skip(i), "resonate:delay"@) {
            Some(d) => spec_parse_u64(d),
            None => None,
        },
    decreases tags@.len() - i,
{
    let v = tags.deep_view();
    assert(v.len() == tags@.len());
    reveal_strlit("resonate:delay");
    assert("resonate:delay"@ =~= seq!['r','e','s','o','n','a','t','e',':','d','e','l','a','y']);
    if i < tags@.len() {
        assert(v.skip(i).len() == v.len() - i);
        assert(v.skip(i)[0] == v[i]);
        assert(v[i] == (tags@[i].0@, tags@[i].1@));
        assert(v.skip(i).drop_first() =~= v.skip(i + 1));
        lemma_delay(tags, i + 1);
    } else {
        assert(v.skip(i).len() == 0);
    }
}

pub proof fn lemma_tags(tags: Tags)
    ensures
        spec_timer(tags) == is_timer(tags.deep_view()),
        spec_targeted(tags) == tags_has(tags.deep_view(), "resonate:target"@),
        spec_targeted(tags) == (otype(tags.deep_view()) == OType::Runnable),
        spec_awaitable(tags) == otype(tags.deep_view()).awaitable(),
{
    let v = tags.deep_view();
    assert(v.skip(0) =~= v);
    reveal_strlit("resonate:timer");
    reveal_strlit("true");
    reveal_strlit("resonate:target");
    reveal_strlit("resonate:external");
    reveal_strlit("resonate:scope");
    reveal_strlit("global");
    assert("resonate:timer"@ =~= seq!['r','e','s','o','n','a','t','e',':','t','i','m','e','r']);
    assert("true"@ =~= seq!['t','r','u','e']);
    assert("resonate:target"@ =~= seq!['r','e','s','o','n','a','t','e',':','t','a','r','g','e','t']);
    assert("resonate:external"@ =~= seq!['r','e','s','o','n','a','t','e',':','e','x','t','e','r','n','a','l']);
    assert("resonate:scope"@ =~= seq!['r','e','s','o','n','a','t','e',':','s','c','o','p','e']);
    assert("global"@ =~= seq!['g','l','o','b','a','l']);
    lemma_tag_is(tags, "resonate:timer"@, "true"@, 0);
    lemma_tag_key(tags, "resonate:target"@, 0);
    lemma_tag_is(tags, "resonate:external"@, "true"@, 0);
    lemma_tag_is(tags, "resonate:scope"@, "global"@, 0);
}

// ---------------------------------------------------------------------------
// Projection commutes with the reading
// ---------------------------------------------------------------------------

pub proof fn lemma_project(id: Seq<char>, o: ObjV, now: u64)
    ensures
        to_prom(id, spec_project_obj(o, now)) == to_prom(id, o).project(now as nat),
{
    lemma_tags(o.promise.tags);
}

/// Projecting twice is projecting once.
pub proof fn lemma_project_twice(p: APromise, now: nat)
    ensures
        p.project(now).project(now) == p.project(now),
{
}

/// A projection at `now` is absorbed by one at a later `later`.
pub proof fn lemma_project_later(p: APromise, now: nat, later: nat)
    requires
        now <= later,
    ensures
        p.project(now).project(later) == p.project(later),
{
}

// ---------------------------------------------------------------------------
// Records
// ---------------------------------------------------------------------------

pub proof fn lemma_record(id: String, o: ObjV)
    ensures
        spec_record(id, o.promise)@ == to_prom(id@, o).to_record(),
{
}

pub proof fn lemma_task_record(id: String, t: TkV)
    ensures
        spec_task_record(id, t)@ == to_task(t).to_record(id@),
{
    if t.pid is Some {
        lemma_string_view(t.pid.unwrap());
    }
}

// ---------------------------------------------------------------------------
// The relation
// ---------------------------------------------------------------------------

/// The process's objects and the model's map hold the same ids, and each
/// object reads the same once projected at `now`.
pub open spec fn objs_rel(objs: Map<Seq<char>, APromise>, map: Map<Seq<char>, ObjV>, now: nat) -> bool {
    &&& objs.dom() == map.dom()
    &&& forall|id: Seq<char>| #[trigger] map.contains_key(id) ==>
        objs[id].project(now) == to_prom(id, map[id]).project(now)
}

/// A schedule slot, as the process's schedules.
pub open spec fn sched_map(slot: Option<Schedule>) -> Map<Seq<char>, ASchedule> {
    match slot {
        Some(s) => Map::empty().insert(s.id@, s@),
        None => Map::empty(),
    }
}

/// An `AState` reads as a `DocV`. The outbox is the drain's and no
/// handler's; the relation leaves it alone.
pub open spec fn doc_rel(a: AState, doc: DocV, now: nat) -> bool {
    match doc {
        DocV::Origin(map) => objs_rel(a.objects, map, now) && a.schedules == Map::<Seq<char>, ASchedule>::empty(),
        DocV::Schedule(slot) => a.objects == Map::<Seq<char>, APromise>::empty() && a.schedules == sched_map(slot),
    }
}

/// Related at `now`, related at any later instant.
pub proof fn lemma_rel_later(a: AState, doc: DocV, now: nat, later: nat)
    requires
        doc_rel(a, doc, now),
        now <= later,
    ensures
        doc_rel(a, doc, later),
{
    match doc {
        DocV::Origin(map) => {
            assert forall|id: Seq<char>| #[trigger] map.contains_key(id) implies
                a.objects[id].project(later) == to_prom(id, map[id]).project(later) by {
                lemma_project_later(a.objects[id], now, later);
                lemma_project_later(to_prom(id, map[id]), now, later);
            }
        },
        DocV::Schedule(_) => {},
    }
}

// ---------------------------------------------------------------------------
// Hypotheses
// ---------------------------------------------------------------------------

/// Every task in the map is below the process's version ceiling and its ttl
/// within its time bound.
pub open spec fn doc_ok(doc: DocV) -> bool {
    match doc {
        DocV::Origin(map) => forall|id: Seq<char>| #[trigger] map.contains_key(id) ==> match map[id].task {
            Some(t) => t.version < MAX_VERSION && (t.ttl is Some ==> t.ttl.unwrap() <= MAX_TIME),
            None => true,
        },
        DocV::Schedule(_) => true,
    }
}

/// A `resonate:delay` tag parses the same on both sides: the process's
/// `spec_parse_nat` is uninterpreted, so this is stated.
pub open spec fn delay_ok(tags: Tags) -> bool {
    match tags_get(tags.deep_view(), "resonate:delay"@) {
        Some(d) => spec_parse_u64(d) is Some
            && echod_document::types::spec_parse_nat(d) == spec_parse_u64(d).unwrap() as nat,
        None => true,
    }
}

pub open spec fn create_ok(req: echod_types::PromiseCreateReq) -> bool {
    req.timeout_at <= MAX_TIME && delay_ok(req.tags)
}

/// What the process establishes of a request before its handler runs.
pub open spec fn req_ok(req: Request, now: u64) -> bool {
    match req {
        Request::PromiseCreate(q) => create_ok(q),
        Request::TaskCreate(q) => create_ok(q.action) && q.ttl <= MAX_TIME,
        Request::TaskAcquire(q) => q.ttl <= MAX_TIME,
        Request::TaskFence(q) => match q.action {
            echod_types::TaskFenceAction::Create(c) => create_ok(c),
            echod_types::TaskFenceAction::Settle(_) => true,
        },
        Request::TaskHeartbeat(q) => q.tasks@.len() > 0
            && echod_concrete::node::spec_one_origin(q.tasks@, echod_types::origin(q.tasks@[0].id@), 0),
        Request::ScheduleCreate(q) => q.promise_timeout <= MAX_TIME
            && q.next_run_at == echod_abstract::trusted::spec_next_cron(q.cron@, now),
        _ => true,
    }
}

/// A request is served on the document of its kind: a schedule request on a
/// schedule's, the rest on an origin's.
pub open spec fn kind_ok(doc: DocV, req: Request) -> bool {
    match req {
        Request::ScheduleGet(q) => doc is Schedule && slot_of(doc, q.id@),
        Request::ScheduleCreate(q) => doc is Schedule && slot_of(doc, q.id@),
        Request::ScheduleDelete(q) => doc is Schedule && slot_of(doc, q.id@),
        _ => doc is Origin,
    }
}

/// A schedule document holds nothing, or the schedule named.
pub open spec fn slot_of(doc: DocV, id: Seq<char>) -> bool {
    match doc {
        DocV::Schedule(Some(s)) => s.id@ == id,
        _ => true,
    }
}

} // verus!
