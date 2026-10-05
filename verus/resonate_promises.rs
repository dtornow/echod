//! Safety properties of the Resonate spec's promises, in Verus.
//!
//! The model is `tests/resonate/spec.rs`, transcribed: the same state, the same
//! branches, with Verus's maps and sequences in place of `HashedMap` and
//! `String`. The transcription is checked by eye, as `certify` is against its
//! Lean copy; the properties are proved about this copy.
//!
//! Property 1, for every promise:
//!
//!     created_at <= timeout_at, and if settled, created_at <= settled_at <= timeout_at
//!
//! Proved here for `promise_create`: every promise it creates has the property,
//! the record it answers with has it, and it keeps the property for every
//! promise that already had it.

use vstd::prelude::*;

verus! {

pub type Time = u64;

pub type Id = Seq<char>;

pub type Data = Seq<char>;

// ------------------------------------------------------------------- state

pub enum PState {
    Pending,
    Resolved,
    Rejected,
    Canceled,
    TimedOut,
}

pub enum TState {
    Pending,
    Acquired,
    Suspended,
    Fulfilled,
}

pub struct Promise {
    pub state: PState,
    pub value: Option<Data>,
    pub param: Option<Data>,
    pub timeout_at: Time,
    pub created_at: Time,
    pub settled_at: Option<Time>,
    pub target: bool,
    pub external_tag: bool,
    pub timer_tag: bool,
    /// Awaiter ids to resume when this promise settles.
    pub callbacks: Set<Id>,
}

pub struct Task {
    pub state: TState,
    pub version: u32,
    pub pid: Option<Data>,
    pub ttl: Option<Time>,
    pub acquired_at: Time,
}

pub struct Server {
    /// The server's clock.
    pub now: Time,
    pub promises: Map<Id, Promise>,
    pub tasks: Map<Id, Task>,
}

// -------------------------------------------------------- requests, answers

pub struct Create {
    pub id: Id,
    pub timeout_at: Time,
    pub data: Option<Data>,
    pub external: bool,
    pub target: bool,
    pub timer: bool,
}

pub struct PromiseRec {
    pub id: Id,
    pub state: PState,
    pub param: Option<Data>,
    pub value: Option<Data>,
    pub timeout_at: Time,
    pub created_at: Time,
    pub settled_at: Option<Time>,
    /// (target, external, timer) tags.
    pub tags: (bool, bool, bool),
}

pub enum Response {
    Status(u16),
    Promise(PromiseRec),
}

pub enum Dispatch {
    Execute { id: Id, version: u32 },
}

/// One outcome of a request: as `ExternalOutcome`, with the work it starts
/// written out (a timer at a time, on a set of ids).
pub struct Outcome {
    pub res: Response,
    pub next: Server,
    pub timers: Seq<(Time, Set<Id>)>,
    pub send: Seq<Dispatch>,
}

pub open spec fn prec(id: Id, p: Promise) -> PromiseRec {
    PromiseRec {
        id,
        state: p.state,
        param: p.param,
        value: p.value,
        timeout_at: p.timeout_at,
        created_at: p.created_at,
        settled_at: p.settled_at,
        tags: (p.target, p.external_tag, p.timer_tag),
    }
}

pub open spec fn status(code: u16, s: Server) -> Outcome {
    Outcome { res: Response::Status(code), next: s, timers: seq![], send: seq![] }
}

pub open spec fn echo(res: Response, s: Server) -> Outcome {
    Outcome { res, next: s, timers: seq![], send: seq![] }
}

// --------------------------------------------------------- promise_create

/// `Resonate::promise_create`, branch by branch.
pub open spec fn promise_create(req: Create, s: Server) -> Outcome {
    let now = s.now;
    if req.timer && req.target {
        status(400, s)  // P-02: timer with target is malformed
    } else if s.promises.contains_key(req.id) {
        echo(Response::Promise(prec(req.id, s.promises[req.id])), s)  // P-02: re-create echoes
    } else {
        let live = req.timeout_at > now;
        let born = if live {
            PState::Pending
        } else if req.timer {
            PState::Resolved
        } else {
            PState::TimedOut
        };
        let p = Promise {
            state: born,
            value: None,
            param: req.data,
            timeout_at: req.timeout_at,
            created_at: if live { now } else { req.timeout_at },
            settled_at: if live { None } else { Some(req.timeout_at) },
            target: req.target,
            external_tag: req.external,
            timer_tag: req.timer,
            callbacks: Set::empty(),
        };
        let tasks = if req.target {
            let state = if live { TState::Pending } else { TState::Fulfilled };
            s.tasks.insert(req.id, Task { state, version: 0, pid: None, ttl: None, acquired_at: 0 })
        } else {
            s.tasks
        };
        let next = Server { promises: s.promises.insert(req.id, p), tasks, ..s };
        // A live targeted promise's task is runnable: the server dispatches it.
        let send = if live && req.target { seq![Dispatch::Execute { id: req.id, version: 0 }] } else { seq![] };
        let timers = if live { seq![(req.timeout_at, set![req.id])] } else { seq![] };
        Outcome { res: Response::Promise(prec(req.id, p)), next, timers, send }
    }
}

// ------------------------------------------------------------- property 1

/// created_at <= timeout_at, and if settled, created_at <= settled_at <= timeout_at.
pub open spec fn times_ok(created_at: Time, settled_at: Option<Time>, timeout_at: Time) -> bool {
    created_at <= timeout_at && match settled_at {
        Some(t) => created_at <= t && t <= timeout_at,
        None => true,
    }
}

pub open spec fn promise_ok(p: Promise) -> bool {
    times_ok(p.created_at, p.settled_at, p.timeout_at)
}

pub open spec fn server_ok(s: Server) -> bool {
    forall|id: Id| #[trigger] s.promises.contains_key(id) ==> promise_ok(s.promises[id])
}

/// A promise `promise_create` creates has the property, whatever the request
/// and the state.
pub proof fn create_makes_ok_promises(req: Create, s: Server)
    ensures
        !s.promises.contains_key(req.id) && promise_create(req, s).next.promises.contains_key(req.id)
            ==> promise_ok(promise_create(req, s).next.promises[req.id]),
{
}

/// The record `promise_create` answers with has the property, if the promise
/// it describes had it: a fresh one always does.
pub proof fn create_answers_ok_records(req: Create, s: Server)
    requires
        server_ok(s),
    ensures
        match promise_create(req, s).res {
            Response::Promise(r) => times_ok(r.created_at, r.settled_at, r.timeout_at),
            Response::Status(_) => true,
        },
{
    if !(req.timer && req.target) && s.promises.contains_key(req.id) {
        assert(promise_ok(s.promises[req.id]));
    }
}

/// `promise_create` keeps the property for every promise.
pub proof fn create_keeps_ok(req: Create, s: Server)
    requires
        server_ok(s),
    ensures
        server_ok(promise_create(req, s).next),
{
    let n = promise_create(req, s).next;
    assert forall|id: Id| #[trigger] n.promises.contains_key(id) implies promise_ok(n.promises[id]) by {
        if id != req.id {
            assert(s.promises.contains_key(id));
        }
    }
}

} // verus!
