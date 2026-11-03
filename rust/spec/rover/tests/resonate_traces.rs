//! Traces ported from the C# specification tests `Tests/ExampleTraces.cs` and
//! `Tests/LeaseAndTimeoutTests.cs`. There is no server here, so each step asks the
//! spec which responses it allows, checks that the one the C# trace expects is
//! among them, and feeds it back as the observation.

#[path = "common/certified.rs"]
mod certified;

use certified::Certified;
use echod_rover::{CallId, Checker, Config, Engine, Event, Grouped, Keyed, Time};
use echod_abstract::types::*;
use echod_abstract::*;

/// Checked twice: with partitions, and in one factor with certificates, which
/// must back everything it accepts.
struct Trace {
    c: Checker<Grouped<Resonate>>,
    shadow: Certified<Keyed<Resonate>>,
    next: CallId,
}

impl Trace {
    /// Starts with the server's clock at `now`.
    fn new(now: Time) -> Self {
        Trace::with(Resonate::default(), now)
    }

    /// Starts with the server's clock at `now`, against `model`.
    fn with(model: Resonate, now: Time) -> Self {
        let shadow = Config { certify: true, ..Config::default() };
        let mut t = Trace {
            c: Checker::with_partitions(Resonate { ..model }, Server::default(), Config::default()),
            shadow: Certified(Checker::with_footprints(model, Server::default(), shadow)),
            next: 0,
        };
        t.tick(now);
        t
    }

    #[track_caller]
    fn invoke(&mut self, call: CallId, op: Request) {
        self.c.invoke(call, op.clone()).unwrap();
        self.shadow.invoke(call, op).unwrap();
    }

    #[track_caller]
    fn ret(&mut self, call: CallId, res: Response) {
        self.c.ret(call, res.clone()).unwrap();
        self.shadow.ret(call, res).unwrap();
    }

    fn id(&mut self) -> CallId {
        self.next += 1;
        self.next
    }

    /// Calls `op` and answers it with an allowed response matching `want`.
    #[track_caller]
    fn step(&mut self, label: &str, op: Request, want: impl Fn(&Response) -> bool) -> Response {
        let allowed = self.c.allowed(&op);
        let Some(r) = allowed.iter().find(|r| want(r)).cloned() else {
            panic!("{label}: no allowed response matches; spec allows {allowed:#?}");
        };
        let id = self.id();
        self.c.call(id, op.clone(), r.clone()).unwrap_or_else(|v| panic!("{label}: {v}"));
        self.shadow.call(id, op, r.clone()).unwrap_or_else(|v| panic!("{label}, in one factor: {v}"));
        r
    }

    /// The model must reject `resp`.
    #[track_caller]
    fn rejects(&mut self, label: &str, op: Request, resp: Response) {
        let id = self.id();
        assert!(self.c.call(id, op.clone(), resp.clone()).is_err(), "{label}: model accepted a bogus response");
        assert!(self.shadow.call(id, op, resp).is_err(), "{label}: model accepted a bogus response in one factor");
    }

    /// The system's clock moves to `t`.
    #[track_caller]
    fn tick(&mut self, t: Time) {
        self.c.clock(t).unwrap_or_else(|v| panic!("tick {t}: {v}"));
        self.shadow.clock(t).unwrap_or_else(|v| panic!("tick {t}, in one factor: {v}"));
    }
}

// --------------------------------------------------------------- builders

fn val(data: Option<&str>) -> Value {
    Value { headers: Vec::new(), data: data.map(str::to_string) }
}

fn plain() -> Tags {
    Vec::new()
}

fn flag_tags(target: bool, external: bool, timer: bool, delay: Option<Time>) -> Tags {
    let mut tags = Vec::new();
    if delay.is_some() {
        tags.push(("resonate:delay".into(), delay.unwrap().to_string()));
    }
    if external {
        tags.push(("resonate:external".into(), "true".into()));
    }
    if target {
        tags.push(("resonate:target".into(), "sim://worker".into()));
    }
    if timer {
        tags.push(("resonate:timer".into(), "true".into()));
    }
    tags
}

fn create(id: &str, timeout_at: Time, data: &str) -> PromiseCreateReq {
    PromiseCreateReq { id: id.into(), timeout_at, param: val(Some(data)), tags: plain() }
}

/// Builders for a create request.
trait CreateExt {
    fn external(self) -> Self;
    fn target(self) -> Self;
    fn op(self) -> Request;
}

impl CreateExt for PromiseCreateReq {
    fn external(mut self) -> Self {
        self.tags.push(("resonate:external".into(), "true".into()));
        self
    }
    fn target(mut self) -> Self {
        self.tags.push(("resonate:target".into(), "sim://worker".into()));
        self
    }
    fn op(self) -> Request {
        Request::PromiseCreate(self)
    }
}

fn state_named(s: &str) -> PromiseState {
    match s {
        "resolved" => PromiseState::Resolved,
        "rejected" => PromiseState::Rejected,
        "rejected_canceled" => PromiseState::RejectedCanceled,
        _ => PromiseState::Pending,
    }
}

fn settle(id: &str, state: &str, data: &str) -> PromiseSettleReq {
    PromiseSettleReq { id: id.into(), state: state_named(state), value: val(Some(data)) }
}

fn get(id: &str) -> Request {
    Request::PromiseGet(PromiseGetReq { id: id.into() })
}

fn get_task(id: &str) -> Request {
    Request::TaskGet(TaskGetReq { id: id.into() })
}

fn acquire(id: &str, version: u64, pid: &str) -> Request {
    acquire_ttl(id, version, pid, 60_000)
}

fn acquire_ttl(id: &str, version: u64, pid: &str, ttl: Time) -> Request {
    Request::TaskAcquire(TaskAcquireReq { id: id.into(), version, pid: pid.into(), ttl })
}

fn fulfill(id: &str, version: u64, state: &str, data: &str) -> Request {
    Request::TaskFulfill(TaskFulfillReq { id: id.into(), version, action: settle(id, state, data) })
}

fn task_create(id: &str, timeout_at: Time, data: &str, target: bool) -> Request {
    let mut c = create(id, timeout_at, data);
    if target {
        c = c.target();
    }
    Request::TaskCreate(TaskCreateReq { pid: "worker-self".into(), ttl: 3_600_000, action: c })
}

fn fence(id: &str, version: u64, action: TaskFenceAction) -> Request {
    Request::TaskFence(TaskFenceReq { id: id.into(), version, action })
}

fn suspend(id: &str, version: u64, awaited: &[&str]) -> Request {
    Request::TaskSuspend(TaskSuspendReq {
        id: id.into(),
        version,
        actions: awaited.iter().map(|a| PromiseRegisterCallbackReq { awaited: (*a).into(), awaiter: id.into() }).collect(),
    })
}

fn callback(awaited: &str, awaiter: &str) -> Request {
    Request::PromiseRegisterCallback(PromiseRegisterCallbackReq { awaited: awaited.into(), awaiter: awaiter.into() })
}

/// The system's clock moved to `at`.
fn clock(at: Time) -> Event<Request, Response, Dispatch> {
    Event::Clock { at }
}

// ------------------------------------------------------------- predicates

fn sched(r: &Response) -> Option<&Schedule> {
    match r {
        Response::Schedule(s) => s.schedule.as_ref(),
        _ => None,
    }
}

fn status_of(r: &Response) -> u16 {
    match r {
        Response::Promise(p) => p.status,
        Response::Schedule(p) => p.status,
        Response::Status(StatusRes { status }) => *status,
        Response::TaskGet(p) => p.status,
        Response::TaskClaim(p) => p.status,
        Response::TaskFence(p) => p.status,
    }
}

fn st(code: u16) -> impl Fn(&Response) -> bool {
    move |r| status_of(r) == code
}

fn promise_record(r: &Response) -> Option<&PromiseRecord> {
    match r {
        Response::Promise(p) => p.promise.as_ref(),
        Response::TaskClaim(c) => c.promise.as_ref(),
        Response::TaskFence(f) => match &f.action {
            Some(TaskFenceInnerRes::Create(p) | TaskFenceInnerRes::Settle(p)) => p.promise.as_ref(),
            _ => None,
        },
        _ => None,
    }
}

fn promise(state: PromiseState, value: Option<&'static str>) -> impl Fn(&Response) -> bool {
    move |r| promise_record(r).is_some_and(|p| p.state == state && p.value.data.as_deref() == value)
}

/// A task record, from a get or a claim.
fn task(state: TaskState, version: u64) -> impl Fn(&Response) -> bool {
    move |r| match r {
        Response::TaskGet(t) => t.task.as_ref().is_some_and(|rec| rec.state == state && rec.version == version),
        Response::TaskClaim(t) => t.task.as_ref().is_some_and(|rec| rec.state == state && rec.version == version),
        _ => false,
    }
}

const FAR: Time = 9_000_000_000_000;

// ------------------------------------------------------------------ traces

#[test]
fn promise_layer() {
    let now = 3_000_000;
    let mut t = Trace::new(now);
    t.step("create p1 pending", create("ex:p1", now + 10_000, "hello").op(), promise(PromiseState::Pending, None));
    t.step("get p1 → pending", get("ex:p1"), promise(PromiseState::Pending, None));
    t.step("settle p1 → resolved(42)", Request::PromiseSettle(settle("ex:p1", "resolved", "42")), promise(PromiseState::Resolved, Some("42")));
    t.step("re-settle p1 → sticky", Request::PromiseSettle(settle("ex:p1", "resolved", "99")), promise(PromiseState::Resolved, Some("42")));
    t.step("create p2", create("ex:p2", now + 10_000, "A").op(), st(200));
    let r = t.step("re-create p2 → echoes A", create("ex:p2", now + 10_000, "B").op(), st(200));
    assert!(promise_record(&r).is_some_and(|p| p.param.data.as_deref() == Some("A")));
    t.step("get missing → 404", get("ex:ghost"), st(404));
    t.step("create pc", create("ex:pc", now + 10_000, "z").op(), st(200));
    t.step("cancel pc", Request::PromiseSettle(settle("ex:pc", "rejected_canceled", "gone")), promise(PromiseState::RejectedCanceled, Some("gone")));
    t.step("re-settle cancelled → sticky", Request::PromiseSettle(settle("ex:pc", "resolved", "x")), promise(PromiseState::RejectedCanceled, Some("gone")));
    t.step("settle invalid state → 400", Request::PromiseSettle(settle("ex:pc", "bogus", "x")), st(400));

    let Response::Promise(real) = t.c.allowed(&get("ex:p1")).remove(0) else { panic!() };
    let mut wrong = real.clone();
    wrong.promise.as_mut().unwrap().value = val(Some("999"));
    t.rejects("get p1 claiming 999", get("ex:p1"), Response::Promise(wrong));
    let mut pending = real;
    pending.promise.as_mut().unwrap().state = PromiseState::Pending;
    t.rejects("get p1 claiming pending", get("ex:p1"), Response::Promise(pending));

    t.step("create p3 (5s)", create("ex:p3", now + 5_000, "x").op(), st(200));
    t.tick(now + 6_000);
    // C#: "(pending|timedout) nondeterministic". Here the deadline is a timer, so it is decided.
    t.step("get p3 → timed out", get("ex:p3"), promise(PromiseState::RejectedTimedout, None));
    let Response::Promise(mut p) = t.c.allowed(&get("ex:p3")).remove(0) else { panic!() };
    let rec = p.promise.as_mut().unwrap();
    rec.state = PromiseState::Pending;
    rec.settled_at = None;
    let stale = Response::Promise(p);
    t.rejects("get p3 → pending after its deadline", get("ex:p3"), stale);
}

#[test]
fn task_layer() {
    let now = 3_000_000;
    let mut t = Trace::new(now);
    t.step("create t1 +target", create("ex:t1", now + 100_000, "work").target().op(), st(200));
    t.step("acquire t1 v0 → v1", acquire("ex:t1", 0, "worker-1"), task(TaskState::Acquired, 1));
    t.step("acquire t1 v0 again → 409", acquire("ex:t1", 0, "worker-2"), st(409));
    t.step("fulfill t1 v1", fulfill("ex:t1", 1, "resolved", "done"), promise(PromiseState::Resolved, Some("done")));
    t.step("get t1 → resolved", get("ex:t1"), promise(PromiseState::Resolved, Some("done")));

    t.step("create t2 +target", create("ex:t2", now + 100_000, "w").target().op(), st(200));
    t.step("acquire t2 → v1", acquire("ex:t2", 0, "worker-1"), task(TaskState::Acquired, 1));
    t.step("release t2 v1", Request::TaskRelease(TaskReleaseReq { id: "ex:t2".into(), version: 1 }), st(200));
    t.step("stale fulfill → 409", fulfill("ex:t2", 1, "resolved", "zombie"), st(409));
    t.step("get t2 → still pending", get("ex:t2"), promise(PromiseState::Pending, None));
    t.step("acquire wrong version → 409", acquire("ex:t2", 9, "worker-1"), st(409));
    t.step("acquire missing → 404", acquire("ex:ghostTask", 0, "worker-1"), st(404));

    let tc = |target| task_create("ex:tc1", now + 100_000, "self", target);
    t.step("task.create tc1 → acquired v1", tc(true), |r| matches!(r, Response::TaskClaim(c) if c.task.as_ref().is_some_and(|t| t.version == 1)));
    t.step("task.create tc1 dup → 409", tc(true), st(409));
    t.step("task.create no-target → 400", tc(false), st(400));
    t.step("fulfill tc1", fulfill("ex:tc1", 1, "resolved", "ok"), st(200));
    t.step("create plain p1", create("ex:p1", now + 100_000, "p").op(), st(200));
    let over = task_create("ex:p1", now + 100_000, "", true);
    t.step("task.create over plain promise → 422", over, st(422));
}

#[test]
fn fence_layer() {
    let now = 3_000_000;
    let mut t = Trace::new(now);
    t.step("create fp +target", create("ex:fp", now + 100_000, "w").target().op(), st(200));
    t.step("acquire fp → v1", acquire("ex:fp", 0, "worker-1"), task(TaskState::Acquired, 1));
    t.step("create fchild", create("ex:fchild", now + 100_000, "c").op(), st(200));
    t.step("fence own id → 400", fence("ex:fp", 1, TaskFenceAction::Settle(settle("ex:fp", "resolved", "x"))), st(400));
    t.step("fence wrong version → 409", fence("ex:fp", 9, TaskFenceAction::Settle(settle("ex:fchild", "resolved", "x"))), st(409));
    t.step("fence settles fchild", fence("ex:fp", 1, TaskFenceAction::Settle(settle("ex:fchild", "resolved", "sealed"))), st(200));
    t.step("get fchild → sealed", get("ex:fchild"), promise(PromiseState::Resolved, Some("sealed")));
    t.step("fence-create fnew", fence("ex:fp", 1, TaskFenceAction::Create(create("ex:fnew", now + 100_000, "kid"))), promise(PromiseState::Pending, None));
    t.step("fence-create past deadline → born timed out", fence("ex:fp", 1, TaskFenceAction::Create(create("ex:fexp", now - 1, "old"))), promise(PromiseState::RejectedTimedout, None));
    t.step("fence-create +target", fence("ex:fp", 1, TaskFenceAction::Create(create("ex:ftask", now + 100_000, "w").target())), st(200));
    t.step("acquire ftask → v1", acquire("ex:ftask", 0, "worker-1"), task(TaskState::Acquired, 1));
    t.step("release fp", Request::TaskRelease(TaskReleaseReq { id: "ex:fp".into(), version: 1 }), st(200));
    t.step("create fchild2", create("ex:fchild2", now + 100_000, "c").op(), st(200));
    t.step("stale fence → 409", fence("ex:fp", 1, TaskFenceAction::Settle(settle("ex:fchild2", "resolved", "late"))), st(409));
    t.step("stale fence-create → 409", fence("ex:fp", 1, TaskFenceAction::Create(create("ex:fzomb", now + 100_000, "z"))), st(409));
    t.step("fchild2 untouched", get("ex:fchild2"), promise(PromiseState::Pending, None));
    t.step("fzomb not created", get("ex:fzomb"), st(404));
}

#[test]
fn callback_layer() {
    let now = 3_000_000;
    let mut t = Trace::new(now);
    t.step("create t1 +target", create("ex:t1", now + 100_000, "w").target().op(), st(200));
    t.step("create awaited (external)", create("ex:awaited", now + 100_000, "x").external().op(), st(200));
    t.step("register_callback pending → 200", callback("ex:awaited", "ex:t1"), promise(PromiseState::Pending, None));
    t.step("register_callback missing → 404", callback("ex:ghost", "ex:t1"), st(404));
    t.step("create internal p2", create("ex:p2", now + 100_000, "x").op(), st(200));
    t.step("register_callback internal → 422", callback("ex:p2", "ex:t1"), st(422));
    t.step("create other:x", create("other:x", now + 100_000, "x").external().op(), st(200));
    t.step("cross-origin → 400", callback("other:x", "ex:t1"), st(400));
    let listen = |a: &str| Request::PromiseRegisterListener(PromiseRegisterListenerReq { awaited: "ex:awaited".into(), address: a.into() });
    t.step("listener http → 200", listen("http://localhost/cb"), st(200));
    t.step("listener poll://bad → 200", listen("poll://bad"), st(200));
    t.step("listener not a url → 400", listen("not a url"), st(400));

    t.step("create root +target", create("ex:root", now + 100_000, "r").target().op(), st(200));
    t.step("acquire root → v1", acquire("ex:root", 0, "worker-1"), task(TaskState::Acquired, 1));
    t.step("suspend root on awaited → 200", suspend("ex:root", 1, &["ex:awaited"]), st(200));
    t.step("task.get root → suspended", get_task("ex:root"), task(TaskState::Suspended, 1));
    t.step("suspend foreign → 400", suspend("ex:root", 1, &["other:x"]), st(400));
    t.step("settle awaited → arms resume", Request::PromiseSettle(settle("ex:awaited", "resolved", "v")), st(200));
    // C# polls until the resume lands; this is the poll that sees it.
    t.step("task.get root → pending (resumed)", get_task("ex:root"), task(TaskState::Pending, 1));
    t.step("re-acquire root v1 → v2", acquire("ex:root", 1, "worker-1"), task(TaskState::Acquired, 2));

    t.step("create done", create("ex:done", now + 100_000, "d").external().op(), st(200));
    t.step("settle done", Request::PromiseSettle(settle("ex:done", "resolved", "d")), st(200));
    t.step("create root2", create("ex:root2", now + 100_000, "r").target().op(), st(200));
    t.step("acquire root2", acquire("ex:root2", 0, "worker-1"), task(TaskState::Acquired, 1));
    t.step("suspend on settled → 300", suspend("ex:root2", 1, &["ex:done"]), st(300));
}

#[test]
fn resume_may_lag_the_settle() {
    let now = 3_000_000;
    let mut t = Trace::new(now);
    t.step("create a", create("ex:a", FAR, "x").external().op(), st(200));
    t.step("create r", create("ex:r", FAR, "r").target().op(), st(200));
    t.step("acquire r", acquire("ex:r", 0, "w"), st(200));
    t.step("suspend r on a", suspend("ex:r", 1, &["ex:a"]), st(200));
    t.step("settle a", Request::PromiseSettle(settle("ex:a", "resolved", "v")), st(200));
    // The resume is background work: right after the settle, either answer is fine.
    let seen = t.c.allowed(&get_task("ex:r"));
    assert!(seen.iter().any(task(TaskState::Suspended, 1)) && seen.iter().any(task(TaskState::Pending, 1)), "{seen:?}");
}

#[test]
fn lease_and_heartbeat() {
    let mut t = Trace::new(1_000_000);
    t.step("create L", create("L", FAR, "w").target().op(), st(200));
    t.step("acquire L ttl 5000", acquire_ttl("L", 0, "wA", 5_000), task(TaskState::Acquired, 1));
    t.tick(1_004_000);
    t.step("acquire while held → 409", acquire_ttl("L", 1, "wB", 5_000), st(409));
    t.tick(1_005_000);
    // C#: "acquired OR pending (reclaim is a choice)". Here the lease check is
    // a timer: at the lease end the task is reclaimed, so only pending.
    let seen = t.c.allowed(&get_task("L"));
    assert!(seen.iter().all(task(TaskState::Pending, 1)) && !seen.is_empty(), "{seen:?}");
    t.step("re-acquire after reclaim → v2", acquire_ttl("L", 1, "wB", 5_000), task(TaskState::Acquired, 2));

    t.step("create H", create("H", FAR, "w").target().op(), st(200));
    t.step("acquire H ttl 5000", acquire_ttl("H", 0, "wH", 5_000), task(TaskState::Acquired, 1));
    t.tick(1_008_000);
    let hb = |pid: &str, version| Request::TaskHeartbeat(TaskHeartbeatReq { pid: pid.into(), tasks: vec![TaskRef { id: "H".into(), version }] });
    t.step("heartbeat H → lease to 1013000", hb("wH", 1), st(200));
    t.tick(1_012_000);
    t.step("acquire H → 409 (heartbeat kept it)", acquire_ttl("H", 1, "wX", 5_000), st(409));
    t.step("heartbeat wrong pid → 200, no extension", hb("WRONG", 1), st(200));
    t.tick(1_014_000);
    t.step("re-acquire H after reclaim → v2", acquire_ttl("H", 1, "wX", 5_000), task(TaskState::Acquired, 2));
    t.step("heartbeat wrong version → 200, no extension", hb("wX", 1), st(200));
    t.tick(1_019_000);
    t.step("re-acquire H v2 → v3", acquire_ttl("H", 2, "wY", 5_000), task(TaskState::Acquired, 3));
}

// ----------------------------------------------- what the new model adds

#[test]
fn get_in_flight_across_a_deadline_may_see_pending() {
    let now = 1_000_000;
    let mut t = Trace::new(now);
    t.step("create p", create("p", now + 1_000, "x").op(), st(200));
    let Response::Promise(pending) = t.c.allowed(&get("p")).remove(0) else { panic!() };
    t.invoke(100, get("p"));
    t.tick(now + 5_000);
    t.ret(100, Response::Promise(pending)); // linearized before the deadline
    t.step("now it is timed out", get("p"), promise(PromiseState::RejectedTimedout, None));
}

#[test]
fn unanswered_settle_may_land_late() {
    let now = 1_000_000;
    let mut t = Trace::new(now);
    t.step("create p", create("p", FAR, "x").op(), st(200));
    t.invoke(100, Request::PromiseSettle(settle("p", "resolved", "v"))); // never answered
    t.step("read misses it", get("p"), promise(PromiseState::Pending, None));
    t.step("read sees it", get("p"), promise(PromiseState::Resolved, Some("v")));
}

#[test]
fn independent_promises_keep_the_profile_narrow() {
    let now = 1_000_000;
    let mut t = Trace::new(now);
    for i in 0..50 {
        t.step("create", create(&format!("p{i}"), now + 1_000 + i, "x").op(), st(200));
    }
    let mut pending = Vec::new();
    for i in 0..50 {
        pending.push(t.c.allowed(&get(&format!("p{i}"))).remove(0));
        t.invoke(1_000 + i, get(&format!("p{i}")));
    }
    t.tick(now + 2_000); // passes 50 deadlines with 50 reads in flight
    assert_eq!(t.c.profile().len(), 1);
    // Each read may have answered before its deadline or after: both are accepted.
    for (i, before) in pending.into_iter().enumerate() {
        let i = i as u64;
        let resp = if i.is_multiple_of(2) {
            before
        } else {
            let Response::Promise(mut p) = before else { panic!() };
            let rec = p.promise.as_mut().unwrap();
            let timeout_at = rec.timeout_at;
            rec.state = PromiseState::RejectedTimedout;
            rec.settled_at = Some(timeout_at);
            Response::Promise(p)
        };
        t.ret(1_000 + i, resp);
    }
    println!("{:?}", t.c.stats);
    assert_eq!(t.c.stats.max_width, 1);
}

#[test]
#[ignore = "prints a violation, for reading"]
fn show_a_violation() {
    let now = 1_000_000;
    let mut t = Trace::new(now);
    t.step("create +target", create("ex:t", FAR, "w").target().op(), st(200));
    t.step("create other", create("ex:o", FAR, "w").op(), st(200));
    let id = t.id();
    let v = t.c.call(id, acquire("ex:t", 0, "w"), Response::Status(StatusRes { status: 409 })).unwrap_err();
    println!("{v}");
}

// ------------------------------------------------------------- partitions

/// Per origin: a promise with a deadline and a settle that is never answered.
/// Across the deadline each origin has two explanations (the settle landed in
/// time, or the promise timed out). Kept together that is 2^origins candidates.
fn settles_cfg() -> Config {
    Config { max_width: 1 << 16, max_explore: 5_000, ..Config::default() }
}

fn unanswered_settles<E: Engine<M = Resonate>>(
    mut c: Checker<E>,
    origins: u64,
) -> Result<Checker<E>, echod_rover::Violation> {
    let now = 1_000_000;
    c.clock(now)?;
    for o in 0..origins {
        let id = format!("o{o}:p");
        let p = PromiseCreateReq { id: id.clone(), timeout_at: now + 1_000, param: val(None), tags: plain() };
        let r = c.allowed(&Request::PromiseCreate(p.clone())).remove(0);
        c.call(o, Request::PromiseCreate(p), r)?;
        c.invoke(1_000 + o, Request::PromiseSettle(PromiseSettleReq { id, state: PromiseState::Resolved, value: val(None) }))?;
    }
    c.clock(now + 2_000)?;
    Ok(c)
}

#[test]
fn partitions_keep_independent_origins_apart() {
    let t0 = std::time::Instant::now();
    let mut c = unanswered_settles(Checker::with_partitions(Resonate::default(), Server::default(), settles_cfg()), 20).unwrap();
    println!("partitioned: {:?}, width {}, {:?}", c.stats, c.width(), t0.elapsed());
    assert_eq!(c.factors().len(), 20);
    assert!(c.factors().iter().all(|f| f.nodes.len() == 2));
    assert_eq!(c.width(), 1 << 20);
    // Each origin resolves on its own read.
    for o in 0..20u64 {
        let id = format!("o{o}:p");
        let want = if o % 3 == 0 { PromiseState::Resolved } else { PromiseState::RejectedTimedout };
        let r = c.allowed(&Request::PromiseGet(PromiseGetReq { id: id.clone() })).into_iter().find(promise(want, None)).unwrap();
        c.call(5_000 + o, Request::PromiseGet(PromiseGetReq { id: id }), r).unwrap();
    }
    assert!(c.factors().iter().all(|f| f.nodes.len() == 1));

    let t0 = std::time::Instant::now();
    let v = unanswered_settles(Checker::with_footprints(Resonate::default(), Server::default(), settles_cfg()), 20)
        .err()
        .expect("one profile of 2^20 candidates");
    println!("unpartitioned: {} {:?}", v.reason, t0.elapsed());
}

#[test]
fn only_a_detached_create_crosses_origins() {
    let now = 1_000_000;
    let mut t = Trace::new(now);
    t.step("create a:t", create("a:t", FAR, "w").target().op(), st(200));
    t.step("acquire a:t", acquire("a:t", 0, "w"), st(200));
    t.step("create b:p", create("b:p", FAR, "x").external().op(), st(200));
    t.step("create c:p", create("c:p", FAR, "x").op(), st(200));
    assert_eq!(t.c.factors().len(), 3);

    // Refused on the ids alone: no merge.
    t.step("fence-settle across origins → 400", fence("a:t", 1, TaskFenceAction::Settle(settle("b:p", "resolved", "v"))), st(400));
    t.step("callback across origins → 400", callback("b:p", "a:t"), st(400));
    t.step("suspend across origins → 400", suspend("a:t", 1, &["b:p"]), st(400));
    assert_eq!((t.c.factors().len(), t.c.stats.merges), (3, 0));

    // A detached workflow: a:t creates d:root. The two origins merge for the
    // request and split again once it has returned.
    t.step("detached create d:root", fence("a:t", 1, TaskFenceAction::Create(create("d:root", FAR, "w").target())), promise(PromiseState::Pending, None));
    assert_eq!(t.c.stats.splits, 1);
    assert_eq!(t.c.factors().len(), 4, "a, b, c and d, each on its own");
    t.step("d:root is its own workflow", acquire("d:root", 0, "w2"), task(TaskState::Acquired, 1));

    // Unanswered, the detached create keeps the two origins together until it is resolved.
    let calls = t.next;
    t.invoke(calls + 1, fence("a:t", 1, TaskFenceAction::Create(create("e:root", FAR, "w"))));
    assert_eq!(t.c.factors().len(), 4, "a and e merged");
    t.next += 1;
    t.step("e:root exists, so the create landed", get("e:root"), promise(PromiseState::Pending, None));
    assert_eq!(t.c.factors().len(), 4, "the unanswered fence still links a and e");
}

/// A small deterministic generator, so the differential test needs no crates.
struct Lcg(u64);

impl Lcg {
    fn next(&mut self, n: u64) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        (self.0 >> 33) % n
    }
}

/// Partitioned and unpartitioned checkers must agree on every verdict.
#[test]
fn partitioning_never_changes_a_verdict() {
    let ids = ["a:1", "a:2", "b:1", "b:2", "c:1"];
    for seed in 1..=40 {
        let mut rng = Lcg(seed);
        let now = 1_000_000;
        let mut on = Checker::with_partitions(Resonate::default(), Server::default(), Config::default());
        let mut off = Checker::with_footprints(Resonate::default(), Server::default(), Config::default());
        let mut open: Vec<(CallId, Request)> = Vec::new();
        let mut at = now;
        let mut all = Vec::new();
        let mut kept = Vec::new();
        for call in 0..60u64 {
            let id = ids[rng.next(ids.len() as u64) as usize].to_string();
            let other = ids[rng.next(ids.len() as u64) as usize].to_string();
            let op = match rng.next(13) {
                0 => Request::PromiseCreate(PromiseCreateReq {
                    id,
                    timeout_at: at + 500 + rng.next(3_000),
                    param: val(None),
                    tags: flag_tags(rng.next(2) == 0, rng.next(2) == 0, false, None),
                }),
                1 => Request::PromiseSettle(PromiseSettleReq { id, state: PromiseState::Resolved, value: val(None) }),
                2 => Request::TaskAcquire(TaskAcquireReq { id, version: rng.next(3), pid: "w".into(), ttl: 1_000 }),
                3 => {
                    let version = rng.next(3);
                    Request::TaskFulfill(TaskFulfillReq { id: id.clone(), version, action: PromiseSettleReq { id, state: PromiseState::Resolved, value: val(None) } })
                }
                4 => Request::TaskSuspend(TaskSuspendReq {
                    id: id.clone(),
                    version: rng.next(3),
                    actions: vec![PromiseRegisterCallbackReq { awaited: other, awaiter: id }],
                }),
                5 => Request::PromiseRegisterCallback(PromiseRegisterCallbackReq { awaited: id, awaiter: other }),
                6 => Request::TaskFence(TaskFenceReq {
                    id,
                    version: rng.next(3),
                    action: TaskFenceAction::Settle(PromiseSettleReq { id: other, state: PromiseState::Resolved, value: val(None) }),
                }),
                7 if rng.next(2) == 0 => Request::TaskFence(TaskFenceReq {
                    id,
                    version: rng.next(3),
                    action: TaskFenceAction::Create(PromiseCreateReq {
                        id: format!("{other}x"),
                        timeout_at: at + rng.next(3_000),
                        param: val(None),
                        tags: flag_tags(rng.next(2) == 0, false, false, None),
                    }),
                }),
                7 => Request::TaskGet(TaskGetReq { id }),
                8 => Request::TaskHalt(TaskHaltReq { id }),
                9 => Request::TaskContinue(TaskContinueReq { id }),
                10 => {
                    let cron = "* * * * * *";
                    Request::ScheduleCreate(ScheduleCreateReq {
                        id: format!("s{}", &id[..1]),
                        cron: cron.into(),
                        promise_id: format!("{}:{{{{.id}}}}.{{{{.timestamp}}}}", &id[..1]),
                        promise_timeout: rng.next(3_000),
                        promise_param: val(None),
                        promise_tags: flag_tags(true, false, false, None),
                        next_run_at: next_cron(cron, at),
                    })
                }
                11 => Request::ScheduleDelete(ScheduleDeleteReq { id: format!("s{}", &id[..1]) }),
                _ => Request::PromiseGet(PromiseGetReq { id }),
            };
            let mut events = if call == 0 { vec![clock(now)] } else { Vec::new() };
            events.push(Event::Invoke { call, req: op.clone() });
            match rng.next(4) {
                0 => open.push((call, op.clone())), // answered later, or never
                _ => {
                    let allowed = off.allowed(&op);
                    let resp = if allowed.is_empty() || rng.next(8) == 0 {
                        Response::Status(StatusRes { status: (500 + rng.next(3)) as u16 }) // bogus
                    } else {
                        allowed[rng.next(allowed.len() as u64) as usize].clone()
                    };
                    events.push(Event::Return { call, res: resp });
                }
            }
            if rng.next(5) == 0 {
                at += 1 + rng.next(2_000); // the clock moves
                events.push(clock(at));
            }
            if !open.is_empty() && rng.next(4) == 0 {
                // A late answer: whatever the op would get if called now. Valid or
                // not, both checkers must agree.
                let (c, op) = open.swap_remove(rng.next(open.len() as u64) as usize);
                let resp = off.allowed(&op).first().cloned().unwrap_or(Response::Status(StatusRes { status: 404 }));
                events.push(Event::Return { call: c, res: resp });
            }
            all.extend(events.iter().cloned());
            for e in events {
                // A rejected event leaves both checkers as they were, so they stay comparable.
                let a = on.observe(e.clone()).is_ok();
                let b = off.observe(e.clone()).is_ok();
                if b {
                    kept.push(e.clone());
                }
                // Property 1 (proved for promise_create in src/exec.rs),
                // checked here on the Rust spec itself, for every candidate state.
                for s in off.states() {
                    for (id, p) in s.promises.iter() {
                        let ok = p.created_at <= p.timeout_at
                            && p.settled_at.is_none_or(|t| p.created_at <= t && t <= p.timeout_at);
                        assert!(ok, "seed {seed}: promise {id} breaks created_at <= settled_at <= timeout_at: {p:?}");
                    }
                }
                assert_eq!(a, b, "seed {seed}: partitioned={a} unpartitioned={b} on {e:?}");
            }
        }
        // The whole history (bogus responses make it invalid), online and depth
        // first: the same verdict.
        let online = Checker::with_footprints(Resonate::default(), Server::default(), Config::default()).check_history(&all).is_ok();
        let mut dfs = Checker::with_footprints(Resonate::default(), Server::default(), Config { certify: true, ..Config::default() });
        let deep = dfs.check_complete(&all).is_ok();
        assert_eq!(online, deep, "seed {seed}: online={online} depth-first={deep}");
        if deep {
            dfs.certified().unwrap_or_else(|v| panic!("seed {seed}: {v}"));
        }
        let mut split = Checker::with_partitions(Resonate::default(), Server::default(), Config::default());
        assert_eq!(split.check_complete(&all).is_ok(), deep, "seed {seed}: depth first by partition");
        // What the online checker accepted, event by event, is a valid history:
        // depth first must accept it too, and certify it.
        let mut dfs = Checker::with_footprints(Resonate::default(), Server::default(), Config { certify: true, ..Config::default() });
        dfs.check_complete(&kept).unwrap_or_else(|v| panic!("seed {seed}: accepted events rejected depth first: {v}"));
        dfs.certified().unwrap_or_else(|v| panic!("seed {seed}: {v}"));
        let mut split = Checker::with_partitions(Resonate::default(), Server::default(), Config::default());
        split.check_complete(&kept).unwrap_or_else(|v| panic!("seed {seed}: by partition: {v}"));
    }
}

// ------------------------------------------------------- server-sent messages

fn execute(id: &str, version: u64) -> Dispatch {
    Dispatch::Execute { id: id.into(), version }
}

#[test]
fn a_new_task_is_dispatched_once() {
    let mut t = Trace::new(1_000_000);
    t.step("create t +target", create("ex:t", FAR, "w").target().op(), st(200));
    t.c.receive(execute("ex:t", 0)).unwrap();
    assert!(t.c.receive(execute("ex:t", 0)).is_err(), "sent once, received once");
}

#[test]
fn a_message_nobody_sent_is_rejected() {
    let mut t = Trace::new(1_000_000);
    assert!(t.c.receive(execute("ex:t", 0)).is_err(), "no such task");
    t.step("create t +target", create("ex:t", FAR, "w").target().op(), st(200));
    assert!(t.c.receive(execute("ex:t", 3)).is_err(), "wrong version");
}

#[test]
fn a_message_may_never_arrive() {
    let mut t = Trace::new(1_000_000);
    t.step("create t +target", create("ex:t", FAR, "w").target().op(), st(200));
    // The execute was sent; nobody has to receive it.
    t.step("acquire t", acquire("ex:t", 0, "w"), task(TaskState::Acquired, 1));
}

#[test]
fn a_resume_dispatches_the_waiting_task() {
    let mut t = Trace::new(1_000_000);
    t.step("create a", create("ex:a", FAR, "x").external().op(), st(200));
    t.step("create r +target", create("ex:r", FAR, "r").target().op(), st(200));
    t.step("acquire r", acquire("ex:r", 0, "w"), task(TaskState::Acquired, 1));
    assert!(t.c.receive(execute("ex:r", 1)).is_err(), "running, not suspended");
    t.step("suspend r on a", suspend("ex:r", 1, &["ex:a"]), st(200));
    t.step("settle a", Request::PromiseSettle(settle("ex:a", "resolved", "v")), st(200));
    // Receiving the execute forces the hidden resume, then the dispatch.
    t.c.receive(execute("ex:r", 1)).unwrap();
    assert!(t.c.all(|s| s.tasks["ex:r"].state == TaskState::Pending));
}

#[test]
fn a_reclaimed_lease_dispatches_again() {
    let mut t = Trace::new(1_000_000);
    t.step("create t +target", create("ex:t", FAR, "w").target().op(), st(200));
    t.c.receive(execute("ex:t", 0)).unwrap();
    t.step("acquire t ttl 5000", acquire_ttl("ex:t", 0, "w", 5_000), task(TaskState::Acquired, 1));
    t.tick(1_010_000);
    t.c.receive(execute("ex:t", 1)).unwrap();
}

#[test]
fn check_takes_calls_dispatches_and_clock_moves() {
    let now = 1_000_000;
    let mut t = Trace::new(now);
    let create_r = create("ex:r", now + 10_000, "r").target().op();
    let created = t.c.allowed(&create_r).remove(0); // the pending record
    let mut c = Checker::with_partitions(Resonate::default(), Server::default(), Config::default());
    let trace = vec![
        clock(now),
        Event::Invoke { call: 1, req: create_r },
        Event::Return { call: 1, res: created.clone() },
        Event::Receive { msg: execute("ex:r", 0) },
        clock(now + 20_000),
        Event::Invoke { call: 2, req: get("ex:r") },
    ];
    c.check(trace).unwrap();
    // The read was sent after the deadline: it can only see the promise timed out.
    let stale = created; // pending, as of before the deadline
    let v = c.check(vec![Event::Return { call: 2, res: stale }]).unwrap_err();
    assert_eq!(v.index, 0);
}

/// Workflow after workflow, each sending dispatches nobody receives, must not
/// multiply the explanations.
#[test]
fn workflows_keep_a_single_explanation() {
    let mut t = Trace::new(10);
    for i in 0..30 {
        let (a, x) = (format!("o:a{i}"), format!("o:x{i}"));
        t.step("create a", create(&a, FAR, "x").external().op(), st(200));
        t.step("create x", create(&x, FAR, "w").target().op(), st(200));
        t.step("acquire x", acquire(&x, 0, "p"), task(TaskState::Acquired, 1));
        t.step("suspend x", suspend(&x, 1, &[&a]), st(200));
        t.step("settle a", Request::PromiseSettle(settle(&a, "resolved", "v")), st(200));
        t.step("re-acquire x", acquire(&x, 1, "p"), task(TaskState::Acquired, 2));
        t.step("fulfill x", fulfill(&x, 2, "resolved", "ok"), st(200));
    }
    assert_eq!(t.c.stats.max_width, 1, "{:?}", t.c.stats);
}

// ------------------------------------------ what the Lean specification adds

fn unblock(address: &str, p: &PromiseRes) -> Dispatch {
    Dispatch::Unblock { address: address.into(), promise: p.promise.clone().unwrap() }
}

fn schedule(id: &str, cron: &str, template: &str, timeout: Time, tags: Tags, now: Time) -> Request {
    Request::ScheduleCreate(ScheduleCreateReq {
        id: id.into(),
        cron: cron.into(),
        promise_id: template.into(),
        promise_timeout: timeout,
        promise_param: val(Some("p")),
        promise_tags: tags,
        next_run_at: next_cron(cron, now),
    })
}

#[test]
fn halt_and_continue() {
    let mut t = Trace::new(1_000_000);
    t.step("create t +target", create("ex:t", FAR, "w").target().op(), st(200));
    t.c.receive(execute("ex:t", 0)).unwrap();
    t.step("acquire t → v1", acquire("ex:t", 0, "w"), task(TaskState::Acquired, 1));
    t.step("halt t", Request::TaskHalt(TaskHaltReq { id: "ex:t".into() }), st(200));
    t.step("task.get t → halted", get_task("ex:t"), task(TaskState::Halted, 1));
    t.step("fulfill a halted task → 409", fulfill("ex:t", 1, "resolved", "x"), st(409));
    t.step("acquire a halted task → 409", acquire("ex:t", 1, "w"), st(409));
    t.step("heartbeat a halted task → 200, nothing kept", Request::TaskHeartbeat(TaskHeartbeatReq { pid: "w".into(), tasks: vec![TaskRef { id: "ex:t".into(), version: 1 }] }), st(200));
    t.step("halt again → 200", Request::TaskHalt(TaskHaltReq { id: "ex:t".into() }), st(200));
    assert!(t.c.receive(execute("ex:t", 1)).is_err(), "a halted task is not offered");
    t.step("continue t", Request::TaskContinue(TaskContinueReq { id: "ex:t".into() }), st(200));
    t.step("task.get t → pending", get_task("ex:t"), task(TaskState::Pending, 1));
    t.c.receive(execute("ex:t", 1)).unwrap();
    t.step("continue a pending task → 409", Request::TaskContinue(TaskContinueReq { id: "ex:t".into() }), st(409));
    t.step("re-acquire t → v2", acquire("ex:t", 1, "w"), task(TaskState::Acquired, 2));
    t.step("fulfill t", fulfill("ex:t", 2, "resolved", "done"), st(200));
    t.step("halt a fulfilled task → 409", Request::TaskHalt(TaskHaltReq { id: "ex:t".into() }), st(409));
    t.step("halt missing → 404", Request::TaskHalt(TaskHaltReq { id: "ex:ghost".into() }), st(404));
    t.step("continue missing → 404", Request::TaskContinue(TaskContinueReq { id: "ex:ghost".into() }), st(404));
    t.step("create p (no task)", create("ex:p", FAR, "x").op(), st(200));
    t.step("halt a promise without a task → 404", Request::TaskHalt(TaskHaltReq { id: "ex:p".into() }), st(404));
}

#[test]
fn a_pending_task_is_offered_again_every_retry_timeout() {
    let now = 1_000_000;
    let mut t = Trace::new(now);
    t.step("create t +target", create("ex:t", FAR, "w").target().op(), st(200));
    t.c.receive(execute("ex:t", 0)).unwrap();
    assert!(t.c.receive(execute("ex:t", 0)).is_err(), "offered once so far");
    t.tick(now + 4_999);
    assert!(t.c.receive(execute("ex:t", 0)).is_err(), "not yet");
    t.tick(now + 5_000);
    t.c.receive(execute("ex:t", 0)).unwrap();
    // The retry due at +10s runs when the clock reaches +15s, and the next is
    // five seconds after it ran, not after it was due: one more offer.
    t.tick(now + 15_000);
    t.c.receive(execute("ex:t", 0)).unwrap();
    assert!(t.c.receive(execute("ex:t", 0)).is_err(), "one more offer");
    t.tick(now + 20_000);
    t.c.receive(execute("ex:t", 0)).unwrap();
    t.step("acquire t → v1", acquire("ex:t", 0, "w"), task(TaskState::Acquired, 1));
    t.tick(now + 30_000);
    assert!(t.c.receive(execute("ex:t", 0)).is_err(), "an acquired task is not offered");
}

#[test]
fn a_delayed_task_is_first_offered_at_its_delay() {
    let now = 1_000_000;
    let mut t = Trace::new(now);
    let c = PromiseCreateReq { id: "ex:d".into(), timeout_at: FAR, param: val(None), tags: flag_tags(true, false, false, Some(now + 1_000)) };
    t.step("create d +target, delayed", Request::PromiseCreate(c), promise(PromiseState::Pending, None));
    assert!(t.c.receive(execute("ex:d", 0)).is_err(), "not before its delay");
    t.tick(now + 1_000);
    t.c.receive(execute("ex:d", 0)).unwrap();
}

#[test]
fn listeners_are_told_once_when_the_promise_settles() {
    let now = 1_000_000;
    let mut t = Trace::new(now);
    t.step("create p (external)", create("ex:p", FAR, "x").external().op(), st(200));
    let listen = |a: &str| Request::PromiseRegisterListener(PromiseRegisterListenerReq { awaited: "ex:p".into(), address: a.into() });
    t.step("listener 1 → 200", listen("http://l/1"), promise(PromiseState::Pending, None));
    t.step("listener 2 → 200", listen("poll://w"), promise(PromiseState::Pending, None));
    t.step("listener 1 again → 200", listen("http://l/1"), promise(PromiseState::Pending, None));
    t.step("bad address → 400", listen("not a url"), st(400));
    t.step("create q (internal)", create("ex:q", FAR, "x").op(), st(200));
    t.step("listener on internal → 422", Request::PromiseRegisterListener(PromiseRegisterListenerReq { awaited: "ex:q".into(), address: "http://l/1".into() }), st(422));
    let Response::Promise(settled) = t.step("settle p", Request::PromiseSettle(settle("ex:p", "resolved", "v")), promise(PromiseState::Resolved, Some("v"))) else { panic!() };
    t.c.receive(unblock("http://l/1", &settled)).unwrap();
    t.c.receive(unblock("poll://w", &settled)).unwrap();
    assert!(t.c.receive(unblock("http://l/1", &settled)).is_err(), "told once");
    t.step("listener on a settled promise → 200", listen("http://l/late"), promise(PromiseState::Resolved, Some("v")));
    assert!(t.c.receive(unblock("http://l/late", &settled)).is_err(), "nothing to tell later");

    t.step("create e (external, 1s)", create("ex:e", now + 1_000, "x").external().op(), st(200));
    t.step("listener on e", Request::PromiseRegisterListener(PromiseRegisterListenerReq { awaited: "ex:e".into(), address: "http://l/e".into() }), st(200));
    t.tick(now + 1_000);
    let Response::Promise(timed_out) = t.step("e timed out", get("ex:e"), promise(PromiseState::RejectedTimedout, None)) else { panic!() };
    t.c.receive(unblock("http://l/e", &timed_out)).unwrap();
}

#[test]
fn task_create_in_every_state() {
    let now = 1_000_000;
    let mut t = Trace::new(now);
    let both = |p: PromiseState, ts: TaskState, v: u64| {
        move |r: &Response| matches!(r, Response::TaskClaim(c) if c.promise.as_ref().is_some_and(|pr| pr.state == p) && c.task.as_ref().is_some_and(|tr| tr.state == ts && tr.version == v))
    };
    t.step("task.create past its deadline → born done", task_create("ex:old", now - 1, "x", true), both(PromiseState::RejectedTimedout, TaskState::Fulfilled, 0));
    let r = t.step("task.create old again → echo", task_create("ex:old", now - 1, "x", true), both(PromiseState::RejectedTimedout, TaskState::Fulfilled, 0));
    assert!(matches!(r, Response::TaskClaim(c) if c.promise.as_ref().is_some_and(|p| p.created_at == now - 1 && p.settled_at == Some(now - 1))));
    assert!(t.c.receive(execute("ex:old", 0)).is_err(), "never offered");
    t.step("create p +target (pending)", create("ex:p", FAR, "w").target().op(), st(200));
    t.c.receive(execute("ex:p", 0)).unwrap();
    t.step("task.create over a pending task → acquired v1", task_create("ex:p", FAR, "w", true), both(PromiseState::Pending, TaskState::Acquired, 1));
    t.step("task.create over an acquired task → 409", task_create("ex:p", FAR, "w", true), st(409));
    t.step("release p", Request::TaskRelease(TaskReleaseReq { id: "ex:p".into(), version: 1 }), st(200));
    t.step("task.create over a pending task → acquired v2", task_create("ex:p", FAR, "w", true), both(PromiseState::Pending, TaskState::Acquired, 2));
    t.step("halt p", Request::TaskHalt(TaskHaltReq { id: "ex:p".into() }), st(200));
    t.step("task.create over a halted task → 409", task_create("ex:p", FAR, "w", true), st(409));
    let timer = Request::TaskCreate(TaskCreateReq { pid: "w".into(), ttl: 10, action: PromiseCreateReq { id: "ex:tt".into(), timeout_at: FAR, param: val(None), tags: flag_tags(true, false, true, None) } });
    t.step("task.create a timer → 400", timer, st(400));
}

#[test]
fn a_task_counts_what_settled_while_it_ran() {
    let now = 1_000_000;
    let mut t = Trace::new(now);
    t.step("create a", create("ex:a", FAR, "x").external().op(), st(200));
    t.step("create b", create("ex:b", FAR, "x").external().op(), st(200));
    t.step("create r +target", create("ex:r", FAR, "r").target().op(), st(200));
    t.step("acquire r → v1", acquire("ex:r", 0, "w"), task(TaskState::Acquired, 1));
    t.step("callback a → r", callback("ex:a", "ex:r"), st(200));
    t.step("callback b → r", callback("ex:b", "ex:r"), st(200));
    t.step("settle a", Request::PromiseSettle(settle("ex:a", "resolved", "v")), st(200));
    let resumes = |n: u64| move |r: &Response| matches!(r, Response::TaskGet(t) if t.task.as_ref().is_some_and(|rec| rec.resumes == n));
    t.step("task.get r → one resume noted", get_task("ex:r"), resumes(1));
    t.step("suspend r on b → 200 (clears the count)", suspend("ex:r", 1, &["ex:b"]), st(200));
    t.step("settle b", Request::PromiseSettle(settle("ex:b", "resolved", "v")), st(200));
    t.step("task.get r → pending with one resume", get_task("ex:r"), |r| matches!(r, Response::TaskGet(t) if t.task.as_ref().is_some_and(|rec| rec.state == TaskState::Pending && rec.resumes == 1)));
    t.c.receive(execute("ex:r", 1)).unwrap();
    t.step("acquire r → v2, count cleared", acquire("ex:r", 1, "w"), |r| matches!(r, Response::TaskClaim(c) if c.task.as_ref().is_some_and(|t| t.version == 2 && t.resumes == 0)));

    t.step("create c", create("ex:c", FAR, "x").external().op(), st(200));
    t.step("settle c", Request::PromiseSettle(settle("ex:c", "resolved", "v")), st(200));
    t.step("suspend r on settled c → 300", suspend("ex:r", 2, &["ex:c"]), st(300));
    t.step("task.get r → still acquired", get_task("ex:r"), task(TaskState::Acquired, 2));
}

#[test]
fn schedules_fire_on_their_cron() {
    let now = 1_000_000; // 1000 s
    let mut t = Trace::new(now);
    let tags = flag_tags(true, false, false, None);
    t.step("id with a colon → 400", schedule("ex:bad", "* * * * * *", "ex:x", 1_500, tags.clone(), now), st(400));
    t.step("promises without a target → 400", schedule("bad", "* * * * * *", "ex:x", 1_500, plain(), now), st(400));
    t.step("invalid cron → 400", schedule("bad", "bogus", "ex:x", 1_500, tags.clone(), now), st(400));
    t.step("timer with target → 400", schedule("bad", "* * * * * *", "ex:x", 1_500, flag_tags(true, false, true, None), now), st(400));
    let every_second = schedule("s", "* * * * * *", "ex:run-{{.timestamp}}", 1_500, tags.clone(), now);
    let r = t.step("create s", every_second.clone(), |r| sched(r).is_some_and(|c| c.next_run_at == 1_001_000 && c.last_run_at.is_none()));
    t.step("get s", Request::ScheduleGet(ScheduleGetReq { id: "s".into() }), |x| *x == r);
    t.step("create s again → echo", every_second, |x| *x == r);
    t.step("get missing → 404", Request::ScheduleGet(ScheduleGetReq { id: "none".into() }), st(404));
    t.step("run-1001000 not yet", get("ex:run-1001000"), st(404));
    t.tick(1_000_999);
    t.step("run-1001000 still not yet", get("ex:run-1001000"), st(404));
    t.tick(1_001_000);
    let r = t.step("run-1001000 created at its instant", get("ex:run-1001000"), promise(PromiseState::Pending, None));
    assert!(promise_record(&r).is_some_and(|p| p.created_at == 1_001_000 && p.timeout_at == 1_002_500 && p.param.data.as_deref() == Some("p")));
    t.c.receive(execute("ex:run-1001000", 0)).unwrap();
    t.step("s advanced", Request::ScheduleGet(ScheduleGetReq { id: "s".into() }), |r| sched(r).is_some_and(|c| c.last_run_at == Some(1_001_000) && c.next_run_at == 1_002_000));
    // A jump over three occurrences fires all three, each as of its instant.
    t.tick(1_004_000);
    let r = t.step("run-1002000 born in the past, already timed out", get("ex:run-1002000"), promise(PromiseState::RejectedTimedout, None));
    assert!(promise_record(&r).is_some_and(|p| p.created_at == 1_002_000 && p.settled_at == Some(1_003_500)));
    assert!(t.c.receive(execute("ex:run-1002000", 0)).is_err(), "a task born done is not offered");
    t.step("run-1003000 pending", get("ex:run-1003000"), promise(PromiseState::Pending, None));
    t.step("run-1004000 pending", get("ex:run-1004000"), promise(PromiseState::Pending, None));
    t.c.receive(execute("ex:run-1004000", 0)).unwrap();
    t.step("s advanced to 1005000", Request::ScheduleGet(ScheduleGetReq { id: "s".into() }), |r| sched(r).is_some_and(|c| c.last_run_at == Some(1_004_000) && c.next_run_at == 1_005_000));
    t.step("delete s", Request::ScheduleDelete(ScheduleDeleteReq { id: "s".into() }), st(200));
    t.step("delete s again → 404", Request::ScheduleDelete(ScheduleDeleteReq { id: "s".into() }), st(404));
    t.tick(1_006_000);
    t.step("run-1005000 never fired", get("ex:run-1005000"), st(404));

    // An occurrence whose id is taken is left alone.
    t.step("create w", schedule("w", "*/5 * * * * *", "ex:job-{{.timestamp}}", 60_000, tags, 1_006_000), |r| sched(r).is_some_and(|c| c.next_run_at == 1_010_000));
    t.step("take the next id first", create("ex:job-1010000", FAR, "mine").op(), st(200));
    t.tick(1_010_000);
    t.step("the occurrence found it", get("ex:job-1010000"), |r| promise_record(r).is_some_and(|p| p.param.data.as_deref() == Some("mine") && !p.tags.iter().any(|(k, _)| k == "resonate:target")));
    t.step("w advanced anyway", Request::ScheduleGet(ScheduleGetReq { id: "w".into() }), |r| sched(r).is_some_and(|c| c.last_run_at == Some(1_010_000) && c.next_run_at == 1_015_000));
}

/// A schedule is owed at `next_run_at`. That step records the run and queues
/// the occurrence; the occurrence then creates the promise. A read at the
/// instant sees both. `fire_within` is not a window on this step.
#[test]
fn a_schedule_is_owed_at_its_instant() {
    let now = 1_000_000;
    let mut t = Trace::with(Resonate { fire_within: 2_500, ..Resonate::default() }, now);
    let tags = flag_tags(true, false, false, None);
    t.step("create s", schedule("s", "* * * * * *", "ex:run-{{.timestamp}}", 60_000, tags.clone(), now), |r| sched(r).is_some_and(|c| c.next_run_at == 1_001_000));
    t.tick(1_000_999);
    t.step("s not yet advanced", Request::ScheduleGet(ScheduleGetReq { id: "s".into() }), |r| sched(r).is_some_and(|c| c.last_run_at.is_none()));
    t.step("run-1001000 absent", get("ex:run-1001000"), st(404));
    t.tick(1_001_000);
    let r = t.step("run-1001000 created at its instant", get("ex:run-1001000"), promise(PromiseState::Pending, None));
    assert!(promise_record(&r).is_some_and(|p| p.created_at == 1_001_000));
    t.c.receive(execute("ex:run-1001000", 0)).unwrap();
    t.step("s advanced", Request::ScheduleGet(ScheduleGetReq { id: "s".into() }), |r| sched(r).is_some_and(|c| c.last_run_at == Some(1_001_000) && c.next_run_at == 1_002_000));
    t.rejects("run-1001000 cannot be absent at its instant", get("ex:run-1001000"), Response::Status(StatusRes { status: 404 }));
    // A jump over later instants owes every one of them, not a sweep window.
    t.tick(1_004_000);
    t.step("run-1002000 owed", get("ex:run-1002000"), promise(PromiseState::Pending, None));
    t.step("run-1003000 owed", get("ex:run-1003000"), promise(PromiseState::Pending, None));
    t.step("run-1004000 owed", get("ex:run-1004000"), promise(PromiseState::Pending, None));
    t.rejects("run-1003000 cannot be absent", get("ex:run-1003000"), Response::Status(StatusRes { status: 404 }));
    t.step("s advanced to 1005000", Request::ScheduleGet(ScheduleGetReq { id: "s".into() }), |r| sched(r).is_some_and(|c| c.last_run_at == Some(1_004_000) && c.next_run_at == 1_005_000));
    t.step("delete s", Request::ScheduleDelete(ScheduleDeleteReq { id: "s".into() }), st(200));

    t.tick(1_010_000);
    t.step("create u", schedule("u", "*/5 * * * * *", "ex:job-{{.timestamp}}", 60_000, tags.clone(), 1_010_000), |r| sched(r).is_some_and(|c| c.next_run_at == 1_015_000));
    t.tick(1_015_000);
    t.step("job-1015000 exists", get("ex:job-1015000"), promise(PromiseState::Pending, None));
    t.step("u advanced with the occurrence", Request::ScheduleGet(ScheduleGetReq { id: "u".into() }), |r| sched(r).is_some_and(|c| c.last_run_at == Some(1_015_000) && c.next_run_at == 1_020_000));
    t.rejects("u cannot still expect 1015000 at that instant", Request::ScheduleGet(ScheduleGetReq { id: "u".into() }), Response::Schedule(ScheduleRes {
        status: 200,
        schedule: Some(Schedule {
            id: "u".into(),
            cron: "*/5 * * * * *".into(),
            promise_id: "ex:job-{{.timestamp}}".into(),
            promise_timeout: 60_000,
            promise_param: val(Some("p")),
            promise_tags: tags,
            created_at: 1_010_000,
            next_run_at: 1_015_000,
            last_run_at: None,
        }),
    }));
}
#[test]
fn the_wire_rules_are_refusals() {
    let now = 1_000_000;
    let mut t = Trace::new(now);
    let delayed = |id: &str, target: bool, delay: Time| {
        Request::PromiseCreate(PromiseCreateReq { id: id.into(), timeout_at: now + 1_000, param: val(None), tags: flag_tags(target, false, false, Some(delay)) })
    };
    t.step("delay without a target → 400", delayed("ex:d1", false, now + 10), st(400));
    t.step("delay at the deadline → 400", delayed("ex:d2", true, now + 1_000), st(400));
    t.step("delay before the deadline → 200", delayed("ex:d3", true, now + 999), promise(PromiseState::Pending, None));
    let tc = Request::TaskCreate(TaskCreateReq {
        pid: "w".into(),
        ttl: 10,
        action: PromiseCreateReq { id: "ex:t".into(), timeout_at: FAR, param: val(None), tags: flag_tags(true, false, false, Some(now + 1)) },
    });
    t.step("task.create with a delay → 400", tc, st(400));
    t.step("create a:t +target", create("a:t", FAR, "w").target().op(), st(200));
    t.step("create b:t +target", create("b:t", FAR, "w").target().op(), st(200));
    t.step("acquire a:t", acquire("a:t", 0, "w"), st(200));
    t.step("acquire b:t", acquire("b:t", 0, "w"), st(200));
    let hb = |ids: &[&str]| {
        Request::TaskHeartbeat(TaskHeartbeatReq {
            pid: "w".into(),
            tasks: ids.iter().map(|id| TaskRef { id: (*id).into(), version: 1 }).collect(),
        })
    };
    t.step("heartbeat across origins → 400", hb(&["a:t", "b:t"]), st(400));
    t.step("heartbeat in one origin → 200", hb(&["a:t"]), st(200));
    // The fence's check runs before the action. A stale same-origin fence is 409.
    // A detached create runs first; a missing task then answers 404.
    let bad = PromiseCreateReq { id: "a:d".into(), timeout_at: FAR, param: val(None), tags: flag_tags(false, false, false, Some(now)) };
    t.step("stale fence, delayed create without a target → 409", fence("a:t", 9, TaskFenceAction::Create(bad.clone())), st(409));
    t.step("missing task, detached delayed create → 404", fence("a:ghost", 0, TaskFenceAction::Create(PromiseCreateReq { id: "d:d".into(), ..bad })), st(404));
    t.step("d:d not created", get("d:d"), st(404));
}

#[test]
fn a_detached_create_lands_before_the_fence_is_checked() {
    let mut t = Trace::new(1_000_000);
    t.step("create a:t +target", create("a:t", FAR, "w").target().op(), st(200));
    t.step("acquire a:t → v1", acquire("a:t", 0, "w"), st(200));
    t.step("stale detached create → 409", fence("a:t", 9, TaskFenceAction::Create(create("d:x", FAR, "x").target())), st(409));
    t.step("d:x exists all the same", get("d:x"), promise(PromiseState::Pending, None));
    t.c.receive(execute("d:x", 0)).unwrap();
    t.step("detached create from a missing task → 404", fence("a:ghost", 0, TaskFenceAction::Create(create("d:y", FAR, "y"))), st(404));
    t.step("d:y exists all the same", get("d:y"), promise(PromiseState::Pending, None));
    t.step("detached create at the held version → 200", fence("a:t", 1, TaskFenceAction::Create(create("d:z", FAR, "z"))), promise(PromiseState::Pending, None));
    t.step("same-origin stale fence creates nothing", fence("a:t", 9, TaskFenceAction::Create(create("a:n", FAR, "n"))), st(409));
    t.step("a:n not created", get("a:n"), st(404));
}

// ------------------------------------------- the same answer, before or after

/// A halt of a halted task answers 200 and changes nothing; after a concurrent
/// continue it answers 200 and halts the task again. Both orders are
/// candidates until a read decides.
#[test]
fn a_halt_may_land_before_or_after_a_concurrent_continue() {
    for (last, want) in [("continue", TaskState::Pending), ("halt", TaskState::Halted)] {
        let mut t = Trace::new(1_000_000);
        t.step("create t +target", create("ex:t", FAR, "w").target().op(), st(200));
        t.step("halt t", Request::TaskHalt(TaskHaltReq { id: "ex:t".into() }), st(200));
        t.invoke(10, Request::TaskHalt(TaskHaltReq { id: "ex:t".into() }));
        t.invoke(11, Request::TaskContinue(TaskContinueReq { id: "ex:t".into() }));
        t.ret(10, Response::Status(StatusRes { status: 200 }));
        t.ret(11, Response::Status(StatusRes { status: 200 }));
        t.step(&format!("task.get t → the {last} came last"), get_task("ex:t"), task(want, 0));
    }
}

/// A create of a schedule that exists echoes it; after its concurrent delete
/// it creates it anew, as of the clock at that time, which a later clock move
/// must not disturb.
#[test]
fn a_schedule_recreated_during_its_delete_keeps_its_time() {
    let now = 1_000_000;
    let mut t = Trace::new(now);
    let s = schedule("s", "* * * * * *", "ex:run-{{.timestamp}}", 1_500, flag_tags(true, false, false, None), now);
    let first = t.step("create s", s.clone(), st(200));
    t.tick(now + 500);
    t.invoke(10, Request::ScheduleDelete(ScheduleDeleteReq { id: "s".into() }));
    t.invoke(11, s);
    t.tick(now + 999);
    t.ret(10, Response::Status(StatusRes { status: 200 }));
    let Response::Schedule(c) = first else { panic!() };
    let mut again = c;
    let rec = again.schedule.as_mut().unwrap();
    rec.created_at = now + 500;
    rec.next_run_at = 1_001_000;
    t.ret(11, Response::Schedule(again.clone()));
    t.step("get s → created anew at +500", Request::ScheduleGet(ScheduleGetReq { id: "s".into() }), |r| *r == Response::Schedule(again.clone()));
}
