//! Traces ported from resonate-accordant `Tests/ExampleTraces.cs` and
//! `Tests/LeaseAndTimeoutTests.cs`. There is no server here, so each step asks the
//! spec which responses it allows, checks that the one the C# trace expects is
//! among them, and feeds it back as the observation.

#[path = "common/certified.rs"]
mod certified;

use accordant::{CallId, Checker, Config, Engine, Event, Grouped, Keyed, Time};
use certified::Certified;
use resonate::*;

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
        let shadow = Config { certify: true, ..Config::default() };
        let mut t = Trace {
            c: Checker::with_partitions(Resonate, Server::default(), Config::default()),
            shadow: Certified(Checker::with_footprints(Resonate, Server::default(), shadow)),
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

    #[track_caller]
    fn idle(&mut self) {
        self.c.assert_idle().unwrap();
        self.shadow.assert_idle().unwrap();
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

    /// The model must reject `resp` (Accordant's `ExpectRejected`).
    #[track_caller]
    fn rejects(&mut self, label: &str, op: Request, resp: Response) {
        let id = self.id();
        assert!(self.c.call(id, op.clone(), resp.clone()).is_err(), "{label}: model accepted a bogus response");
        assert!(self.shadow.call(id, op, resp).is_err(), "{label}: model accepted a bogus response in one factor");
    }

    /// The driver moves the server's clock.
    #[track_caller]
    fn tick(&mut self, t: Time) {
        self.step(&format!("tick {t}"), Request::AdvanceClock(t), st(200));
    }
}

// --------------------------------------------------------------- builders

fn create(id: &str, timeout_at: Time, data: &str) -> Create {
    Create { id: id.into(), timeout_at, data: Some(data.into()), external: false, target: false, timer: false }
}

/// Builders for a create request.
trait CreateExt {
    fn external(self) -> Self;
    fn target(self) -> Self;
    fn op(self) -> Request;
}

impl CreateExt for Create {
    fn external(mut self) -> Self {
        self.external = true;
        self
    }
    fn target(mut self) -> Self {
        self.target = true;
        self
    }
    fn op(self) -> Request {
        Request::CreatePromise(self)
    }
}

fn settle(id: &str, state: &str, data: &str) -> Settle {
    Settle { id: id.into(), state: state.into(), data: Some(data.into()) }
}

fn get(id: &str) -> Request {
    Request::GetPromise(id.into())
}

fn get_task(id: &str) -> Request {
    Request::GetTask(id.into())
}

fn acquire(id: &str, version: u32, pid: &str) -> Request {
    acquire_ttl(id, version, pid, 60_000)
}

fn acquire_ttl(id: &str, version: u32, pid: &str, ttl: Time) -> Request {
    Request::AcquireTask { id: id.into(), version, pid: pid.into(), ttl }
}

fn fulfill(id: &str, version: u32, state: &str, data: &str) -> Request {
    Request::FulfillTask { id: id.into(), version, state: state.into(), data: Some(data.into()) }
}

fn fence(id: &str, version: u32, action: Fenced) -> Request {
    Request::FenceTask { id: id.into(), version, action }
}

fn suspend(id: &str, version: u32, awaited: &[&str]) -> Request {
    Request::SuspendTask { id: id.into(), version, awaited: awaited.iter().map(|a| a.to_string()).collect() }
}

fn callback(awaited: &str, awaiter: &str) -> Request {
    Request::RegisterCallback { awaited: awaited.into(), awaiter: awaiter.into() }
}

// ------------------------------------------------------------- predicates

fn st(code: u16) -> impl Fn(&Response) -> bool {
    move |r| r.status() == code
}

fn promise(state: PState, value: Option<&'static str>) -> impl Fn(&Response) -> bool {
    move |r| matches!(r, Response::Promise(p) if p.state == state && p.value.as_deref() == value)
}

fn task(state: TState, version: u32) -> impl Fn(&Response) -> bool {
    move |r| matches!(r, Response::Task(t) if t.state == state && t.version == version)
}

const FAR: Time = 9_000_000_000_000;

// ------------------------------------------------------------------ traces

#[test]
fn promise_layer() {
    let now = 3_000_000;
    let mut t = Trace::new(now);
    t.step("create p1 pending", create("ex:p1", now + 10_000, "hello").op(), promise(PState::Pending, None));
    t.step("get p1 → pending", get("ex:p1"), promise(PState::Pending, None));
    t.step("settle p1 → resolved(42)", Request::SettlePromise(settle("ex:p1", "resolved", "42")), promise(PState::Resolved, Some("42")));
    t.step("re-settle p1 → sticky", Request::SettlePromise(settle("ex:p1", "resolved", "99")), promise(PState::Resolved, Some("42")));
    t.step("create p2", create("ex:p2", now + 10_000, "A").op(), st(200));
    let r = t.step("re-create p2 → echoes A", create("ex:p2", now + 10_000, "B").op(), st(200));
    assert!(matches!(r, Response::Promise(p) if p.param.as_deref() == Some("A")));
    t.step("get missing → 404", get("ex:ghost"), st(404));
    t.step("create pc", create("ex:pc", now + 10_000, "z").op(), st(200));
    t.step("cancel pc", Request::SettlePromise(settle("ex:pc", "rejected_canceled", "gone")), promise(PState::Canceled, Some("gone")));
    t.step("re-settle cancelled → sticky", Request::SettlePromise(settle("ex:pc", "resolved", "x")), promise(PState::Canceled, Some("gone")));
    t.step("settle invalid state → 400", Request::SettlePromise(settle("ex:pc", "bogus", "x")), st(400));

    let Response::Promise(real) = t.c.allowed(&get("ex:p1")).remove(0) else { panic!() };
    t.rejects("get p1 claiming 999", get("ex:p1"), Response::Promise(PromiseRec { value: Some("999".into()), ..real.clone() }));
    t.rejects("get p1 claiming pending", get("ex:p1"), Response::Promise(PromiseRec { state: PState::Pending, ..real }));

    t.step("create p3 (5s)", create("ex:p3", now + 5_000, "x").op(), st(200));
    t.tick(now + 6_000);
    // C#: "(pending|timedout) nondeterministic". Here the deadline is a timer, so it is decided.
    t.step("get p3 → timed out", get("ex:p3"), promise(PState::TimedOut, None));
    let Response::Promise(p) = t.c.allowed(&get("ex:p3")).remove(0) else { panic!() };
    let stale = Response::Promise(PromiseRec { state: PState::Pending, settled_at: None, ..p });
    t.rejects("get p3 → pending after its deadline", get("ex:p3"), stale);
}

#[test]
fn task_layer() {
    let now = 3_000_000;
    let mut t = Trace::new(now);
    t.step("create t1 +target", create("ex:t1", now + 100_000, "work").target().op(), st(200));
    t.step("acquire t1 v0 → v1", acquire("ex:t1", 0, "worker-1"), task(TState::Acquired, 1));
    t.step("acquire t1 v0 again → 409", acquire("ex:t1", 0, "worker-2"), st(409));
    t.step("fulfill t1 v1", fulfill("ex:t1", 1, "resolved", "done"), promise(PState::Resolved, Some("done")));
    t.step("get t1 → resolved", get("ex:t1"), promise(PState::Resolved, Some("done")));

    t.step("create t2 +target", create("ex:t2", now + 100_000, "w").target().op(), st(200));
    t.step("acquire t2 → v1", acquire("ex:t2", 0, "worker-1"), task(TState::Acquired, 1));
    t.step("release t2 v1", Request::ReleaseTask { id: "ex:t2".into(), version: 1 }, st(200));
    t.step("stale fulfill → 409", fulfill("ex:t2", 1, "resolved", "zombie"), st(409));
    t.step("get t2 → still pending", get("ex:t2"), promise(PState::Pending, None));
    t.step("acquire wrong version → 409", acquire("ex:t2", 9, "worker-1"), st(409));
    t.step("acquire missing → 404", acquire("ex:ghostTask", 0, "worker-1"), st(404));

    let tc = |target| Request::CreateTask { id: "ex:tc1".into(), timeout_at: now + 100_000, data: Some("self".into()), target };
    t.step("task.create tc1 → acquired v1", tc(true), |r| matches!(r, Response::Created(_, t) if t.version == 1));
    t.step("task.create tc1 dup → 409", tc(true), st(409));
    t.step("task.create no-target → 400", tc(false), st(400));
    t.step("fulfill tc1", fulfill("ex:tc1", 1, "resolved", "ok"), st(200));
    t.step("create plain p1", create("ex:p1", now + 100_000, "p").op(), st(200));
    let over = Request::CreateTask { id: "ex:p1".into(), timeout_at: now + 100_000, data: None, target: true };
    t.step("task.create over plain promise → 422", over, st(422));
}

#[test]
fn fence_layer() {
    let now = 3_000_000;
    let mut t = Trace::new(now);
    t.step("create fp +target", create("ex:fp", now + 100_000, "w").target().op(), st(200));
    t.step("acquire fp → v1", acquire("ex:fp", 0, "worker-1"), task(TState::Acquired, 1));
    t.step("create fchild", create("ex:fchild", now + 100_000, "c").op(), st(200));
    t.step("fence own id → 400", fence("ex:fp", 1, Fenced::Settle(settle("ex:fp", "resolved", "x"))), st(400));
    t.step("fence wrong version → 409", fence("ex:fp", 9, Fenced::Settle(settle("ex:fchild", "resolved", "x"))), st(409));
    t.step("fence settles fchild", fence("ex:fp", 1, Fenced::Settle(settle("ex:fchild", "resolved", "sealed"))), st(200));
    t.step("get fchild → sealed", get("ex:fchild"), promise(PState::Resolved, Some("sealed")));
    t.step("fence-create fnew", fence("ex:fp", 1, Fenced::Create(create("ex:fnew", now + 100_000, "kid"))), promise(PState::Pending, None));
    t.step("fence-create past deadline → born timed out", fence("ex:fp", 1, Fenced::Create(create("ex:fexp", now - 1, "old"))), promise(PState::TimedOut, None));
    t.step("fence-create +target", fence("ex:fp", 1, Fenced::Create(create("ex:ftask", now + 100_000, "w").target())), st(200));
    t.step("acquire ftask → v1", acquire("ex:ftask", 0, "worker-1"), task(TState::Acquired, 1));
    t.step("release fp", Request::ReleaseTask { id: "ex:fp".into(), version: 1 }, st(200));
    t.step("create fchild2", create("ex:fchild2", now + 100_000, "c").op(), st(200));
    t.step("stale fence → 409", fence("ex:fp", 1, Fenced::Settle(settle("ex:fchild2", "resolved", "late"))), st(409));
    t.step("stale fence-create → 409", fence("ex:fp", 1, Fenced::Create(create("ex:fzomb", now + 100_000, "z"))), st(409));
    t.step("fchild2 untouched", get("ex:fchild2"), promise(PState::Pending, None));
    t.step("fzomb not created", get("ex:fzomb"), st(404));
}

#[test]
fn callback_layer() {
    let now = 3_000_000;
    let mut t = Trace::new(now);
    t.step("create t1 +target", create("ex:t1", now + 100_000, "w").target().op(), st(200));
    t.step("create awaited (external)", create("ex:awaited", now + 100_000, "x").external().op(), st(200));
    t.step("register_callback pending → 200", callback("ex:awaited", "ex:t1"), promise(PState::Pending, None));
    t.step("register_callback missing → 404", callback("ex:ghost", "ex:t1"), st(404));
    t.step("create internal p2", create("ex:p2", now + 100_000, "x").op(), st(200));
    t.step("register_callback internal → 422", callback("ex:p2", "ex:t1"), st(422));
    t.step("create other:x", create("other:x", now + 100_000, "x").external().op(), st(200));
    t.step("cross-origin → 400", callback("other:x", "ex:t1"), st(400));
    let listen = |a: &str| Request::RegisterListener { awaited: "ex:awaited".into(), address: a.into() };
    t.step("listener http → 200", listen("http://localhost/cb"), st(200));
    t.step("listener poll://bad → 200", listen("poll://bad"), st(200));
    t.step("listener not a url → 400", listen("not a url"), st(400));

    t.step("create root +target", create("ex:root", now + 100_000, "r").target().op(), st(200));
    t.step("acquire root → v1", acquire("ex:root", 0, "worker-1"), task(TState::Acquired, 1));
    t.step("suspend root on awaited → 200", suspend("ex:root", 1, &["ex:awaited"]), st(200));
    t.step("task.get root → suspended", get_task("ex:root"), task(TState::Suspended, 1));
    t.step("suspend foreign → 400", suspend("ex:root", 1, &["other:x"]), st(400));
    t.step("settle awaited → arms resume", Request::SettlePromise(settle("ex:awaited", "resolved", "v")), st(200));
    // C# polls until the resume lands; here Quiesce says the server is idle.
    t.idle();
    assert!(t.c.all(|s| s.tasks["ex:root"].state == TState::Pending));
    t.step("re-acquire root v1 → v2", acquire("ex:root", 1, "worker-1"), task(TState::Acquired, 2));

    t.step("create done", create("ex:done", now + 100_000, "d").external().op(), st(200));
    t.step("settle done", Request::SettlePromise(settle("ex:done", "resolved", "d")), st(200));
    t.step("create root2", create("ex:root2", now + 100_000, "r").target().op(), st(200));
    t.step("acquire root2", acquire("ex:root2", 0, "worker-1"), task(TState::Acquired, 1));
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
    t.step("settle a", Request::SettlePromise(settle("ex:a", "resolved", "v")), st(200));
    // The resume is background work: right after the settle, either answer is fine.
    let seen = t.c.allowed(&get_task("ex:r"));
    assert!(seen.iter().any(task(TState::Suspended, 1)) && seen.iter().any(task(TState::Pending, 1)), "{seen:?}");
}

#[test]
fn lease_and_heartbeat() {
    let mut t = Trace::new(1_000_000);
    t.step("create L", create("L", FAR, "w").target().op(), st(200));
    t.step("acquire L ttl 5000", acquire_ttl("L", 0, "wA", 5_000), task(TState::Acquired, 1));
    t.tick(1_004_000);
    t.step("acquire while held → 409", acquire_ttl("L", 1, "wB", 5_000), st(409));
    t.tick(1_005_000);
    // C#: "acquired OR pending (reclaim is a choice)". Here the lease check is
    // a timer: at the lease end the task is reclaimed, so only pending.
    let seen = t.c.allowed(&get_task("L"));
    assert!(seen.iter().all(task(TState::Pending, 1)) && !seen.is_empty(), "{seen:?}");
    t.step("re-acquire after reclaim → v2", acquire_ttl("L", 1, "wB", 5_000), task(TState::Acquired, 2));

    t.step("create H", create("H", FAR, "w").target().op(), st(200));
    t.step("acquire H ttl 5000", acquire_ttl("H", 0, "wH", 5_000), task(TState::Acquired, 1));
    t.tick(1_008_000);
    let hb = |pid: &str, version| Request::HeartbeatTask { id: "H".into(), version, pid: pid.into() };
    t.step("heartbeat H → lease to 1013000", hb("wH", 1), st(200));
    t.tick(1_012_000);
    t.step("acquire H → 409 (heartbeat kept it)", acquire_ttl("H", 1, "wX", 5_000), st(409));
    t.step("heartbeat wrong pid → 200, no extension", hb("WRONG", 1), st(200));
    t.tick(1_014_000);
    t.step("re-acquire H after reclaim → v2", acquire_ttl("H", 1, "wX", 5_000), task(TState::Acquired, 2));
    t.step("heartbeat wrong version → 200, no extension", hb("wX", 1), st(200));
    t.tick(1_019_000);
    t.step("re-acquire H v2 → v3", acquire_ttl("H", 2, "wY", 5_000), task(TState::Acquired, 3));
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
    t.step("now it is timed out", get("p"), promise(PState::TimedOut, None));
}

#[test]
fn unanswered_settle_may_land_late() {
    let now = 1_000_000;
    let mut t = Trace::new(now);
    t.step("create p", create("p", FAR, "x").op(), st(200));
    t.invoke(100, Request::SettlePromise(settle("p", "resolved", "v"))); // never answered
    t.step("read misses it", get("p"), promise(PState::Pending, None));
    t.step("read sees it", get("p"), promise(PState::Resolved, Some("v")));
}

#[test]
fn poll_past_its_limit_claims_some_subset() {
    let now = 1_000_000;
    let mut t = Trace::new(now);
    for id in ["a", "b", "c"] {
        t.step("create +target", create(id, FAR, "w").target().op(), st(200));
    }
    let poll = Request::PollTask { pid: "w".into(), ttl: 60_000, limit: 2 };
    assert_eq!(t.c.allowed(&poll).len(), 3, "one outcome per 2-subset");
    t.step("poll claims a and c", poll, |r| matches!(r, Response::Claimed(v) if v.iter().map(|t| t.id.as_str()).eq(["a", "c"])));
    t.step("b was not claimed", get_task("b"), task(TState::Pending, 0));
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
            let Response::Promise(p) = before else { panic!() };
            Response::Promise(PromiseRec { state: PState::TimedOut, settled_at: Some(p.timeout_at), ..p })
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
    let v = t.c.call(id, acquire("ex:t", 0, "w"), Response::Status(409)).unwrap_err();
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
) -> Result<Checker<E>, accordant::Violation> {
    let now = 1_000_000;
    c.call(900_000, Request::AdvanceClock(now), Response::Status(200))?;
    for o in 0..origins {
        let id = format!("o{o}:p");
        let p = Create { id: id.clone(), timeout_at: now + 1_000, data: None, external: false, target: false, timer: false };
        let r = c.allowed(&Request::CreatePromise(p.clone())).remove(0);
        c.call(o, Request::CreatePromise(p), r)?;
        c.invoke(1_000 + o, Request::SettlePromise(Settle { id, state: "resolved".into(), data: None }))?;
    }
    c.call(900_001, Request::AdvanceClock(now + 2_000), Response::Status(200))?;
    Ok(c)
}

#[test]
fn partitions_keep_independent_origins_apart() {
    let t0 = std::time::Instant::now();
    let mut c = unanswered_settles(Checker::with_partitions(Resonate, Server::default(), settles_cfg()), 20).unwrap();
    println!("partitioned: {:?}, width {}, {:?}", c.stats, c.width(), t0.elapsed());
    assert_eq!(c.factors().len(), 20);
    assert!(c.factors().iter().all(|f| f.nodes.len() == 2));
    assert_eq!(c.width(), 1 << 20);
    // Each origin resolves on its own read.
    for o in 0..20u64 {
        let id = format!("o{o}:p");
        let want = if o % 3 == 0 { PState::Resolved } else { PState::TimedOut };
        let r = c.allowed(&Request::GetPromise(id.clone())).into_iter().find(promise(want, None)).unwrap();
        c.call(5_000 + o, Request::GetPromise(id), r).unwrap();
    }
    assert!(c.factors().iter().all(|f| f.nodes.len() == 1));

    let t0 = std::time::Instant::now();
    let v = unanswered_settles(Checker::with_footprints(Resonate, Server::default(), settles_cfg()), 20)
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
    t.step("fence-settle across origins → 400", fence("a:t", 1, Fenced::Settle(settle("b:p", "resolved", "v"))), st(400));
    t.step("callback across origins → 400", callback("b:p", "a:t"), st(400));
    t.step("suspend across origins → 400", suspend("a:t", 1, &["b:p"]), st(400));
    assert_eq!((t.c.factors().len(), t.c.stats.merges), (3, 0));

    // A detached workflow: a:t creates d:root. The two origins merge for the
    // request and split again once it has returned.
    t.step("detached create d:root", fence("a:t", 1, Fenced::Create(create("d:root", FAR, "w").target())), promise(PState::Pending, None));
    assert_eq!(t.c.stats.splits, 1);
    assert_eq!(t.c.factors().len(), 4, "a, b, c and d, each on its own");
    t.step("d:root is its own workflow", acquire("d:root", 0, "w2"), task(TState::Acquired, 1));

    // Unanswered, the detached create keeps the two origins together until it is resolved.
    let calls = t.next;
    t.invoke(calls + 1, fence("a:t", 1, Fenced::Create(create("e:root", FAR, "w"))));
    assert_eq!(t.c.factors().len(), 4, "a and e merged");
    t.next += 1;
    t.step("e:root exists, so the create landed", get("e:root"), promise(PState::Pending, None));
    assert_eq!(t.c.factors().len(), 4, "the unanswered fence still links a and e");

    t.step("poll touches every origin", Request::PollTask { pid: "w".into(), ttl: 1_000, limit: 10 }, |_| true);
    assert_eq!(t.c.factors().len(), 1);
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
        let mut on = Checker::with_partitions(Resonate, Server::default(), Config::default());
        let mut off = Checker::with_footprints(Resonate, Server::default(), Config::default());
        let tick = |t| [Event::Invoke { call: 900_000 + t, req: Request::AdvanceClock(t) }, Event::Return { call: 900_000 + t, res: Response::Status(200) }];
        let mut open: Vec<(CallId, Request)> = Vec::new();
        let mut clock = now;
        let mut all = Vec::new();
        let mut kept = Vec::new();
        for call in 0..60u64 {
            let id = ids[rng.next(ids.len() as u64) as usize].to_string();
            let other = ids[rng.next(ids.len() as u64) as usize].to_string();
            let op = match rng.next(9) {
                0 => Request::CreatePromise(Create { id, timeout_at: clock + 500 + rng.next(3_000), data: None, external: rng.next(2) == 0, target: rng.next(2) == 0, timer: false }),
                1 => Request::SettlePromise(Settle { id, state: "resolved".into(), data: None }),
                2 => Request::AcquireTask { id, version: rng.next(3) as u32, pid: "w".into(), ttl: 1_000 },
                3 => Request::FulfillTask { id, version: rng.next(3) as u32, state: "resolved".into(), data: None },
                4 => Request::SuspendTask { id, version: rng.next(3) as u32, awaited: vec![other] },
                5 => Request::RegisterCallback { awaited: id, awaiter: other },
                6 => Request::FenceTask { id, version: rng.next(3) as u32, action: Fenced::Settle(Settle { id: other, state: "resolved".into(), data: None }) },
                7 if rng.next(2) == 0 => Request::FenceTask { id, version: rng.next(3) as u32, action: Fenced::Create(Create { id: format!("{other}x"), timeout_at: clock + rng.next(3_000), data: None, external: false, target: rng.next(2) == 0, timer: false }) },
                7 => Request::GetTask(id),
                _ => Request::GetPromise(id),
            };
            let mut events = if call == 0 { tick(now).to_vec() } else { Vec::new() };
            events.push(Event::Invoke { call, req: op.clone() });
            match rng.next(4) {
                0 => open.push((call, op.clone())), // answered later, or never
                _ => {
                    let allowed = off.allowed(&op);
                    let resp = if allowed.is_empty() || rng.next(8) == 0 {
                        Response::Status(500 + rng.next(3) as u16) // bogus
                    } else {
                        allowed[rng.next(allowed.len() as u64) as usize].clone()
                    };
                    events.push(Event::Return { call, res: resp });
                }
            }
            if rng.next(5) == 0 {
                clock += 1 + rng.next(2_000); // the driver moves the clock
                events.extend(tick(clock));
            }
            if !open.is_empty() && rng.next(4) == 0 {
                // A late answer: whatever the op would get if called now. Valid or
                // not, both checkers must agree.
                let (c, op) = open.swap_remove(rng.next(open.len() as u64) as usize);
                let resp = off.allowed(&op).first().cloned().unwrap_or(Response::Status(404));
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
                // Property 1 (proved for promise_create in src/spec.rs),
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
        assert_eq!(on.assert_idle().is_ok(), off.assert_idle().is_ok(), "seed {seed}: quiesce");
        // The whole history (bogus responses make it invalid), online and depth
        // first: the same verdict.
        let online = Checker::with_footprints(Resonate, Server::default(), Config::default()).check_history(&all).is_ok();
        let mut dfs = Checker::with_footprints(Resonate, Server::default(), Config { certify: true, ..Config::default() });
        let deep = dfs.check_complete(&all).is_ok();
        assert_eq!(online, deep, "seed {seed}: online={online} depth-first={deep}");
        if deep {
            dfs.certified().unwrap_or_else(|v| panic!("seed {seed}: {v}"));
        }
        let mut split = Checker::with_partitions(Resonate, Server::default(), Config::default());
        assert_eq!(split.check_complete(&all).is_ok(), deep, "seed {seed}: depth first by partition");
        // What the online checker accepted, event by event, is a valid history:
        // depth first must accept it too, and certify it.
        let mut dfs = Checker::with_footprints(Resonate, Server::default(), Config { certify: true, ..Config::default() });
        dfs.check_complete(&kept).unwrap_or_else(|v| panic!("seed {seed}: accepted events rejected depth first: {v}"));
        dfs.certified().unwrap_or_else(|v| panic!("seed {seed}: {v}"));
        let mut split = Checker::with_partitions(Resonate, Server::default(), Config::default());
        split.check_complete(&kept).unwrap_or_else(|v| panic!("seed {seed}: by partition: {v}"));
    }
}

// ------------------------------------------------------- server-sent messages

fn execute(id: &str, version: u32) -> Dispatch {
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
    t.idle(); // the execute was sent; nobody has to receive it
    t.step("acquire t", acquire("ex:t", 0, "w"), task(TState::Acquired, 1));
}

#[test]
fn a_resume_dispatches_the_waiting_task() {
    let mut t = Trace::new(1_000_000);
    t.step("create a", create("ex:a", FAR, "x").external().op(), st(200));
    t.step("create r +target", create("ex:r", FAR, "r").target().op(), st(200));
    t.step("acquire r", acquire("ex:r", 0, "w"), task(TState::Acquired, 1));
    assert!(t.c.receive(execute("ex:r", 1)).is_err(), "running, not suspended");
    t.step("suspend r on a", suspend("ex:r", 1, &["ex:a"]), st(200));
    t.step("settle a", Request::SettlePromise(settle("ex:a", "resolved", "v")), st(200));
    // Receiving the execute forces the hidden resume, then the dispatch.
    t.c.receive(execute("ex:r", 1)).unwrap();
    assert!(t.c.all(|s| s.tasks["ex:r"].state == TState::Pending));
}

#[test]
fn a_reclaimed_lease_dispatches_again() {
    let mut t = Trace::new(1_000_000);
    t.step("create t +target", create("ex:t", FAR, "w").target().op(), st(200));
    t.c.receive(execute("ex:t", 0)).unwrap();
    t.step("acquire t ttl 5000", acquire_ttl("ex:t", 0, "w", 5_000), task(TState::Acquired, 1));
    t.tick(1_010_000);
    t.c.receive(execute("ex:t", 1)).unwrap();
}

#[test]
fn check_takes_calls_dispatches_and_clock_moves() {
    let now = 1_000_000;
    let mut t = Trace::new(now);
    let create_r = create("ex:r", now + 10_000, "r").target().op();
    let created = t.c.allowed(&create_r).remove(0); // the pending record
    let mut c = Checker::with_partitions(Resonate, Server::default(), Config::default());
    let tick = |call, t| [Event::Invoke { call, req: Request::AdvanceClock(t) }, Event::Return { call, res: Response::Status(200) }];
    let trace = [
        tick(10, now).to_vec(),
        vec![
            Event::Invoke { call: 1, req: create_r },
            Event::Return { call: 1, res: created.clone() },
            Event::Receive { msg: execute("ex:r", 0) },
        ],
        tick(11, now + 20_000).to_vec(),
        vec![Event::Invoke { call: 2, req: get("ex:r") }],
    ]
    .concat();
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
        t.step("acquire x", acquire(&x, 0, "p"), task(TState::Acquired, 1));
        t.step("suspend x", suspend(&x, 1, &[&a]), st(200));
        t.step("settle a", Request::SettlePromise(settle(&a, "resolved", "v")), st(200));
        t.step("re-acquire x", acquire(&x, 1, "p"), task(TState::Acquired, 2));
        t.step("fulfill x", fulfill(&x, 2, "resolved", "ok"), st(200));
    }
    assert_eq!(t.c.stats.max_width, 1, "{:?}", t.c.stats);
}
