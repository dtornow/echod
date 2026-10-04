//! Traces ported from resonate-accordant `Tests/ExampleTraces.cs` and
//! `Tests/LeaseAndTimeoutTests.cs`. There is no server here, so each step asks the
//! spec which responses it allows, checks that the one the C# trace expects is
//! among them, and feeds it back as the observation.

mod spec;

use accordant::{CallId, Checker, Config, Time};
use spec::*;

struct Trace {
    c: Checker<Resonate>,
    next: CallId,
}

impl Trace {
    fn new(now: Time) -> Self {
        Trace { c: Checker::starting_at(Resonate, Server::default(), Config::default(), now), next: 0 }
    }

    fn id(&mut self) -> CallId {
        self.next += 1;
        self.next
    }

    /// Calls `op` and answers it with an allowed response matching `want`.
    #[track_caller]
    fn step(&mut self, label: &str, op: Op, want: impl Fn(&Resp) -> bool) -> Resp {
        let allowed = self.c.allowed(&op);
        let Some(r) = allowed.iter().find(|r| want(r)).cloned() else {
            panic!("{label}: no allowed response matches; spec allows {allowed:#?}");
        };
        let id = self.id();
        self.c.call(id, op, r.clone()).unwrap_or_else(|v| panic!("{label}: {v}"));
        r
    }

    /// The model must reject `resp` (Accordant's `ExpectRejected`).
    #[track_caller]
    fn rejects(&mut self, label: &str, op: Op, resp: Resp) {
        let id = self.id();
        assert!(self.c.call(id, op, resp).is_err(), "{label}: model accepted a bogus response");
    }

    #[track_caller]
    fn tick(&mut self, t: Time) {
        self.c.tick(t).unwrap_or_else(|v| panic!("tick {t}: {v}"));
    }
}

// --------------------------------------------------------------- builders

fn create(id: &str, timeout_at: Time, data: &str) -> Create {
    Create { id: id.into(), timeout_at, data: Some(data.into()), external: false, target: false, timer: false }
}

impl Create {
    fn external(mut self) -> Self {
        self.external = true;
        self
    }
    fn target(mut self) -> Self {
        self.target = true;
        self
    }
    fn op(self) -> Op {
        Op::CreatePromise(self)
    }
}

fn settle(id: &str, state: &str, data: &str) -> Settle {
    Settle { id: id.into(), state: state.into(), data: Some(data.into()) }
}

fn get(id: &str) -> Op {
    Op::GetPromise(id.into())
}

fn get_task(id: &str) -> Op {
    Op::GetTask(id.into())
}

fn acquire(id: &str, version: u32, pid: &str) -> Op {
    acquire_ttl(id, version, pid, 60_000)
}

fn acquire_ttl(id: &str, version: u32, pid: &str, ttl: Time) -> Op {
    Op::AcquireTask { id: id.into(), version, pid: pid.into(), ttl }
}

fn fulfill(id: &str, version: u32, state: &str, data: &str) -> Op {
    Op::FulfillTask { id: id.into(), version, state: state.into(), data: Some(data.into()) }
}

fn fence(id: &str, version: u32, action: Fenced) -> Op {
    Op::FenceTask { id: id.into(), version, action }
}

fn suspend(id: &str, version: u32, awaited: &[&str]) -> Op {
    Op::SuspendTask { id: id.into(), version, awaited: awaited.iter().map(|a| a.to_string()).collect() }
}

fn callback(awaited: &str, awaiter: &str) -> Op {
    Op::RegisterCallback { awaited: awaited.into(), awaiter: awaiter.into() }
}

// ------------------------------------------------------------- predicates

fn st(code: u16) -> impl Fn(&Resp) -> bool {
    move |r| r.status() == code
}

fn promise(state: PState, value: Option<&'static str>) -> impl Fn(&Resp) -> bool {
    move |r| matches!(r, Resp::Promise(p) if p.state == state && p.value.as_deref() == value)
}

fn task(state: TState, version: u32) -> impl Fn(&Resp) -> bool {
    move |r| matches!(r, Resp::Task(t) if t.state == state && t.version == version)
}

const FAR: Time = 9_000_000_000_000;

// ------------------------------------------------------------------ traces

#[test]
fn promise_layer() {
    let now = 3_000_000;
    let mut t = Trace::new(now);
    t.step("create p1 pending", create("ex:p1", now + 10_000, "hello").op(), promise(PState::Pending, None));
    t.step("get p1 → pending", get("ex:p1"), promise(PState::Pending, None));
    t.step("settle p1 → resolved(42)", Op::SettlePromise(settle("ex:p1", "resolved", "42")), promise(PState::Resolved, Some("42")));
    t.step("re-settle p1 → sticky", Op::SettlePromise(settle("ex:p1", "resolved", "99")), promise(PState::Resolved, Some("42")));
    t.step("create p2", create("ex:p2", now + 10_000, "A").op(), st(200));
    let r = t.step("re-create p2 → echoes A", create("ex:p2", now + 10_000, "B").op(), st(200));
    assert!(matches!(r, Resp::Promise(p) if p.param.as_deref() == Some("A")));
    t.step("get missing → 404", get("ex:ghost"), st(404));
    t.step("create pc", create("ex:pc", now + 10_000, "z").op(), st(200));
    t.step("cancel pc", Op::SettlePromise(settle("ex:pc", "rejected_canceled", "gone")), promise(PState::Canceled, Some("gone")));
    t.step("re-settle cancelled → sticky", Op::SettlePromise(settle("ex:pc", "resolved", "x")), promise(PState::Canceled, Some("gone")));
    t.step("settle invalid state → 400", Op::SettlePromise(settle("ex:pc", "bogus", "x")), st(400));

    let Resp::Promise(real) = t.c.allowed(&get("ex:p1")).remove(0) else { panic!() };
    t.rejects("get p1 claiming 999", get("ex:p1"), Resp::Promise(PromiseRec { value: Some("999".into()), ..real.clone() }));
    t.rejects("get p1 claiming pending", get("ex:p1"), Resp::Promise(PromiseRec { state: PState::Pending, ..real }));

    t.step("create p3 (5s)", create("ex:p3", now + 5_000, "x").op(), st(200));
    t.tick(now + 6_000);
    // C#: "(pending|timedout) nondeterministic". Here the deadline is a timer, so it is decided.
    t.step("get p3 → timed out", get("ex:p3"), promise(PState::TimedOut, None));
    t.rejects("get p3 → pending after its deadline", get("ex:p3"), {
        let Resp::Promise(p) = t.c.allowed(&get("ex:p3")).remove(0) else { panic!() };
        Resp::Promise(PromiseRec { state: PState::Pending, settled_at: None, ..p })
    });
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
    t.step("release t2 v1", Op::ReleaseTask { id: "ex:t2".into(), version: 1 }, st(200));
    t.step("stale fulfill → 409", fulfill("ex:t2", 1, "resolved", "zombie"), st(409));
    t.step("get t2 → still pending", get("ex:t2"), promise(PState::Pending, None));
    t.step("acquire wrong version → 409", acquire("ex:t2", 9, "worker-1"), st(409));
    t.step("acquire missing → 404", acquire("ex:ghostTask", 0, "worker-1"), st(404));

    let tc = |target| Op::CreateTask { id: "ex:tc1".into(), timeout_at: now + 100_000, data: Some("self".into()), target };
    t.step("task.create tc1 → acquired v1", tc(true), |r| matches!(r, Resp::Created(_, t) if t.version == 1));
    t.step("task.create tc1 dup → 409", tc(true), st(409));
    t.step("task.create no-target → 400", tc(false), st(400));
    t.step("fulfill tc1", fulfill("ex:tc1", 1, "resolved", "ok"), st(200));
    t.step("create plain p1", create("ex:p1", now + 100_000, "p").op(), st(200));
    let over = Op::CreateTask { id: "ex:p1".into(), timeout_at: now + 100_000, data: None, target: true };
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
    t.step("release fp", Op::ReleaseTask { id: "ex:fp".into(), version: 1 }, st(200));
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
    let listen = |a: &str| Op::RegisterListener { awaited: "ex:awaited".into(), address: a.into() };
    t.step("listener http → 200", listen("http://localhost/cb"), st(200));
    t.step("listener poll://bad → 200", listen("poll://bad"), st(200));
    t.step("listener not a url → 400", listen("not a url"), st(400));

    t.step("create root +target", create("ex:root", now + 100_000, "r").target().op(), st(200));
    t.step("acquire root → v1", acquire("ex:root", 0, "worker-1"), task(TState::Acquired, 1));
    t.step("suspend root on awaited → 200", suspend("ex:root", 1, &["ex:awaited"]), st(200));
    t.step("task.get root → suspended", get_task("ex:root"), task(TState::Suspended, 1));
    t.step("suspend foreign → 400", suspend("ex:root", 1, &["other:x"]), st(400));
    t.step("settle awaited → arms resume", Op::SettlePromise(settle("ex:awaited", "resolved", "v")), st(200));
    // C# polls until the resume lands; here Quiesce says the server is idle.
    t.c.quiesce().unwrap();
    assert!(t.c.all(|s| s.tasks["ex:root"].state == TState::Pending));
    t.step("re-acquire root v1 → v2", acquire("ex:root", 1, "worker-1"), task(TState::Acquired, 2));

    t.step("create done", create("ex:done", now + 100_000, "d").external().op(), st(200));
    t.step("settle done", Op::SettlePromise(settle("ex:done", "resolved", "d")), st(200));
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
    t.step("settle a", Op::SettlePromise(settle("ex:a", "resolved", "v")), st(200));
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
    // C#: "acquired OR pending (reclaim is a choice)".
    let seen = t.c.allowed(&get_task("L"));
    assert!(seen.iter().any(task(TState::Acquired, 1)) && seen.iter().any(task(TState::Pending, 1)), "{seen:?}");
    t.step("re-acquire after reclaim → v2", acquire_ttl("L", 1, "wB", 5_000), task(TState::Acquired, 2));

    t.step("create H", create("H", FAR, "w").target().op(), st(200));
    t.step("acquire H ttl 5000", acquire_ttl("H", 0, "wH", 5_000), task(TState::Acquired, 1));
    t.tick(1_008_000);
    let hb = |pid: &str, version| Op::HeartbeatTask { id: "H".into(), version, pid: pid.into() };
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
    let Resp::Promise(pending) = t.c.allowed(&get("p")).remove(0) else { panic!() };
    t.c.invoke(100, get("p")).unwrap();
    t.tick(now + 5_000);
    t.c.ret(100, Resp::Promise(pending)).unwrap(); // linearized before the deadline
    t.step("now it is timed out", get("p"), promise(PState::TimedOut, None));
}

#[test]
fn unanswered_settle_may_land_late() {
    let now = 1_000_000;
    let mut t = Trace::new(now);
    t.step("create p", create("p", FAR, "x").op(), st(200));
    t.c.invoke(100, Op::SettlePromise(settle("p", "resolved", "v"))).unwrap(); // never answered
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
    let poll = Op::PollTask { pid: "w".into(), ttl: 60_000, limit: 2 };
    assert_eq!(t.c.allowed(&poll).len(), 3, "one outcome per 2-subset");
    t.step("poll claims a and c", poll, |r| matches!(r, Resp::Claimed(v) if v.iter().map(|t| t.id.as_str()).eq(["a", "c"])));
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
        t.c.invoke(1_000 + i, get(&format!("p{i}"))).unwrap();
    }
    t.tick(now + 2_000); // passes 50 deadlines with 50 reads in flight
    assert_eq!(t.c.profile().len(), 1);
    // Each read may have answered before its deadline or after: both are accepted.
    for (i, before) in pending.into_iter().enumerate() {
        let i = i as u64;
        let resp = if i.is_multiple_of(2) {
            before
        } else {
            let Resp::Promise(p) = before else { panic!() };
            Resp::Promise(PromiseRec { state: PState::TimedOut, settled_at: Some(p.timeout_at), ..p })
        };
        t.c.ret(1_000 + i, resp).unwrap();
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
    let v = t.c.call(id, acquire("ex:t", 0, "w"), Resp::Status(409)).unwrap_err();
    println!("{v}");
}
