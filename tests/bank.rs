//! The BankAccount sample from Accordant, with calls split into request and response.

use accordant::{Checker, Config, Footprint, HashedMap, Keyed, Model, ExternalOutcome, Time, Touches};

#[derive(Clone, PartialEq, Eq, Hash, Debug, Default)]
struct Bank {
    accounts: HashedMap<&'static str, i64>,
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
enum Request {
    Open(&'static str),
    Deposit(&'static str, i64),
    Withdraw(&'static str, i64),
    Balance(&'static str),
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
enum Response {
    Ok(i64),
    NotFound,
    Conflict,
    Insufficient,
}

struct BankModel;

impl Model for BankModel {
    type State = Bank;
    type External = Request;
    type Response = Response;
    type Internal = ();
    type Dispatch = ();

    fn external(&self, op: &Request, s: &Bank, _now: Time) -> Vec<ExternalOutcome<Self>> {
        let with = |a: &'static str, b: i64| {
            let mut n = s.clone();
            n.accounts.insert(a, b);
            n
        };
        let out = match *op {
            Request::Open(a) if s.accounts.contains_key(&a) => ExternalOutcome::same(Response::Conflict, s),
            Request::Open(a) => ExternalOutcome::new(Response::Ok(0), with(a, 0)),
            Request::Deposit(a, x) => match s.accounts.get(&a) {
                None => ExternalOutcome::same(Response::NotFound, s),
                Some(b) => ExternalOutcome::new(Response::Ok(b + x), with(a, b + x)),
            },
            Request::Withdraw(a, x) => match s.accounts.get(&a) {
                None => ExternalOutcome::same(Response::NotFound, s),
                Some(b) if *b < x => ExternalOutcome::same(Response::Insufficient, s),
                Some(b) => ExternalOutcome::new(Response::Ok(b - x), with(a, b - x)),
            },
            Request::Balance(a) => match s.accounts.get(&a) {
                None => ExternalOutcome::same(Response::NotFound, s),
                Some(b) => ExternalOutcome::same(Response::Ok(*b), s),
            },
        };
        vec![out]
    }

}

impl Footprint for BankModel {
    type Key = &'static str;

    fn external_touches(&self, op: &Request) -> Touches<&'static str> {
        match *op {
            Request::Open(a) | Request::Deposit(a, _) | Request::Withdraw(a, _) | Request::Balance(a) => Touches::one(a),
        }
    }

    fn internal_touches(&self, _: &()) -> Touches<&'static str> {
        Touches::Only(vec![])
    }
}

fn checker() -> Checker<Keyed<BankModel>> {
    let mut c = Checker::with_footprints(BankModel, Bank::default(), Config::default());
    c.call(0, Request::Open("alice"), Response::Ok(0)).unwrap();
    c.call(1, Request::Deposit("alice", 100), Response::Ok(100)).unwrap();
    c
}

#[test]
fn overlapping_withdrawals_linearize() {
    let mut c = checker();
    c.invoke(2, Request::Withdraw("alice", 60)).unwrap();
    c.invoke(3, Request::Withdraw("alice", 60)).unwrap();
    c.ret(3, Response::Ok(40)).unwrap();
    c.ret(2, Response::Insufficient).unwrap();
    assert!(c.all(|s| s.accounts[&"alice"] == 40));
}

#[test]
fn double_spend_is_rejected() {
    let mut c = checker();
    c.invoke(2, Request::Withdraw("alice", 60)).unwrap();
    c.invoke(3, Request::Withdraw("alice", 60)).unwrap();
    c.ret(2, Response::Ok(40)).unwrap();
    let v = c.ret(3, Response::Ok(40)).unwrap_err();
    assert!(v.reason.contains("no candidate"), "{v}");
}

#[test]
fn real_time_order_is_respected() {
    // Withdraw returns before Deposit is invoked, so it cannot see the deposit.
    let mut c = checker();
    c.call(2, Request::Withdraw("alice", 150), Response::Insufficient).unwrap();
    c.call(3, Request::Deposit("alice", 100), Response::Ok(200)).unwrap();
    let mut c = checker();
    c.call(2, Request::Deposit("alice", 100), Response::Ok(200)).unwrap();
    assert!(c.call(3, Request::Withdraw("alice", 150), Response::Insufficient).is_err());
}

#[test]
fn unanswered_request_may_take_effect_late() {
    // The client never learns what happened to call 2. Accordant would have to
    // decide "before or never" at the timeout; here the deposit may land after a
    // read that missed it.
    let mut c = checker();
    c.invoke(2, Request::Deposit("alice", 50)).unwrap();
    c.call(3, Request::Balance("alice"), Response::Ok(100)).unwrap();
    c.call(4, Request::Balance("alice"), Response::Ok(150)).unwrap();
    assert!(c.all(|s| s.accounts[&"alice"] == 150));
}

#[test]
fn unanswered_request_may_never_take_effect() {
    let mut c = checker();
    c.invoke(2, Request::Deposit("alice", 50)).unwrap();
    for i in 0..10 {
        c.call(10 + i, Request::Balance("alice"), Response::Ok(100)).unwrap();
    }
    // Both explanations remain: it may still land.
    assert!(c.states().any(|s| s.accounts[&"alice"] == 100));
}

fn with_lifetime(life: Time) -> Checker<Keyed<BankModel>> {
    let cfg = Config { request_lifetime: Some(life), ..Config::default() };
    let mut c = Checker::with_footprints(BankModel, Bank::default(), cfg);
    c.call(0, Request::Open("alice"), Response::Ok(0)).unwrap();
    c.call(1, Request::Deposit("alice", 100), Response::Ok(100)).unwrap();
    c
}

#[test]
fn request_lifetime_bounds_a_late_effect() {
    // A request takes effect within 1s of its invoke, or never.
    let mut c = with_lifetime(1_000);
    c.invoke(2, Request::Deposit("alice", 50)).unwrap();
    c.tick(500).unwrap();
    c.call(3, Request::Balance("alice"), Response::Ok(100)).unwrap();
    c.tick(900).unwrap();
    c.call(4, Request::Balance("alice"), Response::Ok(150)).unwrap(); // landed between 500 and 900
    let mut c = with_lifetime(1_000);
    c.invoke(2, Request::Deposit("alice", 50)).unwrap();
    c.tick(1_500).unwrap();
    c.call(3, Request::Balance("alice"), Response::Ok(100)).unwrap(); // past its lifetime: it never happened
    assert!(c.call(4, Request::Balance("alice"), Response::Ok(150)).is_err());
}

#[test]
fn request_lifetime_prunes_the_profile() {
    let mut c = with_lifetime(1_000);
    c.invoke(2, Request::Deposit("alice", 50)).unwrap();
    c.call(3, Request::Balance("alice"), Response::Ok(100)).unwrap();
    assert!(c.profile().iter().all(|n| n.pending.len() == 1), "call 2 still in flight");
    c.tick(2_000).unwrap();
    c.call(4, Request::Balance("alice"), Response::Ok(100)).unwrap();
    assert_eq!(c.profile().len(), 1);
    assert!(c.profile()[0].pending.is_empty(), "call 2 resolved to never: {:?}", c.profile());
}

#[test]
fn late_response_after_effect_is_still_accepted() {
    let mut c = with_lifetime(1_000);
    c.invoke(2, Request::Deposit("alice", 50)).unwrap();
    c.call(3, Request::Balance("alice"), Response::Ok(150)).unwrap(); // it took effect
    c.tick(5_000).unwrap();
    c.ret(2, Response::Ok(150)).unwrap(); // the response arrives much later
}

#[test]
fn response_after_lifetime_without_effect_is_rejected() {
    let mut c = with_lifetime(1_000);
    c.invoke(2, Request::Deposit("alice", 50)).unwrap();
    c.tick(5_000).unwrap();
    c.call(3, Request::Balance("alice"), Response::Ok(100)).unwrap(); // it never took effect
    assert!(c.ret(2, Response::Ok(150)).is_err());
}

#[test]
fn effect_seen_then_undone_is_rejected() {
    let mut c = checker();
    c.invoke(2, Request::Withdraw("alice", 30)).unwrap();
    c.call(3, Request::Balance("alice"), Response::Ok(70)).unwrap(); // the withdraw linearized
    assert!(c.call(4, Request::Balance("alice"), Response::Ok(100)).is_err());
}

/// Many concurrent calls on distinct accounts. With footprints each Return only
/// linearizes calls on its own account; without them, every subset of the other
/// in-flight calls may have linearized first, and the profile explodes.
#[test]
fn footprints_keep_the_cone_small() {
    let names = ["a", "b", "c", "d", "e", "f", "g", "h"];
    let run = |footprints: bool| {
        let cfg = Config { footprints, ..Config::default() };
        let mut c = Checker::with_footprints(BankModel, Bank::default(), cfg);
        for (i, n) in names.iter().enumerate() {
            c.call(i as u64, Request::Open(n), Response::Ok(0)).unwrap();
        }
        for (i, n) in names.iter().enumerate() {
            c.invoke(100 + i as u64, Request::Deposit(n, 10)).unwrap();
        }
        for (i, _) in names.iter().enumerate() {
            c.ret(100 + i as u64, Response::Ok(10)).unwrap();
        }
        c.stats.clone()
    };
    let with = run(true);
    let without = run(false);
    println!("footprints: {with:?}\nnone:       {without:?}");
    assert_eq!(with.max_width, 1);
    assert!(without.max_width >= 64, "{without:?}");
    assert!(with.explored * 50 < without.explored, "{with:?} vs {without:?}");
}

// ------------------------------------------------------------ whole traces

use accordant::Event;

fn model() -> Checker<Keyed<BankModel>> {
    Checker::with_footprints(BankModel, Bank::default(), Config::default())
}

fn inv(at: Time, call: u64, req: Request) -> Event<Request, Response, ()> {
    Event::Invoke { at, call, req }
}

fn ret(at: Time, call: u64, res: Response) -> Event<Request, Response, ()> {
    Event::Return { at, call, res }
}

#[test]
fn check_accepts_a_valid_trace_of_events() {
    let trace = vec![
        inv(0, 0, Request::Open("alice")),
        ret(0, 0, Response::Ok(0)),
        inv(1, 1, Request::Deposit("alice", 100)),
        ret(1, 1, Response::Ok(100)),
        inv(2, 2, Request::Withdraw("alice", 60)),
        inv(2, 3, Request::Withdraw("alice", 60)),
        ret(3, 3, Response::Ok(40)),
        ret(4, 2, Response::Insufficient),
    ];
    model().check(trace).unwrap();
}

#[test]
fn check_reports_the_position_of_the_first_bad_observation() {
    let trace = vec![
        inv(0, 0, Request::Open("alice")),
        ret(0, 0, Response::Ok(0)),
        inv(1, 1, Request::Deposit("alice", 100)),
        ret(1, 1, Response::Ok(100)),
        inv(2, 2, Request::Withdraw("alice", 60)),
        inv(2, 3, Request::Withdraw("alice", 60)),
        ret(3, 2, Response::Ok(40)),
        ret(3, 3, Response::Ok(40)), // double spend
        inv(4, 4, Request::Balance("alice")),
    ];
    let v = model().check(trace).unwrap_err();
    assert_eq!(v.index, 7, "{v}");
}

#[test]
fn check_rejects_time_going_backwards() {
    let trace = vec![inv(10, 0, Request::Open("alice")), ret(5, 0, Response::Ok(0))];
    assert_eq!(model().check(trace).unwrap_err().index, 1);
}

#[test]
fn check_advances_the_clock_to_each_observation() {
    let cfg = Config { request_lifetime: Some(1_000), ..Config::default() };
    let open = vec![
        inv(0, 0, Request::Open("alice")),
        ret(0, 0, Response::Ok(0)),
        inv(10, 1, Request::Deposit("alice", 50)), // never answered
    ];
    let late_read = |at| vec![inv(at, 2, Request::Balance("alice")), ret(at, 2, Response::Ok(50))];

    let mut c = Checker::with_footprints(BankModel, Bank::default(), cfg.clone());
    c.check(open.clone().into_iter().chain(late_read(500))).unwrap(); // within its lifetime

    let mut c = Checker::with_footprints(BankModel, Bank::default(), cfg);
    c.check(open).unwrap();
    c.check(vec![inv(5_000, 3, Request::Balance("alice")), ret(5_000, 3, Response::Ok(0))]).unwrap(); // past it: never happened
    assert!(c.check(late_read(6_000)).is_err());
}

#[test]
fn check_calls_takes_a_log_of_request_response_pairs() {
    let log = vec![
        (0, Request::Open("alice"), Response::Ok(0)),
        (1, Request::Deposit("alice", 100), Response::Ok(100)),
        (2, Request::Withdraw("alice", 30), Response::Ok(70)),
        (3, Request::Withdraw("alice", 100), Response::Insufficient),
        (4, Request::Balance("alice"), Response::Ok(70)),
    ];
    model().check_calls(log.clone()).unwrap();

    let mut bad = log;
    bad[3].2 = Response::Ok(-30);
    assert_eq!(model().check_calls(bad).unwrap_err().index, 3);
}

#[test]
fn check_calls_streams_a_generated_trace() {
    // 10,000 deposits, generated lazily: nothing is collected up front.
    let mut balance = 0;
    let mut n = 0;
    let deposits = std::iter::from_fn(move || {
        n += 1;
        if n > 10_000 {
            return None;
        }
        balance += 1;
        Some((n, Request::Deposit("alice", 1), Response::Ok(balance)))
    });
    let mut c = model();
    c.check_calls([(0, Request::Open("alice"), Response::Ok(0))]).unwrap();
    let stats = c.check_calls(deposits).unwrap();
    assert_eq!(stats.max_width, 1);
}
