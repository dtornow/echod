//! The BankAccount sample from Accordant, with calls split into request and response.

use accordant::{Checker, Config, Footprint, HashedMap, Keyed, Model, ExternalOutcome, Touches};

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

    fn external(&self, op: &Request, s: &Bank) -> Vec<ExternalOutcome<Self>> {
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
    let mut c = Checker::with_footprints(BankModel, Bank::default(), Config { certify: true, ..Config::default() });
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
    c.certified().unwrap();
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
    c.certified().unwrap();
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
    c.certified().unwrap();
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
    c.certified().unwrap();
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
        let cfg = Config { footprints, certify: true, ..Config::default() };
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
        c.certified().unwrap();
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
    Checker::with_footprints(BankModel, Bank::default(), Config { certify: true, ..Config::default() })
}

fn inv(call: u64, req: Request) -> Event<Request, Response, ()> {
    Event::Invoke { call, req }
}

fn ret(call: u64, res: Response) -> Event<Request, Response, ()> {
    Event::Return { call, res }
}

fn trace_again() -> Vec<Event<Request, Response, ()>> {
    vec![
        inv(0, Request::Open("alice")),
        ret(0, Response::Ok(0)),
        inv(1, Request::Deposit("alice", 100)),
        ret(1, Response::Ok(100)),
        inv(2, Request::Withdraw("alice", 60)),
        inv(3, Request::Withdraw("alice", 60)),
        ret(3, Response::Ok(40)),
        ret(2, Response::Insufficient),
    ]
}

#[test]
fn check_accepts_a_valid_trace_of_events() {
    let trace = vec![
        inv(0, Request::Open("alice")),
        ret(0, Response::Ok(0)),
        inv(1, Request::Deposit("alice", 100)),
        ret(1, Response::Ok(100)),
        inv(2, Request::Withdraw("alice", 60)),
        inv(3, Request::Withdraw("alice", 60)),
        ret(3, Response::Ok(40)),
        ret(2, Response::Insufficient),
    ];
    model().check(trace).unwrap();
    model().check_certified(trace_again()).unwrap();
    // Depth first, with a certificate for the path it found.
    let mut c = model();
    c.check_complete(&trace_again()).unwrap();
    c.certified().unwrap();
}

#[test]
fn check_reports_the_position_of_the_first_bad_observation() {
    let trace = vec![
        inv(0, Request::Open("alice")),
        ret(0, Response::Ok(0)),
        inv(1, Request::Deposit("alice", 100)),
        ret(1, Response::Ok(100)),
        inv(2, Request::Withdraw("alice", 60)),
        inv(3, Request::Withdraw("alice", 60)),
        ret(2, Response::Ok(40)),
        ret(3, Response::Ok(40)), // double spend
        inv(4, Request::Balance("alice")),
    ];
    let v = model().check(trace).unwrap_err();
    assert_eq!(v.index, 7, "{v}");
}

#[test]
fn check_calls_takes_a_log_of_request_response_pairs() {
    let log = vec![
        (Request::Open("alice"), Response::Ok(0)),
        (Request::Deposit("alice", 100), Response::Ok(100)),
        (Request::Withdraw("alice", 30), Response::Ok(70)),
        (Request::Withdraw("alice", 100), Response::Insufficient),
        (Request::Balance("alice"), Response::Ok(70)),
    ];
    let mut c = model();
    c.check_calls(log.clone()).unwrap();
    c.certified().unwrap();

    let mut bad = log;
    bad[3].1 = Response::Ok(-30);
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
        Some((Request::Deposit("alice", 1), Response::Ok(balance)))
    });
    let mut c = model();
    c.check_calls([(Request::Open("alice"), Response::Ok(0))]).unwrap();
    let stats = c.check_calls(deposits).unwrap();
    assert_eq!(stats.max_width, 1);
    // Each call: invoke, effect, return.
    assert_eq!(c.certified().unwrap().len(), 3 * 10_001);
}

/// Random concurrent histories on three accounts, from a real run with some
/// responses corrupted and some never delivered: the online checker and the
/// depth-first one must agree, and every depth-first acceptance must certify.
#[test]
fn depth_first_agrees_with_the_online_checker() {
    struct Lcg(u64);
    impl Lcg {
        fn next(&mut self, n: u64) -> u64 {
            self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            (self.0 >> 33) % n
        }
    }
    let names = ["a", "b", "c"];
    let (mut valid, mut invalid) = (0, 0);
    for seed in 1..=300 {
        let mut rng = Lcg(seed);
        let mut bank = Bank::default();
        let mut trace = vec![];
        let mut open: Vec<(u64, Request)> = vec![];
        for (i, n) in names.iter().enumerate() {
            let call = 1000 + i as u64;
            trace.extend([inv(call, Request::Open(n)), ret(call, Response::Ok(0))]);
            bank.accounts.insert(n, 0);
        }
        for call in 0..14u64 {
            let n = names[rng.next(3) as usize];
            let req = match rng.next(3) {
                0 => Request::Deposit(n, 1 + rng.next(5) as i64),
                1 => Request::Withdraw(n, 1 + rng.next(5) as i64),
                _ => Request::Balance(n),
            };
            trace.push(inv(call, req.clone()));
            open.push((call, req));
            // Some open call takes effect now, in the real system, and answers.
            while !open.is_empty() && rng.next(3) != 0 {
                let (c, req) = open.remove(rng.next(open.len() as u64) as usize);
                let out = BankModel.external(&req, &bank).remove(0);
                bank = out.next;
                let res = if rng.next(12) == 0 { Response::Ok(-7) } else { out.resp };
                if rng.next(10) != 0 {
                    trace.push(ret(c, res)); // else: never delivered
                }
            }
        }
        let online = model().check_history(&trace).is_ok();
        let mut c = model();
        let dfs = c.check_complete(&trace).is_ok();
        assert_eq!(online, dfs, "seed {seed}: online={online} depth-first={dfs}\n{trace:?}");
        if dfs {
            c.certified().unwrap_or_else(|v| panic!("seed {seed}: {v}"));
            valid += 1;
        } else {
            invalid += 1;
        }
    }
    assert!(valid > 50 && invalid > 50, "{valid} valid, {invalid} invalid");
}
