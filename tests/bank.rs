//! The BankAccount sample from Accordant, with calls split into request and response.

use std::collections::BTreeMap;

use accordant::{Checker, Config, Keys, Outcome, Spec};

#[derive(Clone, PartialEq, Eq, Hash, Debug, Default)]
struct Bank {
    accounts: BTreeMap<&'static str, i64>,
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
enum Op {
    Open(&'static str),
    Deposit(&'static str, i64),
    Withdraw(&'static str, i64),
    Balance(&'static str),
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
enum Resp {
    Ok(i64),
    NotFound,
    Conflict,
    Insufficient,
}

struct BankSpec;

impl Spec for BankSpec {
    type State = Bank;
    type Op = Op;
    type Resp = Resp;
    type Step = ();
    type Key = &'static str;

    fn apply(&self, op: &Op, s: &Bank) -> Vec<Outcome<Self>> {
        let with = |a: &'static str, b: i64| {
            let mut n = s.clone();
            n.accounts.insert(a, b);
            n
        };
        let out = match *op {
            Op::Open(a) if s.accounts.contains_key(a) => Outcome::same(Resp::Conflict, s),
            Op::Open(a) => Outcome::new(Resp::Ok(0), with(a, 0)),
            Op::Deposit(a, x) => match s.accounts.get(a) {
                None => Outcome::same(Resp::NotFound, s),
                Some(b) => Outcome::new(Resp::Ok(b + x), with(a, b + x)),
            },
            Op::Withdraw(a, x) => match s.accounts.get(a) {
                None => Outcome::same(Resp::NotFound, s),
                Some(b) if *b < x => Outcome::same(Resp::Insufficient, s),
                Some(b) => Outcome::new(Resp::Ok(b - x), with(a, b - x)),
            },
            Op::Balance(a) => match s.accounts.get(a) {
                None => Outcome::same(Resp::NotFound, s),
                Some(b) => Outcome::same(Resp::Ok(*b), s),
            },
        };
        vec![out]
    }

    fn op_keys(&self, op: &Op) -> Keys<&'static str> {
        match *op {
            Op::Open(a) | Op::Deposit(a, _) | Op::Withdraw(a, _) | Op::Balance(a) => Keys::one(a),
        }
    }
}

fn checker() -> Checker<BankSpec> {
    let mut c = Checker::new(BankSpec, Bank::default(), Config::default());
    c.call(0, Op::Open("alice"), Resp::Ok(0)).unwrap();
    c.call(1, Op::Deposit("alice", 100), Resp::Ok(100)).unwrap();
    c
}

#[test]
fn overlapping_withdrawals_linearize() {
    let mut c = checker();
    c.invoke(2, Op::Withdraw("alice", 60)).unwrap();
    c.invoke(3, Op::Withdraw("alice", 60)).unwrap();
    c.ret(3, Resp::Ok(40)).unwrap();
    c.ret(2, Resp::Insufficient).unwrap();
    assert!(c.all(|s| s.accounts["alice"] == 40));
}

#[test]
fn double_spend_is_rejected() {
    let mut c = checker();
    c.invoke(2, Op::Withdraw("alice", 60)).unwrap();
    c.invoke(3, Op::Withdraw("alice", 60)).unwrap();
    c.ret(2, Resp::Ok(40)).unwrap();
    let v = c.ret(3, Resp::Ok(40)).unwrap_err();
    assert!(v.reason.contains("no candidate"), "{v}");
}

#[test]
fn real_time_order_is_respected() {
    // Withdraw returns before Deposit is invoked, so it cannot see the deposit.
    let mut c = checker();
    c.call(2, Op::Withdraw("alice", 150), Resp::Insufficient).unwrap();
    c.call(3, Op::Deposit("alice", 100), Resp::Ok(200)).unwrap();
    let mut c = checker();
    c.call(2, Op::Deposit("alice", 100), Resp::Ok(200)).unwrap();
    assert!(c.call(3, Op::Withdraw("alice", 150), Resp::Insufficient).is_err());
}

#[test]
fn lost_request_may_take_effect_late() {
    // Accordant models a timeout as OneOf(before, after) at the moment of the
    // timeout. Here the deposit may land after a read that did not see it.
    let mut c = checker();
    c.invoke(2, Op::Deposit("alice", 50)).unwrap();
    c.lost(2).unwrap();
    c.call(3, Op::Balance("alice"), Resp::Ok(100)).unwrap();
    c.call(4, Op::Balance("alice"), Resp::Ok(150)).unwrap();
    assert!(c.all(|s| s.accounts["alice"] == 150));
}

#[test]
fn lost_request_cannot_land_after_its_ttl() {
    // ghost_ttl = 3: the deposit lands by the 3rd response or never, but it may land
    // just after the 3rd read linearized. Once a 4th read misses it, it never happened.
    let mut c = checker();
    c.invoke(2, Op::Deposit("alice", 50)).unwrap();
    c.lost(2).unwrap();
    for i in 0..4 {
        c.call(10 + i, Op::Balance("alice"), Resp::Ok(100)).unwrap();
    }
    assert!(c.call(20, Op::Balance("alice"), Resp::Ok(150)).is_err());
}

#[test]
fn lost_response_after_effect_is_seen() {
    let mut c = checker();
    c.invoke(2, Op::Withdraw("alice", 30)).unwrap();
    c.call(3, Op::Balance("alice"), Resp::Ok(70)).unwrap(); // forces the withdraw to have linearized
    c.lost(2).unwrap();
    assert!(c.call(4, Op::Balance("alice"), Resp::Ok(100)).is_err());
}

/// Many concurrent calls on distinct accounts. With footprints each Return only
/// linearizes calls on its own account; without them, every subset of the other
/// in-flight calls may have linearized first, and the profile explodes.
#[test]
fn footprints_keep_the_cone_small() {
    let names = ["a", "b", "c", "d", "e", "f", "g", "h"];
    let run = |footprints: bool| {
        let cfg = Config { footprints, ..Config::default() };
        let mut c = Checker::new(BankSpec, Bank::default(), cfg);
        for (i, n) in names.iter().enumerate() {
            c.call(i as u64, Op::Open(n), Resp::Ok(0)).unwrap();
        }
        for (i, n) in names.iter().enumerate() {
            c.invoke(100 + i as u64, Op::Deposit(n, 10)).unwrap();
        }
        for (i, _) in names.iter().enumerate() {
            c.ret(100 + i as u64, Resp::Ok(10)).unwrap();
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

#[test]
fn ghost_ttl_boundary() {
    let mut c = checker();
    c.invoke(2, Op::Deposit("alice", 50)).unwrap();
    c.lost(2).unwrap();
    for i in 0..3 {
        c.call(10 + i, Op::Balance("alice"), Resp::Ok(100)).unwrap();
    }
    // ghost_ttl = 3: three reads may miss it and the fourth may still see it.
    c.call(20, Op::Balance("alice"), Resp::Ok(150)).unwrap();
}
