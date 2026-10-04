//! A large bank: many accounts, rounds of concurrent deposits, footprints off so
//! the profile fans out. Compares three state representations: a copied
//! `BTreeMap`, a persistent `imbl::OrdMap`, and `HashedMap` (persistent, with an
//! incrementally maintained hash).
//!
//! cargo run --release --example bank_bench -- [accounts] [rounds] [concurrency]

use std::alloc::{GlobalAlloc, Layout, System};
use std::collections::BTreeMap;
use std::fmt::Debug;
use std::hash::Hash;
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};
use std::time::Instant;

use accordant::{Checker, Config, Keys, Outcome, Spec};

struct Counting;

static LIVE: AtomicUsize = AtomicUsize::new(0);
static PEAK: AtomicUsize = AtomicUsize::new(0);

unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        let live = LIVE.fetch_add(l.size(), Relaxed) + l.size();
        PEAK.fetch_max(live, Relaxed);
        unsafe { System.alloc(l) }
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        LIVE.fetch_sub(l.size(), Relaxed);
        unsafe { System.dealloc(p, l) }
    }
}

#[global_allocator]
static A: Counting = Counting;

trait Accounts: Clone + Eq + Hash + Debug + Default {
    fn get(&self, k: u32) -> Option<i64>;
    fn put(&mut self, k: u32, v: i64);
}

impl Accounts for BTreeMap<u32, i64> {
    fn get(&self, k: u32) -> Option<i64> {
        BTreeMap::get(self, &k).copied()
    }
    fn put(&mut self, k: u32, v: i64) {
        self.insert(k, v);
    }
}

impl Accounts for accordant::HashedMap<u32, i64> {
    fn get(&self, k: u32) -> Option<i64> {
        accordant::HashedMap::get(self, &k).copied()
    }
    fn put(&mut self, k: u32, v: i64) {
        self.insert(k, v);
    }
}

impl Accounts for imbl::OrdMap<u32, i64> {
    fn get(&self, k: u32) -> Option<i64> {
        imbl::OrdMap::get(self, &k).copied()
    }
    fn put(&mut self, k: u32, v: i64) {
        self.insert(k, v);
    }
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
enum Op {
    Deposit(u32, i64),
}

struct Bank<M>(std::marker::PhantomData<M>);

impl<M: Accounts> Spec for Bank<M> {
    type State = M;
    type Op = Op;
    type Resp = i64;
    type Step = ();
    type Key = u32;

    fn apply(&self, op: &Op, s: &M, _now: accordant::Time) -> Vec<Outcome<Self>> {
        let Op::Deposit(a, x) = *op;
        let b = s.get(a).unwrap_or(0) + x;
        let mut n = s.clone();
        n.put(a, b);
        vec![Outcome::new(b, n)]
    }

    fn op_keys(&self, Op::Deposit(a, _): &Op) -> Keys<u32> {
        Keys::one(*a)
    }
}

fn run<M: Accounts>(name: &str, accounts: u32, rounds: u32, k: u32, footprints: bool) {
    let mut init = M::default();
    for a in 0..accounts {
        init.put(a, 0);
    }
    let base = LIVE.load(Relaxed);
    PEAK.store(base, Relaxed);
    let t = Instant::now();
    let cfg = Config { footprints, max_width: 1 << 20, ..Config::default() };
    let mut c = Checker::new(Bank::<M>(Default::default()), init, cfg);
    let mut balance = vec![0i64; accounts as usize];
    let mut id = 0u64;
    for r in 0..rounds {
        let calls: Vec<(u64, u32)> = (0..k)
            .map(|i| {
                id += 1;
                (id, (r * k + i) * 7919 % accounts)
            })
            .collect();
        for &(call, a) in &calls {
            c.invoke(call, Op::Deposit(a, 10)).unwrap();
        }
        for &(call, a) in &calls {
            balance[a as usize] += 10;
            c.ret(call, balance[a as usize]).unwrap();
        }
    }
    let secs = t.elapsed().as_secs_f64();
    let s = &c.stats;
    println!(
        "{name:<10} footprints={footprints:<5} width={:<5} explored={:<8} time={:>7.3}s  {:>9.0} nodes/s  peak={:>8.1} MiB",
        s.max_width,
        s.explored,
        secs,
        s.explored as f64 / secs,
        (PEAK.load(Relaxed) - base) as f64 / (1 << 20) as f64,
    );
}

fn main() {
    let args: Vec<u32> = std::env::args().skip(1).map(|a| a.parse().unwrap()).collect();
    let accounts = *args.first().unwrap_or(&10_000);
    let rounds = *args.get(1).unwrap_or(&20);
    let k = *args.get(2).unwrap_or(&8);
    println!("accounts={accounts} rounds={rounds} concurrency={k}");
    for footprints in [false, true] {
        run::<BTreeMap<u32, i64>>("BTreeMap", accounts, rounds, k, footprints);
        run::<imbl::OrdMap<u32, i64>>("OrdMap", accounts, rounds, k, footprints);
        run::<accordant::HashedMap<u32, i64>>("HashedMap", accounts, rounds, k, footprints);
    }
}
