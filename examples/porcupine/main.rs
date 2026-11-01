//! Porcupine's benchmark histories on this checker: the etcd Jepsen logs
//! (a single register with read, write and compare-and-set) and the key-value
//! logs (get, put and append on many keys), with Porcupine's models.
//!
//! examples/porcupine/fetch.sh, then
//! cargo run --release --example porcupine -- [etcd|kv|all] [--dfs] [--certify]
//!
//! Porcupine gives a call that never answered (Jepsen's `:info`, or a log that
//! ends first) a made-up "unknown" response at the end of the history that its
//! model accepts whatever happened. Here such a call simply never returns: it
//! may have taken effect at any point, or never. A read that timed out
//! (`:fail :read :timed-out`) is the same.

use std::collections::HashMap;
use std::time::{Duration, Instant};

use accordant::{Checker, Config, Engine, Event, Verdict, ExternalOutcome, Footprint, HashedMap, InternalOutcome, Model, Partitioned, Time, Touches};

const DATA: &str = "examples/porcupine/porcupine/test_data";

// ------------------------------------------------------------------- etcd

/// One register, initially empty.
struct Etcd;

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum EtcdReq {
    Read,
    Write(i64),
    Cas(i64, i64),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum EtcdRes {
    Read(Option<i64>),
    Write,
    Cas(bool),
}

impl Model for Etcd {
    type State = Option<i64>;
    type External = EtcdReq;
    type Response = EtcdRes;
    type Internal = ();
    type Dispatch = ();

    fn external(&self, req: &EtcdReq, s: &Option<i64>, _: Time) -> Vec<ExternalOutcome<Self>> {
        vec![match *req {
            EtcdReq::Read => ExternalOutcome::same(EtcdRes::Read(*s), s),
            EtcdReq::Write(v) => ExternalOutcome::new(EtcdRes::Write, Some(v)),
            EtcdReq::Cas(from, to) if *s == Some(from) => ExternalOutcome::new(EtcdRes::Cas(true), Some(to)),
            EtcdReq::Cas(..) => ExternalOutcome::same(EtcdRes::Cas(false), s),
        }]
    }

    fn internal(&self, _: &(), _: &Option<i64>, _: Time) -> Vec<InternalOutcome<Self>> {
        Vec::new()
    }
}

type EtcdEvent = Event<EtcdReq, EtcdRes, ()>;

/// `INFO  jepsen.util - 3\t:invoke\t:cas\t[1 4]`
fn parse_etcd(text: &str) -> Vec<EtcdEvent> {
    let mut events = Vec::new();
    let mut open: HashMap<u64, u64> = HashMap::new();
    let mut next = 0;
    for line in text.lines() {
        let Some((_, rest)) = line.split_once(" - ") else { continue };
        // Tabs in most logs, spaces in a few; a cas value is `[1 4]`.
        let f: Vec<&str> = rest.split_whitespace().collect();
        let (proc, kind, op, value) = match f[..] {
            [p, k, o, v] => (p, k, o, v.to_string()),
            [p, k, o, a, b] => (p, k, o, format!("{a} {b}")),
            _ => continue,
        };
        let value = value.as_str();
        let proc: u64 = proc.trim().parse().unwrap();
        let num = |s: &str| s.trim_matches(|c| c == '[' || c == ']').parse::<i64>().unwrap();
        match (kind, op) {
            (":invoke", _) => {
                let req = match op {
                    ":read" => EtcdReq::Read,
                    ":write" => EtcdReq::Write(num(value)),
                    ":cas" => {
                        let (a, b) = value.split_once(' ').unwrap();
                        EtcdReq::Cas(num(a), num(b))
                    }
                    _ => continue,
                };
                open.insert(proc, next);
                events.push(Event::Invoke { call: next, req });
                next += 1;
            }
            (":ok", ":read") => {
                let res = EtcdRes::Read(if value == "nil" { None } else { Some(num(value)) });
                events.push(Event::Return { call: open.remove(&proc).unwrap(), res });
            }
            (":ok", ":write") => events.push(Event::Return { call: open.remove(&proc).unwrap(), res: EtcdRes::Write }),
            (":ok" | ":fail", ":cas") => {
                events.push(Event::Return { call: open.remove(&proc).unwrap(), res: EtcdRes::Cas(kind == ":ok") })
            }
            // A read that timed out: it never answers, like `:info`.
            (":fail", ":read") => {
                open.remove(&proc);
            }
            _ => {}
        }
    }
    events
}


// --------------------------------------------------------------------- kv

/// Keys to strings, initially empty; partitioned by key.
struct Kv;

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum KvReq {
    Get(String),
    Put(String, String),
    Append(String, String),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum KvRes {
    Value(String),
    Ok,
}

impl Model for Kv {
    type State = HashedMap<String, String>;
    type External = KvReq;
    type Response = KvRes;
    type Internal = ();
    type Dispatch = ();

    fn external(&self, req: &KvReq, s: &Self::State, _: Time) -> Vec<ExternalOutcome<Self>> {
        vec![match req {
            KvReq::Get(k) => ExternalOutcome::same(KvRes::Value(s.get(k).cloned().unwrap_or_default()), s),
            KvReq::Put(k, v) => {
                let mut n = s.clone();
                n.insert(k.clone(), v.clone());
                ExternalOutcome::new(KvRes::Ok, n)
            }
            KvReq::Append(k, v) => {
                let mut n = s.clone();
                let old = s.get(k).cloned().unwrap_or_default();
                n.insert(k.clone(), old + v);
                ExternalOutcome::new(KvRes::Ok, n)
            }
        }]
    }

    fn internal(&self, _: &(), _: &Self::State, _: Time) -> Vec<InternalOutcome<Self>> {
        Vec::new()
    }
}

impl Footprint for Kv {
    type Key = String;

    fn external_touches(&self, req: &KvReq) -> Touches<String> {
        match req {
            KvReq::Get(k) | KvReq::Put(k, _) | KvReq::Append(k, _) => Touches::one(k.clone()),
        }
    }

    fn internal_touches(&self, _: &()) -> Touches<String> {
        Touches::Only(Vec::new())
    }
}

impl Partitioned for Kv {
    type Group = String;

    fn group(&self, key: &String) -> String {
        key.clone()
    }

    fn restrict(&self, s: &Self::State, keep: &dyn Fn(&String) -> bool) -> Self::State {
        s.iter().filter(|(k, _)| keep(k)).map(|(k, v)| (k.clone(), v.clone())).collect()
    }

    fn join(&self, a: &Self::State, b: &Self::State) -> Self::State {
        let mut n = a.clone();
        for (k, v) in b.iter() {
            n.insert(k.clone(), v.clone());
        }
        n
    }
}

type KvEvent = Event<KvReq, KvRes, ()>;

/// The text after `name` up to the next `, ` or `}`, unquoted; `None` for nil.
fn field<'a>(line: &'a str, name: &str) -> Option<&'a str> {
    let rest = &line[line.find(name)? + name.len()..];
    if let Some(q) = rest.strip_prefix('"') {
        return Some(&q[..q.find('"')?]);
    }
    let end = rest.find([',', '}']).unwrap_or(rest.len());
    let v = &rest[..end];
    (v != "nil").then_some(v)
}

/// `{:process 0, :type :invoke, :f :append, :key "0", :value "x 0 0 y"}`
fn parse_kv(text: &str) -> Vec<KvEvent> {
    let mut events = Vec::new();
    let mut open: HashMap<u64, u64> = HashMap::new();
    let mut next = 0;
    for line in text.lines() {
        let (Some(proc), Some(kind), Some(f)) = (field(line, ":process "), field(line, ":type "), field(line, ":f ")) else {
            continue;
        };
        let proc: u64 = proc.parse().unwrap();
        let key = field(line, ":key ").unwrap_or_default().to_string();
        let value = field(line, ":value ");
        match (kind, f) {
            (":invoke", _) => {
                let req = match f {
                    ":get" => KvReq::Get(key),
                    ":put" => KvReq::Put(key, value.unwrap().into()),
                    ":append" => KvReq::Append(key, value.unwrap().into()),
                    _ => continue,
                };
                open.insert(proc, next);
                events.push(Event::Invoke { call: next, req });
                next += 1;
            }
            (":ok", ":get") => {
                let Some(v) = value else { continue }; // a nil read stays unanswered, as in Porcupine
                events.push(Event::Return { call: open.remove(&proc).unwrap(), res: KvRes::Value(v.into()) });
            }
            (":ok", _) => events.push(Event::Return { call: open.remove(&proc).unwrap(), res: KvRes::Ok }),
            _ => {}
        }
    }
    events
}

// ---------------------------------------------------------------- harness

fn cfg(certify: bool) -> Config {
    Config { max_width: 1 << 17, max_explore: 20_000_000, certify, ..Config::default() }
}

/// Runs `check` until about 200ms have passed (at least once) and returns the
/// verdict and the mean time.
fn time(mut check: impl FnMut() -> bool) -> (bool, Duration) {
    let t0 = Instant::now();
    let mut runs = 0;
    let mut ok = false;
    while runs == 0 || t0.elapsed() < Duration::from_millis(200) {
        ok = check();
        runs += 1;
    }
    (ok, t0.elapsed() / runs)
}

#[derive(Clone, Copy)]
struct Mode {
    /// Depth first, for complete histories (`check_complete`), instead of every
    /// candidate at once (`check_history`).
    dfs: bool,
    /// Back the verdict with a certificate that `certify` replays.
    certify: bool,
}

/// Checks `events` in `mode`; the reason if the checker gave up instead of
/// deciding.
#[allow(clippy::type_complexity)]
fn run<S: Engine>(c: &mut Checker<S>, events: &[Event<<S::M as Model>::External, <S::M as Model>::Response, ()>], mode: Mode) -> (bool, Option<String>)
where
    S::M: Model<Dispatch = ()>,
{
    let r = match (mode.dfs, mode.certify) {
        (false, false) => c.check_history(events).map(|_| ()),
        (false, true) => c.check_certified(events.iter().cloned()).map(|_| ()),
        (true, certify) => c.check_complete(events).map(|_| ()).and_then(|_| if certify { c.certified().map(|_| ()) } else { Ok(()) }),
    };
    match Verdict::from(r) {
        Verdict::Ok(()) => (true, None),
        Verdict::Unknown(v) => (false, Some(format!("event {}: {}", v.index, v.reason))),
        Verdict::Ko(_) => (false, None),
    }
}

fn etcd(mode: Mode) {
    let expected: HashMap<u32, bool> = std::fs::read_to_string("examples/porcupine/expected_etcd.txt")
        .unwrap()
        .lines()
        .map(|l| {
            let (n, v) = l.split_once(' ').unwrap();
            (n.parse().unwrap(), v == "true")
        })
        .collect();
    let (mut total, mut wrong, mut gave) = (Duration::ZERO, 0, 0);
    for n in 0..=102u32 {
        let events = parse_etcd(&std::fs::read_to_string(format!("{DATA}/jepsen/etcd_{n:03}.log")).unwrap());
        let mut width = 0;
        let mut gave_up = None;
        let (ok, dt) = time(|| {
            let mut c = Checker::new(Etcd, None, cfg(mode.certify));
            let (ok, why) = run(&mut c, &events, mode);
            gave_up = why;
            width = c.stats.max_width;
            ok
        });
        let mark = match (&gave_up, expected.get(&n)) {
            (Some(why), _) => {
                gave += 1;
                format!("  GAVE UP at {why}")
            }
            (None, Some(w)) if *w == ok => String::new(),
            (None, Some(_)) => {
                wrong += 1;
                "  MISMATCH".into()
            }
            (None, None) => "  (Porcupine has no expected verdict)".into(),
        };
        total += dt;
        println!("etcd_{n:03}  events={:<5} {:<5} {:>10.3}ms  width={width}{mark}", events.len(), ok, dt.as_secs_f64() * 1e3);
    }
    println!(
        "etcd: 103 histories, {:.1}ms in total, {wrong} verdicts differ from Porcupine's, gave up on {gave}",
        total.as_secs_f64() * 1e3
    );
}

fn kv(mode: Mode) {
    for (name, want) in [("c01-ok", true), ("c01-bad", false), ("c10-ok", true), ("c10-bad", false), ("c50-ok", true), ("c50-bad", false)] {
        let events = parse_kv(&std::fs::read_to_string(format!("{DATA}/kv/{name}.txt")).unwrap());
        let mut width = 0;
        let mut gave_up = None;
        let (ok, dt) = time(|| {
            // Certificates need one factor; otherwise partitions, by key.
            let (ok, why) = if mode.certify {
                let mut c = Checker::with_footprints(Kv, HashedMap::new(), cfg(true));
                let r = run(&mut c, &events, mode);
                width = c.stats.max_width;
                r
            } else {
                let mut c = Checker::with_partitions(Kv, HashedMap::new(), cfg(false));
                let r = run(&mut c, &events, mode);
                width = c.stats.max_width;
                r
            };
            gave_up = why;
            ok
        });
        let mark = match &gave_up {
            Some(why) => format!("  GAVE UP at {why}"),
            None if ok == want => String::new(),
            None => "  MISMATCH".into(),
        };
        println!("kv {name:<8} events={:<5} {:<5} {:>10.3}ms  width={width}{mark}", events.len(), ok, dt.as_secs_f64() * 1e3);
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.first().map(String::as_str) == Some("probe") { probe(&args[1]); return; }
    let mode = Mode { dfs: args.iter().any(|a| a == "--dfs"), certify: args.iter().any(|a| a == "--certify") };
    let which = args.iter().find(|a| !a.starts_with("--")).map(String::as_str).unwrap_or("all");
    if which == "etcd" || which == "all" {
        etcd(mode);
    }
    if which == "kv" || which == "all" {
        kv(mode);
    }
}


#[allow(dead_code)]
fn probe(name: &str) {
    if let Some(n) = name.strip_prefix("etcd_") {
        let events = parse_etcd(&std::fs::read_to_string(format!("{DATA}/jepsen/etcd_{n}.log")).unwrap());
        let explore = std::env::var("EXPLORE").ok().and_then(|v| v.parse().ok()).unwrap_or(20_000_000);
        let mut c = Checker::new(Etcd, None, Config { max_explore: explore, ..cfg(false) });
        let t0 = Instant::now();
        let r = c.check_complete(&events).map(|_| ());
        let orphans = events.iter().filter(|e| matches!(e, Event::Invoke { .. })).count() - events.iter().filter(|e| matches!(e, Event::Return { .. })).count();
        println!("{name}: {:?} in {:?}, {} events, {orphans} never answered, {:?}", r.err().map(|v| (v.index, v.reason)), t0.elapsed(), events.len(), c.stats);
        return;
    }
    let events = parse_kv(&std::fs::read_to_string(format!("{DATA}/kv/{name}.txt")).unwrap());
    let explore = std::env::var("EXPLORE").ok().and_then(|v| v.parse().ok()).unwrap_or(20_000_000);
    let fp = std::env::var("NOFP").is_err();
    let mut c = Checker::with_partitions(Kv, HashedMap::new(), Config { max_explore: explore, footprints: fp, ..cfg(false) });
    let t0 = Instant::now();
    let r = c.check_complete(&events).map(|_| ());
    println!("{name}: {:?} in {:?}, {:?}", r.err().map(|v| (v.index, v.reason)), t0.elapsed(), c.stats);
}
