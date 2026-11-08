include "order.dfy"

// A network of processes, generic in the process.
//
// A process is a value: its step, told the time. A system is the set of ids,
// how each one boots, the process installed at each id, and whether the
// network may drop or duplicate packets. One network runs any system.
// Deliver, fire, tick, drop and duplicate are the same transitions; a trace
// invariant is an argument of the safety theorem, not a module each system
// has to refine.
//
// Liveness ("eventually") holds only under fairness, otherwise the network
// may drop every message or never let time pass:
//   TimeDiverges  — every deadline is eventually reached
//   WeakFairFire  — a timer that stays due eventually fires
//   FairLoss      — a packet sent infinitely often is eventually delivered
// The four rules (Timer, Send, Delivery, Stabilize) do the temporal work.
// A protocol supplies the single-step facts.

module Network {
  datatype Input<P(!new), M(!new)> = Request(from: P, msg: M) | Timeout
  datatype Send<P(!new), M(!new)> = Send(to: P, msg: M)
  datatype TimerOp = Keep | Set(delay: nat) | Cancel   // delay is relative to "now"
  datatype Result<P(!new), M(!new), S(!new)> = Result(state: S, sends: seq<Send<P, M>>, timer: TimerOp)

  // The interface of a process: who it is, the state it holds, what arrived,
  // and the time. A datatype implements it, so the process is a value.
  // `{:termination false}` lets that datatype live in another module. `step`
  // does not call itself through the trait.
  trait {:termination false} Process<!P(==, !new), !M(==, !new), !S(!new)> {
    function step(self: P, s: S, i: Input<P, M>, now: nat): Result<P, M, S>
      decreases now
  }

  // The processes, plugged in. `!` because each type occurs under a function arrow.
  // `!new` because a trace quantifies over these values, so they are not references.
  // One process per id. A delivery or a timer calls that process's step.
  datatype Sys<!P(==, !new), !M(==, !new), !S(!new)> = Sys(
    pids: set<P>,
    faults: bool,
    init: P -> S,
    process: P -> Process<P, M, S>)

  datatype Packet<P(==, !new), M(==, !new)> = Packet(src: P, dst: P, msg: M)

  datatype Net<P(==, !new), M(==, !new), S(!new)> = Net(
    procs:    map<P, S>,
    inflight: multiset<Packet<P, M>>,
    timers:   map<P, nat>,     // absolute deadlines
    now:      nat)

  datatype Action<P(==, !new), M(==, !new)> =
    | Deliver(p: Packet<P, M>)
    | Fire(pid: P)
    | Tick
    | Drop(p: Packet<P, M>)
    | Duplicate(p: Packet<P, M>)

  function ToPackets<P(==, !new), M(==, !new)>(src: P, sends: seq<Send<P, M>>): multiset<Packet<P, M>>
  {
    if |sends| == 0 then multiset{}
    else multiset{Packet(src, sends[0].to, sends[0].msg)} + ToPackets(src, sends[1..])
  }

  lemma InToPackets<P(!new), M(!new)>(src: P, sends: seq<Send<P, M>>, x: Packet<P, M>)
    requires x in ToPackets(src, sends)
    ensures exists i :: 0 <= i < |sends| && x == Packet(src, sends[i].to, sends[i].msg)
    decreases |sends|
  {
    if x != Packet(src, sends[0].to, sends[0].msg) {
      InToPackets(src, sends[1..], x);
      var i :| 0 <= i < |sends[1..]| && x == Packet(src, sends[1..][i].to, sends[1..][i].msg);
      assert x == Packet(src, sends[i+1].to, sends[i+1].msg);
    }
  }

  // Accept whatever the process returned.
  function Advance<P(==, !new), M(==, !new), S(!new)>(
    n: Net<P, M, S>, self: P, r: Result<P, M, S>
  ): Net<P, M, S>
  {
    Net(n.procs[self := r.state],
        n.inflight + ToPackets(self, r.sends),
        match r.timer
          case Keep   => n.timers
          case Set(d) => n.timers[self := n.now + d]
          case Cancel => n.timers - {self},
        n.now)
  }

  // Every process boots via a Timeout at time 0.
  ghost predicate IsInit<P(!new), M(!new), S(!new)>(w: Sys<P, M, S>, n: Net<P, M, S>)
  {
    && n.procs    == (map p | p in w.pids :: w.init(p))
    && n.inflight == multiset{}
    && n.timers   == (map p | p in w.pids :: 0)
    && n.now      == 0
  }

  ghost predicate NextStep<P(!new), M(!new), S(!new)>(
    w: Sys<P, M, S>, n: Net<P, M, S>, n': Net<P, M, S>, a: Action<P, M>)
  {
    match a
    case Deliver(p) =>
      && p in n.inflight && p.dst in n.procs
      && n' == Advance(n.(inflight := n.inflight - multiset{p}), p.dst,
                       w.process(p.dst).step(p.dst, n.procs[p.dst], Request(p.src, p.msg), n.now))
    case Fire(pid) =>
      && pid in n.timers && pid in n.procs && n.timers[pid] <= n.now
      && n' == Advance(n.(timers := n.timers - {pid}), pid,
                       w.process(pid).step(pid, n.procs[pid], Timeout, n.now))
    case Tick =>
      n' == n.(now := n.now + 1)
    case Drop(p) =>
      w.faults && p in n.inflight && n' == n.(inflight := n.inflight - multiset{p})
    case Duplicate(p) =>
      w.faults && p in n.inflight && n' == n.(inflight := n.inflight + multiset{p})
  }

  ghost predicate Next<P(!new), M(!new), S(!new)>(
    w: Sys<P, M, S>, n: Net<P, M, S>, n': Net<P, M, S>)
  { exists a :: NextStep(w, n, n', a) }

  ghost predicate IsTrace<P(!new), M(!new), S(!new)>(w: Sys<P, M, S>, t: seq<Net<P, M, S>>)
  {
    |t| > 0 && IsInit(w, t[0]) && forall i :: 0 <= i < |t| - 1 ==> Next(w, t[i], t[i+1])
  }

  // `inv` holds at boot and is kept by every transition.
  ghost predicate Preserves<P(!new), M(!new), S(!new)>(w: Sys<P, M, S>, inv: Net<P, M, S> -> bool)
  {
    && (forall n {:trigger IsInit(w, n)} :: IsInit(w, n) ==> inv(n))
    && (forall n, n', a {:trigger NextStep(w, n, n', a)} ::
          inv(n) && NextStep(w, n, n', a) ==> inv(n'))
  }

  lemma TraceSafety<P(!new), M(!new), S(!new)>(
    w: Sys<P, M, S>, inv: Net<P, M, S> -> bool, safe: Net<P, M, S> -> bool,
    t: seq<Net<P, M, S>>)
    requires IsTrace(w, t) && Preserves(w, inv)
    requires forall n :: inv(n) ==> safe(n)
    ensures forall i :: 0 <= i < |t| ==> safe(t[i])
  {
    forall i | 0 <= i < |t| ensures inv(t[i]) { TraceInv(w, inv, t, i); }
    forall i | 0 <= i < |t| ensures safe(t[i]) { }
  }

  ghost predicate IsBehavior<P(!new), M(!new), S(!new)>(
    w: Sys<P, M, S>, b: nat -> Net<P, M, S>, a: nat -> Action<P, M>)
  {
    IsInit(w, b(0)) && forall i: nat :: NextStep(w, b(i), b(i+1), a(i))
  }

  ghost predicate FireEnabled<P(!new), M(!new), S(!new)>(n: Net<P, M, S>, p: P)
  {
    p in n.timers && p in n.procs && n.timers[p] <= n.now
  }

  ghost predicate SentAt<P(!new), M(!new), S(!new)>(b: nat -> Net<P, M, S>, j: nat, pk: Packet<P, M>)
  {
    b(j+1).inflight[pk] > b(j).inflight[pk]
  }

  // Named temporal patterns. Each one is a quantifier trigger.
  ghost predicate SentAfter<P(!new), M(!new), S(!new)>(b: nat -> Net<P, M, S>, i: nat, pk: Packet<P, M>)
  { exists j: nat {:trigger SentAt(b, j, pk)} :: j >= i && SentAt(b, j, pk) }

  ghost predicate DeliveredAfter<P(!new), M(!new)>(a: nat -> Action<P, M>, i: nat, pk: Packet<P, M>)
  { exists j: nat {:trigger a(j)} :: j >= i && a(j) == Deliver(pk) }

  ghost predicate FiredAfter<P(!new), M(!new)>(a: nat -> Action<P, M>, i: nat, p: P)
  { exists j: nat {:trigger a(j)} :: j >= i && a(j) == Fire(p) }

  ghost predicate EnabledFrom<P(!new), M(!new), S(!new)>(b: nat -> Net<P, M, S>, i: nat, p: P)
  { forall j: nat {:trigger b(j)} :: j >= i ==> FireEnabled(b(j), p) }

  ghost predicate Reaches<P(!new), M(!new), S(!new)>(b: nat -> Net<P, M, S>, t: nat)
  { exists i: nat {:trigger b(i)} :: b(i).now >= t }

  ghost predicate InfinitelyOftenSent<P(!new), M(!new), S(!new)>(b: nat -> Net<P, M, S>, pk: Packet<P, M>)
  { forall i: nat :: SentAfter(b, i, pk) }

  ghost predicate TimeDiverges<P(!new), M(!new), S(!new)>(b: nat -> Net<P, M, S>)
  { forall t: nat :: Reaches(b, t) }

  ghost predicate WeakFairFire<P(!new), M(!new), S(!new)>(b: nat -> Net<P, M, S>, a: nat -> Action<P, M>)
  { forall p: P, i: nat :: EnabledFrom(b, i, p) ==> FiredAfter(a, i, p) }

  ghost predicate FairLoss<P(!new), M(!new), S(!new)>(b: nat -> Net<P, M, S>, a: nat -> Action<P, M>)
  { forall pk: Packet<P, M>, i: nat :: InfinitelyOftenSent(b, pk) ==> DeliveredAfter(a, i, pk) }

  ghost predicate Fair<P(!new), M(!new), S(!new)>(b: nat -> Net<P, M, S>, a: nat -> Action<P, M>)
  {
    TimeDiverges(b) && WeakFairFire(b, a) && FairLoss(b, a)
  }

  lemma BehaviorInv<P(!new), M(!new), S(!new)>(
    w: Sys<P, M, S>, inv: Net<P, M, S> -> bool,
    b: nat -> Net<P, M, S>, a: nat -> Action<P, M>, i: nat)
    requires IsBehavior(w, b, a) && Preserves(w, inv)
    ensures inv(b(i))
  {
    if i == 0 {
      assert IsInit(w, b(0));
    } else {
      BehaviorInv(w, inv, b, a, i - 1);
      assert NextStep(w, b(i-1), b(i), a(i-1));
    }
  }

  ghost predicate Always<P(!new), M(!new), S(!new)>(b: nat -> Net<P, M, S>, i: nat, holds: Net<P, M, S> -> bool)
  { forall j: nat {:trigger b(j)} :: j >= i ==> holds(b(j)) }

  ghost predicate Eventually<P(!new), M(!new), S(!new)>(b: nat -> Net<P, M, S>, i: nat, holds: Net<P, M, S> -> bool)
  { exists j: nat {:trigger b(j)} :: j >= i && holds(b(j)) }

  ghost predicate ActsAfter<P(!new), M(!new)>(a: nat -> Action<P, M>, i: nat, act: Action<P, M>)
  { exists j: nat {:trigger a(j)} :: j >= i && a(j) == act }

  ghost predicate ActsInfinitelyOften<P(!new), M(!new)>(a: nat -> Action<P, M>, i: nat, act: Action<P, M>)
  { forall k: nat :: k >= i ==> ActsAfter(a, k, act) }

  // Rule 1 (timers). While `holds` is true forever, it keeps p's timer pending,
  // and no step other than Fire(p) moves p's deadline: then p fires forever.
  lemma TimerRule<P(!new), M(!new), S(!new)>(
    w: Sys<P, M, S>, inv: Net<P, M, S> -> bool,
    b: nat -> Net<P, M, S>, a: nat -> Action<P, M>,
    i: nat, p: P, holds: Net<P, M, S> -> bool)
    requires IsBehavior(w, b, a) && Fair(b, a) && Preserves(w, inv) && Always(b, i, holds)
    requires forall n: Net<P, M, S> :: inv(n) && holds(n) ==> p in n.timers && p in n.procs
    requires forall n: Net<P, M, S>, n': Net<P, M, S>, act: Action<P, M>
        {:trigger NextStep(w, n, n', act)} ::
      inv(n) && holds(n) && holds(n') && NextStep(w, n, n', act) && act != Fire(p) ==>
      p in n.timers && p in n'.timers && n'.timers[p] == n.timers[p]
    ensures ActsInfinitelyOften(a, i, Fire(p))
  {
    forall k: nat | k >= i ensures ActsAfter(a, k, Fire(p)) {
      if !FiredAfter(a, k, p) {
        BehaviorInv(w, inv, b, a, k);
        assert holds(b(k));
        var d := b(k).timers[p];
        assert Reaches(b, d);
        var t: nat :| b(t).now >= d;
        var m: nat := if t > k then t else k;
        forall x: nat | x >= m ensures FireEnabled(b(x), p) {
          DeadlineFrozen(w, inv, b, a, i, k, x, p, holds);
          TimeMonotone(w, b, a, t, x);
          BehaviorInv(w, inv, b, a, x);
        }
        assert EnabledFrom(b, m, p);
        assert FiredAfter(a, m, p);
        var y: nat :| y >= m && a(y) == Fire(p);
        assert false;
      }
      var y: nat :| y >= k && a(y) == Fire(p);
    }
  }

  lemma DeadlineFrozen<P(!new), M(!new), S(!new)>(
    w: Sys<P, M, S>, inv: Net<P, M, S> -> bool,
    b: nat -> Net<P, M, S>, a: nat -> Action<P, M>,
    i: nat, k: nat, x: nat, p: P, holds: Net<P, M, S> -> bool)
    requires IsBehavior(w, b, a) && Preserves(w, inv) && Always(b, i, holds)
    requires k >= i && x >= k && !FiredAfter(a, k, p)
    requires forall n: Net<P, M, S> :: inv(n) && holds(n) ==> p in n.timers && p in n.procs
    requires forall n: Net<P, M, S>, n': Net<P, M, S>, act: Action<P, M>
        {:trigger NextStep(w, n, n', act)} ::
      inv(n) && holds(n) && holds(n') && NextStep(w, n, n', act) && act != Fire(p) ==>
      p in n.timers && p in n'.timers && n'.timers[p] == n.timers[p]
    ensures p in b(x).timers && p in b(k).timers && b(x).timers[p] == b(k).timers[p]
    decreases x - k
  {
    BehaviorInv(w, inv, b, a, k); BehaviorInv(w, inv, b, a, x);
    assert holds(b(k)) && holds(b(x));
    if x > k {
      DeadlineFrozen(w, inv, b, a, i, k, x - 1, p, holds);
      BehaviorInv(w, inv, b, a, x - 1);
      assert NextStep(w, b(x-1), b(x), a(x-1));
    }
  }

  // Rule 2 (sending). If action A happens forever while `holds` is true,
  // and each such step puts pk in flight: pk is sent forever.
  lemma SendRule<P(!new), M(!new), S(!new)>(
    w: Sys<P, M, S>, inv: Net<P, M, S> -> bool,
    b: nat -> Net<P, M, S>, a: nat -> Action<P, M>,
    i: nat, pk: Packet<P, M>, act: Action<P, M>, holds: Net<P, M, S> -> bool)
    requires IsBehavior(w, b, a) && Preserves(w, inv)
    requires Always(b, i, holds) && ActsInfinitelyOften(a, i, act)
    requires forall n: Net<P, M, S>, n': Net<P, M, S> {:trigger NextStep(w, n, n', act)} ::
      inv(n) && holds(n) && NextStep(w, n, n', act) ==> n'.inflight[pk] > n.inflight[pk]
    ensures InfinitelyOftenSent(b, pk)
  {
    forall k: nat ensures SentAfter(b, k, pk) {
      var k' := if k > i then k else i;
      assert ActsAfter(a, k', act);
      var j: nat :| j >= k' && a(j) == act;
      BehaviorInv(w, inv, b, a, j);
      assert NextStep(w, b(j), b(j+1), a(j));
      assert SentAt(b, j, pk);
    }
  }

  // Rule 3 (fair loss). A packet sent forever is delivered forever, and each
  // delivery establishes whatever `after` its step gives.
  lemma DeliveryRule<P(!new), M(!new), S(!new)>(
    w: Sys<P, M, S>, inv: Net<P, M, S> -> bool,
    b: nat -> Net<P, M, S>, a: nat -> Action<P, M>,
    i: nat, pk: Packet<P, M>, after: Net<P, M, S> -> bool)
    requires IsBehavior(w, b, a) && Fair(b, a) && Preserves(w, inv) && InfinitelyOftenSent(b, pk)
    requires forall n: Net<P, M, S>, n': Net<P, M, S> {:trigger NextStep(w, n, n', Deliver(pk))} ::
      inv(n) && NextStep(w, n, n', Deliver(pk)) ==> after(n')
    ensures ActsInfinitelyOften(a, i, Deliver(pk))
    ensures Eventually(b, i, after)
  {
    forall k: nat | k >= i ensures ActsAfter(a, k, Deliver(pk)) {
      assert DeliveredAfter(a, k, pk);
      var j: nat :| j >= k && a(j) == Deliver(pk);
    }
    assert DeliveredAfter(a, i, pk);
    var j: nat :| j >= i && a(j) == Deliver(pk);
    BehaviorInv(w, inv, b, a, j);
    assert NextStep(w, b(j), b(j+1), a(j));
    assert after(b(j+1));
  }

  // Rule 4 (stabilization). A bounded measure that never decreases is
  // eventually constant forever.
  lemma StabilizeRule<P(!new), M(!new), S(!new)>(
    w: Sys<P, M, S>, inv: Net<P, M, S> -> bool,
    b: nat -> Net<P, M, S>, a: nat -> Action<P, M>,
    f: Net<P, M, S> -> nat, bound: nat, i: nat) returns (s: nat)
    requires IsBehavior(w, b, a) && Preserves(w, inv)
    requires forall n: Net<P, M, S> :: inv(n) ==> f(n) <= bound
    requires forall n: Net<P, M, S>, n': Net<P, M, S>, act: Action<P, M>
        {:trigger NextStep(w, n, n', act)} ::
      inv(n) && NextStep(w, n, n', act) ==> f(n) <= f(n')
    ensures s >= i && Always(b, s, n => f(n) == f(b(s)))
    decreases bound - f(b(i))
  {
    BehaviorInv(w, inv, b, a, i);
    if Always(b, i, n => f(n) == f(b(i))) { return i; }
    var j: nat :| j >= i && f(b(j)) != f(b(i));
    MeasureMonotone(w, inv, b, a, f, i, j);
    BehaviorInv(w, inv, b, a, j);
    s := StabilizeRule(w, inv, b, a, f, bound, j);
  }

  lemma MeasureMonotone<P(!new), M(!new), S(!new)>(
    w: Sys<P, M, S>, inv: Net<P, M, S> -> bool,
    b: nat -> Net<P, M, S>, a: nat -> Action<P, M>,
    f: Net<P, M, S> -> nat, i: nat, j: nat)
    requires IsBehavior(w, b, a) && Preserves(w, inv) && i <= j
    requires forall n: Net<P, M, S>, n': Net<P, M, S>, act: Action<P, M>
        {:trigger NextStep(w, n, n', act)} ::
      inv(n) && NextStep(w, n, n', act) ==> f(n) <= f(n')
    ensures f(b(i)) <= f(b(j))
    decreases j - i
  {
    if i < j {
      MeasureMonotone(w, inv, b, a, f, i, j - 1);
      BehaviorInv(w, inv, b, a, j - 1);
      assert NextStep(w, b(j-1), b(j), a(j-1));
    }
  }

  lemma TimeMonotone<P(!new), M(!new), S(!new)>(
    w: Sys<P, M, S>, b: nat -> Net<P, M, S>, a: nat -> Action<P, M>, i: nat, j: nat)
    requires IsBehavior(w, b, a) && i <= j
    ensures b(i).now <= b(j).now
    decreases j - i
  {
    if i < j {
      TimeMonotone(w, b, a, i, j - 1);
      assert NextStep(w, b(j-1), b(j), a(j-1));
    }
  }

  lemma TraceInv<P(!new), M(!new), S(!new)>(
    w: Sys<P, M, S>, inv: Net<P, M, S> -> bool, t: seq<Net<P, M, S>>, i: nat)
    requires IsTrace(w, t) && Preserves(w, inv) && i < |t|
    ensures inv(t[i])
  {
    if i == 0 {
      assert IsInit(w, t[0]);
    } else {
      TraceInv(w, inv, t, i - 1);
      var a :| NextStep(w, t[i-1], t[i], a);
    }
  }
}
