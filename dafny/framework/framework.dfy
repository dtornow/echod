include "order.dfy"

// A network of processes, generic in the process.
//
// A process is a value: its step, told the time. A system is the set of ids,
// how each one boots, the process installed at each id, and whether the
// network may drop or duplicate packets. One network runs any system.
// Deliver, fire, tick, drop and duplicate are the same transitions. A behavior
// is a moment at every time: the state, and the event that takes it to the
// next state. A trace invariant is an argument of the safety theorem, not a
// module each system has to refine.
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

  // An id is a number. The next request's id is the hash of the request it follows.
  datatype Uuid = Uuid(n: nat)

  function Hash(id: Uuid): Uuid {
    Uuid(2 * id.n + 1)
  }

  // A request carries an id. The response cites that same id, so a reply is
  // the answer to one request and not to whatever else is in flight.
  // `ask` and `ans` are separate names: a shared destructor has one type, and
  // the request body and the response body need not be the same type.
  datatype RR<Q(==, !new), A(==, !new)> = Req(id: Uuid, ask: Q) | Res(id: Uuid, ans: A)

  function ReqTo<P(!new), Q(==, !new), A(==, !new)>(to: P, id: Uuid, body: Q): Send<P, RR<Q, A>> {
    Send(to, Req(id, body))
  }

  function ResTo<P(!new), Q(==, !new), A(==, !new)>(to: P, id: Uuid, body: A): Send<P, RR<Q, A>> {
    Send(to, Res(id, body))
  }

  // Answer the request in hand. The response cites that request's id.
  function Answer<P(!new), Q(==, !new), A(==, !new)>(to: P, request: RR<Q, A>, body: A): Send<P, RR<Q, A>>
    requires request.Req?
  {
    ResTo(to, request.id, body)
  }

  // The same shape for every process: who it is, the state it holds, what
  // arrived, and the time.
  datatype Process<!P(==, !new), !M(==, !new), !S(!new)> = Process(
    step: (P, S, Input<P, M>, nat) -> Result<P, M, S>)

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

  // One moment of a trace: the state, and the event that takes it to the next state.
  datatype Moment<P(==, !new), M(==, !new), S(!new)> = Moment(state: Net<P, M, S>, event: Action<P, M>)

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
    w: Sys<P, M, S>, tr: nat -> Moment<P, M, S>)
  {
    IsInit(w, tr(0).state) && forall i: nat :: NextStep(w, tr(i).state, tr(i+1).state, tr(i).event)
  }

  ghost predicate FireEnabled<P(!new), M(!new), S(!new)>(n: Net<P, M, S>, p: P)
  {
    p in n.timers && p in n.procs && n.timers[p] <= n.now
  }

  ghost predicate SentAt<P(!new), M(!new), S(!new)>(tr: nat -> Moment<P, M, S>, j: nat, pk: Packet<P, M>)
  {
    tr(j+1).state.inflight[pk] > tr(j).state.inflight[pk]
  }

  // Named temporal patterns. Each one is a quantifier trigger.
  ghost predicate SentAfter<P(!new), M(!new), S(!new)>(tr: nat -> Moment<P, M, S>, i: nat, pk: Packet<P, M>)
  { exists j: nat {:trigger SentAt(tr, j, pk)} :: j >= i && SentAt(tr, j, pk) }

  ghost predicate DeliveredAfter<P(!new), M(!new), S(!new)>(tr: nat -> Moment<P, M, S>, i: nat, pk: Packet<P, M>)
  { exists j: nat {:trigger tr(j).event} :: j >= i && tr(j).event == Deliver(pk) }

  ghost predicate FiredAfter<P(!new), M(!new), S(!new)>(tr: nat -> Moment<P, M, S>, i: nat, p: P)
  { exists j: nat {:trigger tr(j).event} :: j >= i && tr(j).event == Fire(p) }

  ghost predicate EnabledFrom<P(!new), M(!new), S(!new)>(tr: nat -> Moment<P, M, S>, i: nat, p: P)
  { forall j: nat {:trigger tr(j).state} :: j >= i ==> FireEnabled(tr(j).state, p) }

  ghost predicate Reaches<P(!new), M(!new), S(!new)>(tr: nat -> Moment<P, M, S>, t: nat)
  { exists i: nat {:trigger tr(i).state} :: tr(i).state.now >= t }

  ghost predicate InfinitelyOftenSent<P(!new), M(!new), S(!new)>(tr: nat -> Moment<P, M, S>, pk: Packet<P, M>)
  { forall i: nat :: SentAfter(tr, i, pk) }

  ghost predicate TimeDiverges<P(!new), M(!new), S(!new)>(tr: nat -> Moment<P, M, S>)
  { forall t: nat :: Reaches(tr, t) }

  ghost predicate WeakFairFire<P(!new), M(!new), S(!new)>(tr: nat -> Moment<P, M, S>)
  { forall p: P, i: nat :: EnabledFrom(tr, i, p) ==> FiredAfter(tr, i, p) }

  ghost predicate FairLoss<P(!new), M(!new), S(!new)>(tr: nat -> Moment<P, M, S>)
  { forall pk: Packet<P, M>, i: nat :: InfinitelyOftenSent(tr, pk) ==> DeliveredAfter(tr, i, pk) }

  ghost predicate Fair<P(!new), M(!new), S(!new)>(tr: nat -> Moment<P, M, S>)
  {
    TimeDiverges(tr) && WeakFairFire(tr) && FairLoss(tr)
  }

  lemma BehaviorInv<P(!new), M(!new), S(!new)>(
    w: Sys<P, M, S>, inv: Net<P, M, S> -> bool,
    tr: nat -> Moment<P, M, S>, i: nat)
    requires IsBehavior(w, tr) && Preserves(w, inv)
    ensures inv(tr(i).state)
  {
    if i == 0 {
      assert IsInit(w, tr(0).state);
    } else {
      BehaviorInv(w, inv, tr, i - 1);
      assert NextStep(w, tr(i-1).state, tr(i).state, tr(i-1).event);
    }
  }

  ghost predicate Always<P(!new), M(!new), S(!new)>(tr: nat -> Moment<P, M, S>, i: nat, holds: Net<P, M, S> -> bool)
  { forall j: nat {:trigger tr(j).state} :: j >= i ==> holds(tr(j).state) }

  ghost predicate Eventually<P(!new), M(!new), S(!new)>(tr: nat -> Moment<P, M, S>, i: nat, holds: Net<P, M, S> -> bool)
  { exists j: nat {:trigger tr(j).state} :: j >= i && holds(tr(j).state) }

  ghost predicate ActsAfter<P(!new), M(!new), S(!new)>(tr: nat -> Moment<P, M, S>, i: nat, act: Action<P, M>)
  { exists j: nat {:trigger tr(j).event} :: j >= i && tr(j).event == act }

  ghost predicate ActsInfinitelyOften<P(!new), M(!new), S(!new)>(tr: nat -> Moment<P, M, S>, i: nat, act: Action<P, M>)
  { forall k: nat :: k >= i ==> ActsAfter(tr, k, act) }

  // Rule 1 (timers). While `holds` is true forever, it keeps p's timer pending,
  // and no step other than Fire(p) moves p's deadline: then p fires forever.
  lemma TimerRule<P(!new), M(!new), S(!new)>(
    w: Sys<P, M, S>, inv: Net<P, M, S> -> bool,
    tr: nat -> Moment<P, M, S>,
    i: nat, p: P, holds: Net<P, M, S> -> bool)
    requires IsBehavior(w, tr) && Fair(tr) && Preserves(w, inv) && Always(tr, i, holds)
    requires forall n: Net<P, M, S> :: inv(n) && holds(n) ==> p in n.timers && p in n.procs
    requires forall n: Net<P, M, S>, n': Net<P, M, S>, act: Action<P, M>
        {:trigger NextStep(w, n, n', act)} ::
      inv(n) && holds(n) && holds(n') && NextStep(w, n, n', act) && act != Fire(p) ==>
      p in n.timers && p in n'.timers && n'.timers[p] == n.timers[p]
    ensures ActsInfinitelyOften(tr, i, Fire(p))
  {
    forall k: nat | k >= i ensures ActsAfter(tr, k, Fire(p)) {
      if !FiredAfter(tr, k, p) {
        BehaviorInv(w, inv, tr, k);
        assert holds(tr(k).state);
        var d := tr(k).state.timers[p];
        assert Reaches(tr, d);
        var t: nat :| tr(t).state.now >= d;
        var m: nat := if t > k then t else k;
        forall x: nat | x >= m ensures FireEnabled(tr(x).state, p) {
          DeadlineFrozen(w, inv, tr, i, k, x, p, holds);
          TimeMonotone(w, tr, t, x);
          BehaviorInv(w, inv, tr, x);
        }
        assert EnabledFrom(tr, m, p);
        assert FiredAfter(tr, m, p);
        var y: nat :| y >= m && tr(y).event == Fire(p);
        assert false;
      }
      var y: nat :| y >= k && tr(y).event == Fire(p);
    }
  }

  lemma DeadlineFrozen<P(!new), M(!new), S(!new)>(
    w: Sys<P, M, S>, inv: Net<P, M, S> -> bool,
    tr: nat -> Moment<P, M, S>,
    i: nat, k: nat, x: nat, p: P, holds: Net<P, M, S> -> bool)
    requires IsBehavior(w, tr) && Preserves(w, inv) && Always(tr, i, holds)
    requires k >= i && x >= k && !FiredAfter(tr, k, p)
    requires forall n: Net<P, M, S> :: inv(n) && holds(n) ==> p in n.timers && p in n.procs
    requires forall n: Net<P, M, S>, n': Net<P, M, S>, act: Action<P, M>
        {:trigger NextStep(w, n, n', act)} ::
      inv(n) && holds(n) && holds(n') && NextStep(w, n, n', act) && act != Fire(p) ==>
      p in n.timers && p in n'.timers && n'.timers[p] == n.timers[p]
    ensures p in tr(x).state.timers && p in tr(k).state.timers && tr(x).state.timers[p] == tr(k).state.timers[p]
    decreases x - k
  {
    BehaviorInv(w, inv, tr, k); BehaviorInv(w, inv, tr, x);
    assert holds(tr(k).state) && holds(tr(x).state);
    if x > k {
      DeadlineFrozen(w, inv, tr, i, k, x - 1, p, holds);
      BehaviorInv(w, inv, tr, x - 1);
      assert NextStep(w, tr(x-1).state, tr(x).state, tr(x-1).event);
    }
  }

  // Rule 2 (sending). If action A happens forever while `holds` is true,
  // and each such step puts pk in flight: pk is sent forever.
  lemma SendRule<P(!new), M(!new), S(!new)>(
    w: Sys<P, M, S>, inv: Net<P, M, S> -> bool,
    tr: nat -> Moment<P, M, S>,
    i: nat, pk: Packet<P, M>, act: Action<P, M>, holds: Net<P, M, S> -> bool)
    requires IsBehavior(w, tr) && Preserves(w, inv)
    requires Always(tr, i, holds) && ActsInfinitelyOften(tr, i, act)
    requires forall n: Net<P, M, S>, n': Net<P, M, S> {:trigger NextStep(w, n, n', act)} ::
      inv(n) && holds(n) && NextStep(w, n, n', act) ==> n'.inflight[pk] > n.inflight[pk]
    ensures InfinitelyOftenSent(tr, pk)
  {
    forall k: nat ensures SentAfter(tr, k, pk) {
      var k' := if k > i then k else i;
      assert ActsAfter(tr, k', act);
      var j: nat :| j >= k' && tr(j).event == act;
      BehaviorInv(w, inv, tr, j);
      assert NextStep(w, tr(j).state, tr(j+1).state, tr(j).event);
      assert SentAt(tr, j, pk);
    }
  }

  // Rule 3 (fair loss). A packet sent forever is delivered forever, and each
  // delivery establishes whatever `after` its step gives.
  lemma DeliveryRule<P(!new), M(!new), S(!new)>(
    w: Sys<P, M, S>, inv: Net<P, M, S> -> bool,
    tr: nat -> Moment<P, M, S>,
    i: nat, pk: Packet<P, M>, after: Net<P, M, S> -> bool)
    requires IsBehavior(w, tr) && Fair(tr) && Preserves(w, inv) && InfinitelyOftenSent(tr, pk)
    requires forall n: Net<P, M, S>, n': Net<P, M, S> {:trigger NextStep(w, n, n', Deliver(pk))} ::
      inv(n) && NextStep(w, n, n', Deliver(pk)) ==> after(n')
    ensures ActsInfinitelyOften(tr, i, Deliver(pk))
    ensures Eventually(tr, i, after)
  {
    forall k: nat | k >= i ensures ActsAfter(tr, k, Deliver(pk)) {
      assert DeliveredAfter(tr, k, pk);
      var j: nat :| j >= k && tr(j).event == Deliver(pk);
    }
    assert DeliveredAfter(tr, i, pk);
    var j: nat :| j >= i && tr(j).event == Deliver(pk);
    BehaviorInv(w, inv, tr, j);
    assert NextStep(w, tr(j).state, tr(j+1).state, tr(j).event);
    assert after(tr(j+1).state);
  }

  // Rule 4 (stabilization). A bounded measure that never decreases is
  // eventually constant forever.
  lemma StabilizeRule<P(!new), M(!new), S(!new)>(
    w: Sys<P, M, S>, inv: Net<P, M, S> -> bool,
    tr: nat -> Moment<P, M, S>,
    f: Net<P, M, S> -> nat, bound: nat, i: nat) returns (s: nat)
    requires IsBehavior(w, tr) && Preserves(w, inv)
    requires forall n: Net<P, M, S> :: inv(n) ==> f(n) <= bound
    requires forall n: Net<P, M, S>, n': Net<P, M, S>, act: Action<P, M>
        {:trigger NextStep(w, n, n', act)} ::
      inv(n) && NextStep(w, n, n', act) ==> f(n) <= f(n')
    ensures s >= i && Always(tr, s, n => f(n) == f(tr(s).state))
    decreases bound - f(tr(i).state)
  {
    BehaviorInv(w, inv, tr, i);
    if Always(tr, i, n => f(n) == f(tr(i).state)) { return i; }
    var j: nat :| j >= i && f(tr(j).state) != f(tr(i).state);
    MeasureMonotone(w, inv, tr, f, i, j);
    BehaviorInv(w, inv, tr, j);
    s := StabilizeRule(w, inv, tr, f, bound, j);
  }

  lemma MeasureMonotone<P(!new), M(!new), S(!new)>(
    w: Sys<P, M, S>, inv: Net<P, M, S> -> bool,
    tr: nat -> Moment<P, M, S>,
    f: Net<P, M, S> -> nat, i: nat, j: nat)
    requires IsBehavior(w, tr) && Preserves(w, inv) && i <= j
    requires forall n: Net<P, M, S>, n': Net<P, M, S>, act: Action<P, M>
        {:trigger NextStep(w, n, n', act)} ::
      inv(n) && NextStep(w, n, n', act) ==> f(n) <= f(n')
    ensures f(tr(i).state) <= f(tr(j).state)
    decreases j - i
  {
    if i < j {
      MeasureMonotone(w, inv, tr, f, i, j - 1);
      BehaviorInv(w, inv, tr, j - 1);
      assert NextStep(w, tr(j-1).state, tr(j).state, tr(j-1).event);
    }
  }

  lemma TimeMonotone<P(!new), M(!new), S(!new)>(
    w: Sys<P, M, S>, tr: nat -> Moment<P, M, S>, i: nat, j: nat)
    requires IsBehavior(w, tr) && i <= j
    ensures tr(i).state.now <= tr(j).state.now
    decreases j - i
  {
    if i < j {
      TimeMonotone(w, tr, i, j - 1);
      assert NextStep(w, tr(j-1).state, tr(j).state, tr(j-1).event);
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
