// Actor simulation framework in Dafny.
//
//   ProcessSpec  — the "interface": a pure step function per process.
//   Network      — a nondeterministic state machine that delivers messages,
//                  fires timers (any time at/after their deadline), advances
//                  time, and optionally drops / duplicates packets.
//   Proofs are inductive invariants over Network.Next, lifted to traces.


// ---------------------------------------------------------------------------
// Process interface
// ---------------------------------------------------------------------------
abstract module ProcessSpec {
  type Pid(==, !new)
  type Msg(==, !new)
  type State(!new)

  datatype Input  = Request(from: Pid, msg: Msg) | Timeout
  datatype Send   = Send(to: Pid, msg: Msg)
  datatype TimerOp = Keep | Set(delay: nat) | Cancel   // delay is relative to "now"
  datatype Result = Result(state: State, sends: seq<Send>, timer: TimerOp)

  const Pids: set<Pid>
  function Init(self: Pid): State
  function Step(self: Pid, s: State, i: Input): Result
}

// ---------------------------------------------------------------------------
// Network
// ---------------------------------------------------------------------------
abstract module Network {
  import opened P : ProcessSpec

  const Faults: bool          // allow Drop / Duplicate?

  datatype Packet = Packet(src: Pid, dst: Pid, msg: Msg)

  datatype Net = Net(
    procs:    map<Pid, State>,
    inflight: multiset<Packet>,
    timers:   map<Pid, nat>,     // absolute deadlines
    now:      nat)

  datatype Action =
    | Deliver(p: Packet)
    | Fire(pid: Pid)
    | Tick
    | Drop(p: Packet)
    | Duplicate(p: Packet)

  function ToPackets(src: Pid, sends: seq<Send>): multiset<Packet>
  {
    if |sends| == 0 then multiset{}
    else multiset{Packet(src, sends[0].to, sends[0].msg)} + ToPackets(src, sends[1..])
  }

  lemma InToPackets(src: Pid, sends: seq<Send>, x: Packet)
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
  function Apply(n: Net, self: Pid, r: Result): Net
  {
    n.(procs    := n.procs[self := r.state],
       inflight := n.inflight + ToPackets(self, r.sends),
       timers   := match r.timer
                     case Keep   => n.timers
                     case Set(d) => n.timers[self := n.now + d]
                     case Cancel => n.timers - {self})
  }

  // Every process boots via a Timeout at time 0.
  ghost predicate Init(n: Net)
  {
    && n.procs    == (map p | p in Pids :: P.Init(p))
    && n.inflight == multiset{}
    && n.timers   == (map p | p in Pids :: 0)
    && n.now      == 0
  }

  ghost predicate NextStep(n: Net, n': Net, a: Action)
  {
    match a
    case Deliver(p) =>
      && p in n.inflight && p.dst in n.procs
      && n' == Apply(n.(inflight := n.inflight - multiset{p}), p.dst,
                     P.Step(p.dst, n.procs[p.dst], Request(p.src, p.msg)))
    case Fire(pid) =>
      && pid in n.timers && pid in n.procs && n.timers[pid] <= n.now
      && n' == Apply(n.(timers := n.timers - {pid}), pid,
                     P.Step(pid, n.procs[pid], Timeout))
    case Tick =>
      n' == n.(now := n.now + 1)
    case Drop(p) =>
      Faults && p in n.inflight && n' == n.(inflight := n.inflight - multiset{p})
    case Duplicate(p) =>
      Faults && p in n.inflight && n' == n.(inflight := n.inflight + multiset{p})
  }

  ghost predicate Next(n: Net, n': Net) { exists a :: NextStep(n, n', a) }

  ghost predicate IsTrace(t: seq<Net>)
  {
    |t| > 0 && Init(t[0]) && forall i :: 0 <= i < |t| - 1 ==> Next(t[i], t[i+1])
  }

  // --- proof obligations supplied by each concrete system -------------------
  ghost predicate Inv(n: Net)
  ghost predicate Safety(n: Net)
  lemma InitInv(n: Net)              requires Init(n)               ensures Inv(n)
  lemma NextInv(n: Net, n': Net, a: Action) requires Inv(n) && NextStep(n, n', a) ensures Inv(n')
  lemma InvSafety(n: Net)            requires Inv(n)                ensures Safety(n)

  // --- generic: invariant => safety on every state of every trace ----------
  lemma TraceSafety(t: seq<Net>)
    requires IsTrace(t)
    ensures forall i :: 0 <= i < |t| ==> Safety(t[i])
  {
    forall i | 0 <= i < |t| ensures Inv(t[i]) { TraceInv(t, i); }
    forall i | 0 <= i < |t| ensures Safety(t[i]) { InvSafety(t[i]); }
  }

  // =========================================================================
  // Liveness: infinite behaviors + fairness assumptions.
  //
  // A behavior is an infinite execution: states b(i), actions a(i).
  // Liveness ("eventually P") only holds under fairness — otherwise the
  // network may drop every message, or never let time pass. Fair says:
  //   TimeDiverges  — time is not Zeno: every deadline is eventually reached
  //   WeakFairFire  — a timer that stays due eventually fires
  //   FairLoss      — a packet sent infinitely often is eventually delivered
  //                   (drops and duplicates are still allowed, just not forever)
  // =========================================================================

  ghost predicate IsBehavior(b: nat -> Net, a: nat -> Action)
  {
    Init(b(0)) && forall i: nat :: NextStep(b(i), b(i+1), a(i))
  }

  ghost predicate FireEnabled(n: Net, p: Pid)
  {
    p in n.timers && p in n.procs && n.timers[p] <= n.now
  }

  ghost predicate SentAt(b: nat -> Net, j: nat, pk: Packet)
  {
    b(j+1).inflight[pk] > b(j).inflight[pk]
  }

  // Named temporal patterns (each one is a clean quantifier trigger for Z3).
  ghost predicate SentAfter(b: nat -> Net, i: nat, pk: Packet)
  { exists j: nat {:trigger SentAt(b, j, pk)} :: j >= i && SentAt(b, j, pk) }

  ghost predicate DeliveredAfter(a: nat -> Action, i: nat, pk: Packet)
  { exists j: nat {:trigger a(j)} :: j >= i && a(j) == Deliver(pk) }

  ghost predicate FiredAfter(a: nat -> Action, i: nat, p: Pid)
  { exists j: nat {:trigger a(j)} :: j >= i && a(j) == Fire(p) }

  ghost predicate EnabledFrom(b: nat -> Net, i: nat, p: Pid)
  { forall j: nat {:trigger b(j)} :: j >= i ==> FireEnabled(b(j), p) }

  ghost predicate Reaches(b: nat -> Net, t: nat)
  { exists i: nat {:trigger b(i)} :: b(i).now >= t }

  ghost predicate InfinitelyOftenSent(b: nat -> Net, pk: Packet)
  { forall i: nat :: SentAfter(b, i, pk) }

  ghost predicate TimeDiverges(b: nat -> Net)
  { forall t: nat :: Reaches(b, t) }

  ghost predicate WeakFairFire(b: nat -> Net, a: nat -> Action)
  { forall p: Pid, i: nat :: EnabledFrom(b, i, p) ==> FiredAfter(a, i, p) }

  ghost predicate FairLoss(b: nat -> Net, a: nat -> Action)
  { forall pk: Packet, i: nat :: InfinitelyOftenSent(b, pk) ==> DeliveredAfter(a, i, pk) }

  ghost predicate Fair(b: nat -> Net, a: nat -> Action)
  {
    TimeDiverges(b) && WeakFairFire(b, a) && FairLoss(b, a)
  }

  // Generic: the safety invariant holds on every state of a behavior.
  lemma BehaviorInv(b: nat -> Net, a: nat -> Action, i: nat)
    requires IsBehavior(b, a)
    ensures Inv(b(i))
  {
    if i == 0 { InitInv(b(0)); }
    else { BehaviorInv(b, a, i - 1); NextInv(b(i-1), b(i), a(i-1)); }
  }

  // =========================================================================
  // Reusable liveness proof rules. A protocol supplies only SINGLE-STEP facts
  // (quantified over n, n', act, assuming Inv); the rules do the temporal work.
  // =========================================================================

  ghost predicate Always(b: nat -> Net, i: nat, P: Net -> bool)
  { forall j: nat {:trigger b(j)} :: j >= i ==> P(b(j)) }

  ghost predicate Eventually(b: nat -> Net, i: nat, P: Net -> bool)
  { exists j: nat {:trigger b(j)} :: j >= i && P(b(j)) }

  ghost predicate ActsAfter(a: nat -> Action, i: nat, act: Action)
  { exists j: nat {:trigger a(j)} :: j >= i && a(j) == act }


  ghost predicate ActsInfinitelyOften(a: nat -> Action, i: nat, act: Action)
  { forall k: nat :: k >= i ==> ActsAfter(a, k, act) }

  // Rule 1 (timers). While P holds forever, P keeps p's timer pending, and no
  // step other than Fire(p) moves p's deadline: then p fires infinitely often.
  lemma TimerRule(b: nat -> Net, a: nat -> Action, i: nat, p: Pid, P: Net -> bool)
    requires IsBehavior(b, a) && Fair(b, a) && Always(b, i, P)
    requires forall n: Net :: Inv(n) && P(n) ==> p in n.timers && p in n.procs
    requires forall n: Net, n': Net, act: Action {:trigger NextStep(n, n', act)} ::
      Inv(n) && P(n) && P(n') && NextStep(n, n', act) && act != Fire(p) ==>
      p in n.timers && p in n'.timers && n'.timers[p] == n.timers[p]
    ensures ActsInfinitelyOften(a, i, Fire(p))
  {
    forall k: nat | k >= i ensures ActsAfter(a, k, Fire(p)) {
      if !FiredAfter(a, k, p) {
        BehaviorInv(b, a, k);
        assert P(b(k));
        var d := b(k).timers[p];
        assert Reaches(b, d);
        var t: nat :| b(t).now >= d;
        var m: nat := if t > k then t else k;
        forall x: nat | x >= m ensures FireEnabled(b(x), p) {
          DeadlineFrozen(b, a, i, k, x, p, P);
          TimeMonotone(b, a, t, x);
          BehaviorInv(b, a, x);
        }
        assert EnabledFrom(b, m, p);
        assert FiredAfter(a, m, p);
        var y: nat :| y >= m && a(y) == Fire(p);
        assert false;
      }
      var y: nat :| y >= k && a(y) == Fire(p);
    }
  }

  lemma DeadlineFrozen(b: nat -> Net, a: nat -> Action, i: nat, k: nat, x: nat, p: Pid, P: Net -> bool)
    requires IsBehavior(b, a) && Always(b, i, P) && k >= i && x >= k && !FiredAfter(a, k, p)
    requires forall n: Net :: Inv(n) && P(n) ==> p in n.timers && p in n.procs
    requires forall n: Net, n': Net, act: Action {:trigger NextStep(n, n', act)} ::
      Inv(n) && P(n) && P(n') && NextStep(n, n', act) && act != Fire(p) ==>
      p in n.timers && p in n'.timers && n'.timers[p] == n.timers[p]
    ensures p in b(x).timers && p in b(k).timers && b(x).timers[p] == b(k).timers[p]
    decreases x - k
  {
    BehaviorInv(b, a, k); BehaviorInv(b, a, x);
    assert P(b(k)) && P(b(x));
    if x > k {
      DeadlineFrozen(b, a, i, k, x - 1, p, P);
      BehaviorInv(b, a, x - 1);
      assert NextStep(b(x-1), b(x), a(x-1));
    }
  }

  // Rule 2 (sending). If action A happens infinitely often while P holds,
  // and each such step puts pk in flight: pk is sent infinitely often.
  lemma SendRule(b: nat -> Net, a: nat -> Action, i: nat, pk: Packet, A: Action, P: Net -> bool)
    requires IsBehavior(b, a) && Always(b, i, P) && ActsInfinitelyOften(a, i, A)
    requires forall n: Net, n': Net {:trigger NextStep(n, n', A)} ::
      Inv(n) && P(n) && NextStep(n, n', A) ==> n'.inflight[pk] > n.inflight[pk]
    ensures InfinitelyOftenSent(b, pk)
  {
    forall k: nat ensures SentAfter(b, k, pk) {
      var k' := if k > i then k else i;
      assert ActsAfter(a, k', A);
      var j: nat :| j >= k' && a(j) == A;
      BehaviorInv(b, a, j);
      assert NextStep(b(j), b(j+1), a(j));
      assert SentAt(b, j, pk);
    }
  }

  // Rule 3 (fair loss). A packet sent infinitely often is delivered
  // infinitely often, and each delivery establishes whatever Q its step gives.
  lemma DeliveryRule(b: nat -> Net, a: nat -> Action, i: nat, pk: Packet, Q: Net -> bool)
    requires IsBehavior(b, a) && Fair(b, a) && InfinitelyOftenSent(b, pk)
    requires forall n: Net, n': Net {:trigger NextStep(n, n', Deliver(pk))} ::
      Inv(n) && NextStep(n, n', Deliver(pk)) ==> Q(n')
    ensures ActsInfinitelyOften(a, i, Deliver(pk))
    ensures Eventually(b, i, Q)
  {
    forall k: nat | k >= i ensures ActsAfter(a, k, Deliver(pk)) {
      assert DeliveredAfter(a, k, pk);
      var j: nat :| j >= k && a(j) == Deliver(pk);
    }
    assert DeliveredAfter(a, i, pk);
    var j: nat :| j >= i && a(j) == Deliver(pk);
    BehaviorInv(b, a, j);
    assert NextStep(b(j), b(j+1), a(j));
    assert Q(b(j+1));
  }

  // Rule 4 (stabilization). A bounded measure that never decreases is
  // eventually constant forever.
  lemma StabilizeRule(b: nat -> Net, a: nat -> Action, f: Net -> nat, bound: nat, i: nat) returns (s: nat)
    requires IsBehavior(b, a)
    requires forall n: Net :: Inv(n) ==> f(n) <= bound
    requires forall n: Net, n': Net, act: Action {:trigger NextStep(n, n', act)} ::
      Inv(n) && NextStep(n, n', act) ==> f(n) <= f(n')
    ensures s >= i && Always(b, s, n => f(n) == f(b(s)))
    decreases bound - f(b(i))
  {
    BehaviorInv(b, a, i);
    if Always(b, i, n => f(n) == f(b(i))) { return i; }
    var j: nat :| j >= i && f(b(j)) != f(b(i));
    MeasureMonotone(b, a, f, i, j);
    BehaviorInv(b, a, j);
    s := StabilizeRule(b, a, f, bound, j);
  }

  lemma MeasureMonotone(b: nat -> Net, a: nat -> Action, f: Net -> nat, i: nat, j: nat)
    requires IsBehavior(b, a) && i <= j
    requires forall n: Net, n': Net, act: Action {:trigger NextStep(n, n', act)} ::
      Inv(n) && NextStep(n, n', act) ==> f(n) <= f(n')
    ensures f(b(i)) <= f(b(j))
    decreases j - i
  {
    if i < j {
      MeasureMonotone(b, a, f, i, j - 1);
      BehaviorInv(b, a, j - 1);
      assert NextStep(b(j-1), b(j), a(j-1));
    }
  }

  // Generic: time never goes backwards.
  lemma TimeMonotone(b: nat -> Net, a: nat -> Action, i: nat, j: nat)
    requires IsBehavior(b, a) && i <= j
    ensures b(i).now <= b(j).now
    decreases j - i
  {
    if i < j { TimeMonotone(b, a, i, j - 1); assert NextStep(b(j-1), b(j), a(j-1)); }
  }

  lemma TraceInv(t: seq<Net>, i: nat)
    requires IsTrace(t) && i < |t|
    ensures Inv(t[i])
  {
    if i == 0 { InitInv(t[0]); }
    else {
      TraceInv(t, i - 1);
      var a :| NextStep(t[i-1], t[i], a);
      NextInv(t[i-1], t[i], a);
    }
  }
}

