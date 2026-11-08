include "../framework/framework.dfy"
include "temp.dfy"

// A promise get, across the client, the node, and the bucket.
//
// The bucket holds documents. A missing key is the empty origin. The node
// asks for the origin document of the id and replies with that document's
// Get at the instant the answer arrives. A delivered reply is that Get of
// a document the bucket held at the read, and the read sits between the
// request and the reply. A dropped reply never arrives, so this says
// nothing about a client that received nothing.

module Node {
  import opened Network
  import Temp

  datatype Pid = Client | Node | Bucket
  datatype Phase = Idle | Getting(caller: Pid, id: string)
  datatype Msg =
    | PromiseGet(id: string)
    | PromiseReply(answer: Temp.Answer)
    | Get(id: string)
    | Got(id: string, doc: Temp.Doc)
  datatype State =
    | AtClient(id: string, waiting: bool)
    | AtNode(phase: Phase)
    | AtBucket(docs: map<string, Temp.Doc>)

  const Pids: set<Pid> := {Client, Node, Bucket}

  function Empty(): Temp.Doc { Temp.Origin(0, map[]) }
  function DocKey(id: string): string { "wf/" + Temp.OriginOf(id) }

  function DocumentAt(docs: map<string, Temp.Doc>, id: string): Temp.Doc {
    var key := DocKey(id);
    if key in docs then docs[key] else Empty()
  }

  function Boot(docs: map<string, Temp.Doc>, id: string, self: Pid): State {
    match self
    case Client => AtClient(id, true)
    case Node => AtNode(Idle)
    case Bucket => AtBucket(docs)
  }

  function ClientOn(s: State, i: Input<Pid, Msg>): Result<Pid, Msg, State>
    requires s.AtClient?
  {
    if s.waiting && i.Timeout? then
      Result(AtClient(s.id, false), [Send(Node, PromiseGet(s.id))], Keep)
    else Result(s, [], Keep)
  }

  function BucketOn(s: State, i: Input<Pid, Msg>): Result<Pid, Msg, State>
    requires s.AtBucket?
  {
    match i
    case Request(from, Get(id)) =>
      Result(s, [Send(from, Got(id, DocumentAt(s.docs, id)))], Keep)
    case _ => Result(s, [], Keep)
  }

  function NodeOn(s: State, i: Input<Pid, Msg>, now: nat): Result<Pid, Msg, State>
    requires s.AtNode?
  {
    match s.phase
    case Idle =>
      (match i
       case Request(from, PromiseGet(id)) =>
         Result(AtNode(Getting(from, id)), [Send(Bucket, Get(id))], Keep)
       case _ => Result(s, [], Keep))
    case Getting(caller, id) =>
      (match i
       case Request(_, Got(got, doc)) =>
         if got == id then
           var answer := Temp.Get(doc, id, now).answer;
           Result(AtNode(Idle), [Send(caller, PromiseReply(answer))], Keep)
         else Result(s, [], Keep)
       case _ => Result(s, [], Keep))
  }

  function Step(self: Pid, s: State, i: Input<Pid, Msg>, now: nat): Result<Pid, Msg, State> {
    match self
    case Client => if s.AtClient? then ClientOn(s, i) else Result(s, [], Keep)
    case Node => if s.AtNode? then NodeOn(s, i, now) else Result(s, [], Keep)
    case Bucket => if s.AtBucket? then BucketOn(s, i) else Result(s, [], Keep)
  }

  function World(docs: map<string, Temp.Doc>, id: string): Sys<Pid, Msg, State> {
    Sys(Pids, true, self => Boot(docs, id, self), Step)
  }

  // ---- what a reply is allowed to say -------------------------------------

  ghost predicate Shaped(docs: map<string, Temp.Doc>, n: Net<Pid, Msg, State>) {
    && n.procs.Keys == Pids
    && Client in n.procs && n.procs[Client].AtClient?
    && Node in n.procs && n.procs[Node].AtNode?
    && Bucket in n.procs && n.procs[Bucket].AtBucket?
    && n.procs[Bucket].docs == docs
  }

  ghost predicate GetsOk(n: Net<Pid, Msg, State>) {
    forall p {:trigger n.inflight[p]} ::
      n.inflight[p] > 0 && p.msg.Get? ==> p.src == Node && p.dst == Bucket
  }

  ghost predicate GotsOk(docs: map<string, Temp.Doc>, n: Net<Pid, Msg, State>) {
    forall p {:trigger n.inflight[p]} ::
      n.inflight[p] > 0 && p.msg.Got? ==>
        p.src == Bucket && p.dst == Node && p.msg.doc == DocumentAt(docs, p.msg.id)
  }

  function {:opaque} Lt(i: nat, n: nat): bool { i < n }

  ghost predicate Still(b: nat -> Net<Pid, Msg, State>, phase: Phase, i: nat, n: nat) {
    forall m {:trigger b(m)} :: Lt(i, m) && Lt(m, n + 1) ==>
      Node in b(m).procs && b(m).procs[Node] == AtNode(phase)
  }

  ghost predicate OpenOk(b: nat -> Net<Pid, Msg, State>, a: nat -> Action<Pid, Msg>, n: nat) {
    Node in b(n).procs && b(n).procs[Node].AtNode? &&
     (var phase := b(n).procs[Node].phase;
     phase.Getting? ==>
       exists i {:trigger a(i)} ::
         && Lt(i, n)
         && a(i) == Deliver(Packet(phase.caller, Node, PromiseGet(phase.id)))
         && Still(b, phase, i, n))
  }

  ghost predicate Justified(docs: map<string, Temp.Doc>, b: nat -> Net<Pid, Msg, State>,
                             a: nat -> Action<Pid, Msg>, limit: nat, caller: Pid, answer: Temp.Answer)
  {
    exists i, k, id, doc {:trigger a(i), a(k), Got(id, doc)} ::
      && Lt(i, k) && Lt(k, limit)
      && a(i) == Deliver(Packet(caller, Node, PromiseGet(id)))
      && a(k) == Deliver(Packet(Bucket, Node, Got(id, doc)))
      && doc == DocumentAt(docs, id)
      && answer == Temp.Get(doc, id, b(k).now).answer
      && Bucket in b(k).procs && b(k).procs[Bucket].AtBucket?
      && b(k).procs[Bucket].docs == docs
      && Node in b(k).procs && b(k).procs[Node] == AtNode(Getting(caller, id))
  }

  ghost predicate RepliesOk(docs: map<string, Temp.Doc>, b: nat -> Net<Pid, Msg, State>,
                            a: nat -> Action<Pid, Msg>, n: nat)
  {
    forall p {:trigger b(n).inflight[p]} ::
      b(n).inflight[p] > 0 && p.msg.PromiseReply? ==>
        p.src == Node && Justified(docs, b, a, n, p.dst, p.msg.answer)
  }

  ghost predicate Inv(docs: map<string, Temp.Doc>, b: nat -> Net<Pid, Msg, State>,
                      a: nat -> Action<Pid, Msg>, n: nat)
  {
    && Shaped(docs, b(n))
    && GetsOk(b(n))
    && GotsOk(docs, b(n))
    && OpenOk(b, a, n)
    && RepliesOk(docs, b, a, n)
  }

  // ---- one step of the network --------------------------------------------

  lemma InSent(self: Pid, sends: seq<Send<Pid, Msg>>, q: Packet<Pid, Msg>)
    requires q in ToPackets(self, sends)
    ensures exists i {:trigger sends[i]} :: 0 <= i < |sends| && q == Packet(self, sends[i].to, sends[i].msg)
  {
    InToPackets(self, sends, q);
  }

  lemma Split(base: Net<Pid, Msg, State>, self: Pid, r: Result<Pid, Msg, State>, q: Packet<Pid, Msg>)
    requires self in base.procs
    requires q in Advance(base, self, r).inflight
    ensures q in base.inflight || q in ToPackets(self, r.sends)
  {
    var n' := Advance(base, self, r);
    assert n'.inflight == base.inflight + ToPackets(self, r.sends);
    if q !in base.inflight {
      assert q in ToPackets(self, r.sends);
    }
  }

  lemma ShapeAt(docs: map<string, Temp.Doc>, n: Net<Pid, Msg, State>, self: Pid, s: State)
    requires Shaped(docs, n) && self in n.procs
    requires self.Client? ==> s.AtClient?
    requires self.Node? ==> s.AtNode?
    requires self.Bucket? ==> s.AtBucket? && s.docs == docs
    ensures Shaped(docs, n.(procs := n.procs[self := s]))
  {
    var n' := n.(procs := n.procs[self := s]);
    assert self in Pids;
    assert n'.procs.Keys == Pids;
    if self == Bucket {
      assert n'.procs[Bucket] == s;
    } else {
      assert n'.procs[Bucket] == n.procs[Bucket];
    }
    if self != Client { assert n'.procs[Client] == n.procs[Client]; }
    if self != Node { assert n'.procs[Node] == n.procs[Node]; }
  }

  lemma StillLater(b: nat -> Net<Pid, Msg, State>, phase: Phase, i: nat, n: nat)
    requires Still(b, phase, i, n)
    requires Node in b(n+1).procs && b(n+1).procs[Node] == AtNode(phase)
    ensures Still(b, phase, i, n+1)
  {
    reveal Lt();
    forall m {:trigger b(m)} | i < m < n + 2
      ensures Node in b(m).procs && b(m).procs[Node] == AtNode(phase)
    {
      if m < n + 1 {
        assert b(m).procs[Node] == AtNode(phase);
      }
    }
  }

  lemma OpenLater(b: nat -> Net<Pid, Msg, State>, a: nat -> Action<Pid, Msg>, n: nat)
    requires OpenOk(b, a, n)
    requires Node in b(n).procs && Node in b(n+1).procs
    requires b(n).procs[Node].AtNode? && b(n+1).procs[Node] == b(n).procs[Node]
    ensures OpenOk(b, a, n+1)
  {
    reveal Lt();
    var phase := b(n+1).procs[Node].phase;
    if phase.Getting? {
      assert b(n).procs[Node].phase == phase;
      var i :| Lt(i, n) && a(i) == Deliver(Packet(phase.caller, Node, PromiseGet(phase.id))) && Still(b, phase, i, n);
      StillLater(b, phase, i, n);
    }
  }

  lemma JustifyLater(docs: map<string, Temp.Doc>, b: nat -> Net<Pid, Msg, State>, a: nat -> Action<Pid, Msg>,
                     n: nat, caller: Pid, answer: Temp.Answer)
    requires Justified(docs, b, a, n, caller, answer)
    ensures Justified(docs, b, a, n+1, caller, answer)
  {
    reveal Lt();
    var i, k, id, doc :|
      && Lt(i, k) && Lt(k, n)
      && a(i) == Deliver(Packet(caller, Node, PromiseGet(id)))
      && a(k) == Deliver(Packet(Bucket, Node, Got(id, doc)))
      && doc == DocumentAt(docs, id)
      && answer == Temp.Get(doc, id, b(k).now).answer
      && Bucket in b(k).procs && b(k).procs[Bucket].AtBucket?
      && b(k).procs[Bucket].docs == docs
      && Node in b(k).procs && b(k).procs[Node] == AtNode(Getting(caller, id));
    assert Lt(k, n + 1);
  }

  lemma Carry(docs: map<string, Temp.Doc>, b: nat -> Net<Pid, Msg, State>, a: nat -> Action<Pid, Msg>, n: nat)
    requires Inv(docs, b, a, n)
    requires Shaped(docs, b(n+1))
    requires b(n+1).procs[Node] == b(n).procs[Node]
    requires forall q :: q in b(n+1).inflight && q.msg.Get? ==> q in b(n).inflight
    requires forall q :: q in b(n+1).inflight && q.msg.Got? ==> q in b(n).inflight
    requires forall q :: q in b(n+1).inflight && q.msg.PromiseReply? ==> q in b(n).inflight
    ensures Inv(docs, b, a, n+1)
  {
    forall p | p in b(n+1).inflight && p.msg.Get?
      ensures p.src == Node && p.dst == Bucket
    {
      assert p in b(n).inflight;
    }
    forall p | p in b(n+1).inflight && p.msg.Got?
      ensures p.src == Bucket && p.dst == Node && p.msg.doc == DocumentAt(docs, p.msg.id)
    {
      assert p in b(n).inflight;
    }
    forall p | p in b(n+1).inflight && p.msg.PromiseReply?
      ensures p.src == Node && Justified(docs, b, a, n+1, p.dst, p.msg.answer)
    {
      assert p in b(n).inflight;
      assert Justified(docs, b, a, n, p.dst, p.msg.answer);
      JustifyLater(docs, b, a, n, p.dst, p.msg.answer);
    }
    OpenLater(b, a, n);
  }

  lemma NoSuch(self: Pid, sends: seq<Send<Pid, Msg>>, q: Packet<Pid, Msg>)
    requires q in ToPackets(self, sends)
    requires q.msg.Got? || q.msg.PromiseReply?
    requires q.msg.Got? ==> forall i {:trigger sends[i]} :: 0 <= i < |sends| ==> !sends[i].msg.Got?
    requires q.msg.PromiseReply? ==> forall i {:trigger sends[i]} :: 0 <= i < |sends| ==> !sends[i].msg.PromiseReply?
    ensures false
  {
    InSent(self, sends, q);
    var i :| 0 <= i < |sends| && q == Packet(self, sends[i].to, sends[i].msg);
    assert q.msg == sends[i].msg;
    if q.msg.Got? {
      assert !sends[i].msg.Got?;
    } else {
      assert q.msg.PromiseReply?;
      assert !sends[i].msg.PromiseReply?;
    }
  }

  lemma OldPackets(base: Net<Pid, Msg, State>, self: Pid, r: Result<Pid, Msg, State>,
                   q: Packet<Pid, Msg>, got: bool)
    requires self in base.procs
    requires q in Advance(base, self, r).inflight
    requires if got then q.msg.Got? else q.msg.PromiseReply?
    requires forall i {:trigger r.sends[i]} :: 0 <= i < |r.sends| ==> if got then !r.sends[i].msg.Got? else !r.sends[i].msg.PromiseReply?
    ensures q in base.inflight
  {
    Split(base, self, r, q);
    if q !in base.inflight {
      NoSuch(self, r.sends, q);
    }
  }

  lemma SameShape(docs: map<string, Temp.Doc>, n: Net<Pid, Msg, State>, m: Net<Pid, Msg, State>)
    requires Shaped(docs, n) && m.procs == n.procs
    ensures Shaped(docs, m)
  {
  }

  lemma Booted(docs: map<string, Temp.Doc>, ask: string, n: Net<Pid, Msg, State>)
    requires IsInit(World(docs, ask), n)
    ensures Shaped(docs, n)
    ensures n.inflight == multiset{}
    ensures n.procs[Node] == AtNode(Idle)
  {
    var w := World(docs, ask);
    assert n.procs == (map p | p in w.pids :: w.init(p));
    assert w.init(Node) == Boot(docs, ask, Node) == AtNode(Idle);
    assert n.procs[Node] == AtNode(Idle);
    assert n.procs[Bucket] == AtBucket(docs);
    assert n.procs[Client] == AtClient(ask, true);
    assert n.procs.Keys == Pids;
  }

  lemma QuietStep(docs: map<string, Temp.Doc>, b: nat -> Net<Pid, Msg, State>, a: nat -> Action<Pid, Msg>,
                  n: nat, base: Net<Pid, Msg, State>, self: Pid, r: Result<Pid, Msg, State>)
    requires Inv(docs, b, a, n)
    requires self in b(n).procs && base.procs == b(n).procs
    requires forall q :: q in base.inflight ==> q in b(n).inflight
    requires b(n+1) == Advance(base, self, r)
    requires self.Node? ==> r.state == b(n).procs[Node]
    requires self.Client? ==> r.state.AtClient?
    requires self.Bucket? ==> r.state == b(n).procs[Bucket]
    requires forall i {:trigger r.sends[i]} :: 0 <= i < |r.sends| ==> !r.sends[i].msg.Get? && !r.sends[i].msg.Got? && !r.sends[i].msg.PromiseReply?
    ensures Inv(docs, b, a, n+1)
  {
    ShapeAt(docs, b(n), self, r.state);
    assert b(n+1).procs == b(n).procs[self := r.state];
    assert b(n+1).procs[Node] == b(n).procs[Node];
    forall q | q in b(n+1).inflight && q.msg.Get?
      ensures q in b(n).inflight
    {
      OldKind(base, self, r, q);
    }
    forall q | q in b(n+1).inflight && q.msg.Got?
      ensures q in b(n).inflight
    {
      OldPackets(base, self, r, q, true);
    }
    forall q | q in b(n+1).inflight && q.msg.PromiseReply?
      ensures q in b(n).inflight
    {
      OldPackets(base, self, r, q, false);
    }
    Carry(docs, b, a, n);
  }

  lemma OldKind(base: Net<Pid, Msg, State>, self: Pid, r: Result<Pid, Msg, State>, q: Packet<Pid, Msg>)
    requires self in base.procs
    requires q in Advance(base, self, r).inflight && q.msg.Get?
    requires forall i {:trigger r.sends[i]} :: 0 <= i < |r.sends| ==> !r.sends[i].msg.Get?
    ensures q in base.inflight
  {
    Split(base, self, r, q);
    if q !in base.inflight {
      InSent(self, r.sends, q);
      var i :| 0 <= i < |r.sends| && q == Packet(self, r.sends[i].to, r.sends[i].msg);
      assert !r.sends[i].msg.Get?;
    }
  }

  lemma OnTimeout(self: Pid, s: State, now: nat)
    requires self == Client ==> s.AtClient?
    requires self == Node ==> s.AtNode?
    requires self == Bucket ==> s.AtBucket?
    ensures var r := Step(self, s, Timeout, now);
      if self == Client && s.waiting then
        r == Result(AtClient(s.id, false), [Send(Node, PromiseGet(s.id))], Keep)
      else r == Result(s, [], Keep)
  {
  }

  lemma StepOk(docs: map<string, Temp.Doc>, ask: string, b: nat -> Net<Pid, Msg, State>,
               a: nat -> Action<Pid, Msg>, n: nat)
    requires IsBehavior(World(docs, ask), b, a) && Inv(docs, b, a, n)
    ensures Inv(docs, b, a, n+1)
  {
    var w := World(docs, ask);
    assert w.step == Step;
    assert NextStep(w, b(n), b(n+1), a(n));
    match a(n)
    case Tick =>
      assert b(n+1) == b(n).(now := b(n).now + 1);
      SameShape(docs, b(n), b(n+1));
      Carry(docs, b, a, n);
    case Drop(p) =>
      assert b(n+1) == b(n).(inflight := b(n).inflight - multiset{p});
      SameShape(docs, b(n), b(n+1));
      forall q | q in b(n+1).inflight ensures q in b(n).inflight {}
      Carry(docs, b, a, n);
    case Duplicate(p) =>
      assert b(n+1) == b(n).(inflight := b(n).inflight + multiset{p});
      SameShape(docs, b(n), b(n+1));
      forall q | q in b(n+1).inflight ensures q in b(n).inflight {
        if q != p { assert b(n).inflight[q] == b(n+1).inflight[q]; }
      }
      Carry(docs, b, a, n);
    case Fire(pid) =>
      var base := b(n).(timers := b(n).timers - {pid});
      var r := Step(pid, b(n).procs[pid], Timeout, b(n).now);
      assert base.inflight == b(n).inflight && base.procs == b(n).procs;
      assert b(n+1) == Advance(base, pid, r);
      OnTimeout(pid, b(n).procs[pid], b(n).now);
      QuietStep(docs, b, a, n, base, pid, r);
    case Deliver(p) =>
      DeliverOk(docs, ask, b, a, n, p);
  }

  lemma DeliverOk(docs: map<string, Temp.Doc>, ask: string, b: nat -> Net<Pid, Msg, State>,
                  a: nat -> Action<Pid, Msg>, n: nat, p: Packet<Pid, Msg>)
    requires IsBehavior(World(docs, ask), b, a) && Inv(docs, b, a, n)
    requires a(n) == Deliver(p)
    ensures Inv(docs, b, a, n+1)
  {
    var w := World(docs, ask);
    assert w.step == Step;
    assert NextStep(w, b(n), b(n+1), Deliver(p));
    var base := b(n).(inflight := b(n).inflight - multiset{p});
    var r := Step(p.dst, b(n).procs[p.dst], Request(p.src, p.msg), b(n).now);
    assert base.procs == b(n).procs && b(n+1) == Advance(base, p.dst, r);
    forall q | q in base.inflight ensures q in b(n).inflight {}
    match p.dst
    case Client =>
      assert r == Result(b(n).procs[Client], [], Keep);
      QuietStep(docs, b, a, n, base, Client, r);
    case Bucket =>
      BucketDeliver(docs, b, a, n, base, p, r);
    case Node =>
      NodeDeliver(docs, b, a, n, base, p, r);
  }

  lemma BucketDeliver(docs: map<string, Temp.Doc>, b: nat -> Net<Pid, Msg, State>, a: nat -> Action<Pid, Msg>,
                      n: nat, base: Net<Pid, Msg, State>, p: Packet<Pid, Msg>, r: Result<Pid, Msg, State>)
    requires Inv(docs, b, a, n)
    requires p.dst == Bucket && p in b(n).inflight
    requires base == b(n).(inflight := b(n).inflight - multiset{p})
    requires r == Step(Bucket, b(n).procs[Bucket], Request(p.src, p.msg), b(n).now)
    requires b(n+1) == Advance(base, Bucket, r)
    requires forall q :: q in base.inflight ==> q in b(n).inflight
    ensures Inv(docs, b, a, n+1)
  {
    match p.msg
    case Get(id) =>
      assert p.src == Node && p.dst == Bucket;
      assert b(n).procs[Bucket] == AtBucket(docs);
      var doc := DocumentAt(docs, id);
      assert r == Result(AtBucket(docs), [Send(Node, Got(id, doc))], Keep);
      var born := Packet(Bucket, Node, Got(id, doc));
      ShapeAt(docs, b(n), Bucket, r.state);
      assert b(n+1).procs == b(n).procs[Bucket := r.state];
      assert b(n+1).procs[Node] == b(n).procs[Node];
      forall q | q in b(n+1).inflight && q.msg.Get?
        ensures q.src == Node && q.dst == Bucket
      {
        OldKind(base, Bucket, r, q);
        assert q in base.inflight && q in b(n).inflight;
      }
      forall q | q in b(n+1).inflight && q.msg.PromiseReply?
        ensures q.src == Node && Justified(docs, b, a, n+1, q.dst, q.msg.answer)
      {
        OldPackets(base, Bucket, r, q, false);
        assert q in base.inflight && q in b(n).inflight;
        JustifyLater(docs, b, a, n, q.dst, q.msg.answer);
      }
      forall q | q in b(n+1).inflight && q.msg.Got?
        ensures q.src == Bucket && q.dst == Node && q.msg.doc == DocumentAt(docs, q.msg.id)
      {
        if q == born {
        } else {
          Split(base, Bucket, r, q);
          if q !in base.inflight { InSent(Bucket, r.sends, q); }
          assert q in base.inflight;
          assert q in b(n).inflight;
        }
      }
      OpenLater(b, a, n);
    case _ =>
      assert r == Result(b(n).procs[Bucket], [], Keep);
      QuietStep(docs, b, a, n, base, Bucket, r);
  }

  lemma NodeDeliver(docs: map<string, Temp.Doc>, b: nat -> Net<Pid, Msg, State>, a: nat -> Action<Pid, Msg>,
                    n: nat, base: Net<Pid, Msg, State>, p: Packet<Pid, Msg>, r: Result<Pid, Msg, State>)
    requires Inv(docs, b, a, n)
    requires a(n) == Deliver(p)
    requires p.dst == Node && p in b(n).inflight
    requires base == b(n).(inflight := b(n).inflight - multiset{p})
    requires r == Step(Node, b(n).procs[Node], Request(p.src, p.msg), b(n).now)
    requires b(n+1) == Advance(base, Node, r)
    requires forall q :: q in base.inflight ==> q in b(n).inflight
    ensures Inv(docs, b, a, n+1)
  {
    var s := b(n).procs[Node];
    if s.phase.Idle? && p.msg.PromiseGet? {
      var id := p.msg.id;
      assert r == Result(AtNode(Getting(p.src, id)), [Send(Bucket, Get(id))], Keep);
      var phase := Getting(p.src, id);
      var born := Packet(Node, Bucket, Get(id));
      ShapeAt(docs, b(n), Node, r.state);
      assert b(n+1).procs == b(n).procs[Node := r.state];
      assert b(n+1).procs[Node] == AtNode(phase);
      reveal Lt();
      forall m {:trigger b(m)} | n < m < n + 2
        ensures Node in b(m).procs && b(m).procs[Node] == AtNode(phase)
      { assert m == n+1; }
      assert Still(b, phase, n, n+1);
      assert a(n) == Deliver(Packet(p.src, Node, PromiseGet(id)));
      forall q | q in b(n+1).inflight && q.msg.Got? ensures q in b(n).inflight {
        OldPackets(base, Node, r, q, true);
        assert q in base.inflight;
      }
      forall q | q in b(n+1).inflight && q.msg.PromiseReply? ensures q in b(n).inflight {
        OldPackets(base, Node, r, q, false);
        assert q in base.inflight;
      }
      forall q | q in b(n+1).inflight && q.msg.Get?
        ensures q.src == Node && q.dst == Bucket
      {
        if q != born {
          Split(base, Node, r, q);
          if q !in base.inflight { InSent(Node, r.sends, q); assert q == born; }
          assert q in base.inflight && q in b(n).inflight;
        }
      }
    } else if s.phase.Getting? && p.msg.Got? && p.msg.id == s.phase.id {
      var caller := s.phase.caller;
      var id := s.phase.id;
      var doc := p.msg.doc;
      assert p.src == Bucket && doc == DocumentAt(docs, id);
      var answer := Temp.Get(doc, id, b(n).now).answer;
      assert r == Result(AtNode(Idle), [Send(caller, PromiseReply(answer))], Keep);
      ShapeAt(docs, b(n), Node, r.state);
      assert b(n+1).procs == b(n).procs[Node := r.state];
      assert b(n+1).procs[Node] == AtNode(Idle);
      var born := Packet(Node, caller, PromiseReply(answer));
      forall q | q in b(n+1).inflight && q.msg.Get? ensures q in b(n).inflight {
        OldKind(base, Node, r, q);
        assert q in base.inflight;
      }
      forall q | q in b(n+1).inflight && q.msg.Got? ensures q in b(n).inflight {
        OldPackets(base, Node, r, q, true);
        assert q in base.inflight;
      }
      forall q | q in b(n+1).inflight && q.msg.PromiseReply?
        ensures q.src == Node && Justified(docs, b, a, n+1, q.dst, q.msg.answer)
      {
        if q == born {
          reveal Lt();
          var phase := Getting(caller, id);
          var i :| Lt(i, n) && a(i) == Deliver(Packet(caller, Node, PromiseGet(id))) && Still(b, phase, i, n);
          assert Lt(n, n + 1);
          assert a(n) == Deliver(Packet(Bucket, Node, Got(id, doc)));
          assert Justified(docs, b, a, n+1, caller, answer);
        } else {
          Split(base, Node, r, q);
          if q !in base.inflight { InSent(Node, r.sends, q); assert q == born; }
          assert q in base.inflight;
          assert q in b(n).inflight;
          JustifyLater(docs, b, a, n, q.dst, q.msg.answer);
        }
      }
    } else {
      assert r == Result(s, [], Keep);
      QuietStep(docs, b, a, n, base, Node, r);
    }
  }

  lemma Safe(docs: map<string, Temp.Doc>, ask: string, b: nat -> Net<Pid, Msg, State>,
             a: nat -> Action<Pid, Msg>, n: nat)
    requires IsBehavior(World(docs, ask), b, a)
    ensures Inv(docs, b, a, n)
    decreases n
  {
    if n == 0 {
      assert IsInit(World(docs, ask), b(0));
      Booted(docs, ask, b(0));
    } else {
      Safe(docs, ask, b, a, n - 1);
      StepOk(docs, ask, b, a, n - 1);
    }
  }

  lemma Cases(doc: Temp.Doc, id: string, now: nat)
    ensures var answer := Temp.Get(doc, id, now).answer;
      && (id !in Temp.ObjectsOf(doc) ==> answer == Temp.Answer(404, Temp.None))
      && (id in Temp.ObjectsOf(doc) ==>
           answer == Temp.Answer(200, Temp.Some(Temp.Project(Temp.ObjectsOf(doc)[id], now).promise)))
  {
    var shown := Temp.Opened(doc);
    assert Temp.ObjectsOf(shown) == Temp.ObjectsOf(doc);
  }

  lemma PromiseGetReceived(docs: map<string, Temp.Doc>, ask: string, b: nat -> Net<Pid, Msg, State>,
                           a: nat -> Action<Pid, Msg>, r: nat, from: Pid, answer: Temp.Answer)
    requires IsBehavior(World(docs, ask), b, a)
    requires a(r) == Deliver(Packet(Node, from, PromiseReply(answer)))
    ensures exists i: nat, k: nat, id, doc {:trigger a(i), a(k), Got(id, doc)} ::
      && i < k < r
      && a(i) == Deliver(Packet(from, Node, PromiseGet(id)))
      && a(k) == Deliver(Packet(Bucket, Node, Got(id, doc)))
      && doc == DocumentAt(docs, id)
      && Bucket in b(k).procs && b(k).procs[Bucket].AtBucket?
      && b(k).procs[Bucket].docs == docs
      && answer == Temp.Get(doc, id, b(k).now).answer
      && (id !in Temp.ObjectsOf(doc) ==> answer == Temp.Answer(404, Temp.None))
      && (id in Temp.ObjectsOf(doc) ==>
           answer == Temp.Answer(200, Temp.Some(Temp.Project(Temp.ObjectsOf(doc)[id], b(k).now).promise)))
  {
    Safe(docs, ask, b, a, r);
    var w := World(docs, ask);
    assert NextStep(w, b(r), b(r+1), a(r));
    var pk := Packet(Node, from, PromiseReply(answer));
    reveal Lt();
    assert pk in b(r).inflight;
    assert Justified(docs, b, a, r, from, answer);
    var i, k, id, doc :|
      && Lt(i, k) && Lt(k, r)
      && a(i) == Deliver(Packet(from, Node, PromiseGet(id)))
      && a(k) == Deliver(Packet(Bucket, Node, Got(id, doc)))
      && doc == DocumentAt(docs, id)
      && Bucket in b(k).procs && b(k).procs[Bucket].AtBucket?
      && b(k).procs[Bucket].docs == docs
      && answer == Temp.Get(doc, id, b(k).now).answer;
    Cases(doc, id, b(k).now);
  }
}
