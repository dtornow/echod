include "../framework/framework.dfy"
include "temp.dfy"

// A promise get, across the clients, the nodes, and the one bucket.
//
// A world names its clients and its nodes. The bucket is the single store,
// and it holds the documents. A missing key is the empty origin. Each client
// asks one node for one id. Each node holds the set of gets in flight, one
// continuation per id: the caller to answer when the bucket returns that id.
// Many gets sit in that set at once, and many nodes hold such sets at once.
// A delivered reply is the Get of a document the bucket held at the read,
// and the read sits between the request and the reply, on the node that
// answers, while that continuation was in its set. A dropped reply never
// arrives, so this says nothing about a client that received nothing.

module Node {
  import opened Network
  import Temp

  datatype Pid = Client(c: nat) | Node(i: nat) | Bucket
  datatype Cont = WaitGet(caller: Pid)
  datatype Ask = Ask(id: string, node: nat)
  datatype Msg =
    | PromiseGet(id: string)
    | PromiseReply(answer: Temp.Answer)
    | Get(id: string)
    | Got(id: string, doc: Temp.Doc)
  datatype State =
    | AtClient(id: string, node: nat, waiting: bool)
    | AtNode(open: map<string, Cont>)
    | AtBucket(docs: map<string, Temp.Doc>)

  function Empty(): Temp.Doc { Temp.Origin(0, map[]) }
  function DocKey(id: string): string { "wf/" + Temp.OriginOf(id) }

  function DocumentAt(docs: map<string, Temp.Doc>, id: string): Temp.Doc {
    var key := DocKey(id);
    if key in docs then docs[key] else Empty()
  }

  function Pids(clients: set<nat>, nodes: set<nat>): set<Pid> {
    (set c | c in clients :: Client(c)) + (set i | i in nodes :: Node(i)) + {Bucket}
  }

  ghost predicate Routed(clients: set<nat>, nodes: set<nat>, ask: nat -> Ask) {
    forall c {:trigger ask(c)} :: c in clients ==> ask(c).node in nodes
  }

  function Boot(docs: map<string, Temp.Doc>, ask: nat -> Ask, self: Pid): State {
    match self
    case Client(c) => AtClient(ask(c).id, ask(c).node, true)
    case Node(_) => AtNode(map[])
    case Bucket => AtBucket(docs)
  }

  function ClientOn(s: State, i: Input<Pid, Msg>): Result<Pid, Msg, State>
    requires s.AtClient?
  {
    if s.waiting && i.Timeout? then
      Result(AtClient(s.id, s.node, false), [Send(Node(s.node), PromiseGet(s.id))], Keep)
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
    match i
    case Request(from, PromiseGet(id)) =>
      if id in s.open then Result(s, [], Keep)
      else Result(AtNode(s.open[id := WaitGet(from)]), [Send(Bucket, Get(id))], Keep)
    case Request(_, Got(id, doc)) =>
      if id in s.open then
        var answer := Temp.Get(doc, id, now).answer;
        Result(AtNode(s.open - {id}), [Send(s.open[id].caller, PromiseReply(answer))], Keep)
      else Result(s, [], Keep)
    case _ => Result(s, [], Keep)
  }

  function Step(self: Pid, s: State, i: Input<Pid, Msg>, now: nat): Result<Pid, Msg, State> {
    match self
    case Client(_) => if s.AtClient? then ClientOn(s, i) else Result(s, [], Keep)
    case Node(_) => if s.AtNode? then NodeOn(s, i, now) else Result(s, [], Keep)
    case Bucket => if s.AtBucket? then BucketOn(s, i) else Result(s, [], Keep)
  }

  function World(docs: map<string, Temp.Doc>, clients: set<nat>, nodes: set<nat>, ask: nat -> Ask): Sys<Pid, Msg, State>
    requires Routed(clients, nodes, ask)
  {
    Sys(Pids(clients, nodes), true, self => Boot(docs, ask, self), Step)
  }

  // ---- what a reply is allowed to say -------------------------------------

  ghost predicate Shaped(docs: map<string, Temp.Doc>, n: Net<Pid, Msg, State>) {
    && Bucket in n.procs
    && n.procs[Bucket].AtBucket?
    && n.procs[Bucket].docs == docs
    && (forall p {:trigger n.procs[p]} ::
         p in n.procs && p.Client? ==>
           && n.procs[p].AtClient?
           && Node(n.procs[p].node) in n.procs)
    && (forall p {:trigger n.procs[p]} ::
         p in n.procs && p.Node? ==> n.procs[p].AtNode?)
  }

  ghost predicate GetsOk(n: Net<Pid, Msg, State>) {
    forall p {:trigger n.inflight[p]} ::
      n.inflight[p] > 0 && p.msg.Get? ==> p.src.Node? && p.src in n.procs && p.dst == Bucket
  }

  ghost predicate GotsOk(docs: map<string, Temp.Doc>, n: Net<Pid, Msg, State>) {
    forall p {:trigger n.inflight[p]} ::
      n.inflight[p] > 0 && p.msg.Got? ==>
        && p.src == Bucket && p.dst.Node? && p.dst in n.procs
        && p.msg.doc == DocumentAt(docs, p.msg.id)
  }

  function {:opaque} Lt(i: nat, n: nat): bool { i < n }

  // `id` has waited for `caller` on `node` at every state strictly after the request.
  ghost predicate Held(b: nat -> Net<Pid, Msg, State>, node: Pid, id: string, caller: Pid, i: nat, n: nat) {
    forall m {:trigger b(m)} :: Lt(i, m) && Lt(m, n + 1) ==>
      && node in b(m).procs
      && b(m).procs[node].AtNode?
      && id in b(m).procs[node].open
      && b(m).procs[node].open[id] == WaitGet(caller)
  }

  ghost predicate Entry(b: nat -> Net<Pid, Msg, State>, a: nat -> Action<Pid, Msg>, n: nat, node: Pid, id: string) {
    && node in b(n).procs && node.Node? && b(n).procs[node].AtNode?
    && id in b(n).procs[node].open
    && (var caller := b(n).procs[node].open[id].caller;
        exists i {:trigger a(i)} ::
          && Lt(i, n)
          && a(i) == Deliver(Packet(caller, node, PromiseGet(id)))
          && Held(b, node, id, caller, i, n))
  }

  ghost predicate NodeOpen(b: nat -> Net<Pid, Msg, State>, a: nat -> Action<Pid, Msg>, n: nat, node: Pid) {
    && node in b(n).procs && node.Node? && b(n).procs[node].AtNode?
    && (forall id {:trigger b(n).procs[node].open[id]} ::
         id in b(n).procs[node].open ==> Entry(b, a, n, node, id))
  }

  ghost predicate OpenOk(b: nat -> Net<Pid, Msg, State>, a: nat -> Action<Pid, Msg>, n: nat) {
    forall node {:trigger b(n).procs[node]} ::
      node in b(n).procs && node.Node? ==> NodeOpen(b, a, n, node)
  }

  ghost predicate Justified(docs: map<string, Temp.Doc>, b: nat -> Net<Pid, Msg, State>,
                             a: nat -> Action<Pid, Msg>, limit: nat, node: Pid, caller: Pid, answer: Temp.Answer)
  {
    exists i, k, id, doc {:trigger a(i), a(k), Got(id, doc)} ::
      && Lt(i, k) && Lt(k, limit)
      && node.Node?
      && a(i) == Deliver(Packet(caller, node, PromiseGet(id)))
      && a(k) == Deliver(Packet(Bucket, node, Got(id, doc)))
      && doc == DocumentAt(docs, id)
      && answer == Temp.Get(doc, id, b(k).now).answer
      && Bucket in b(k).procs && b(k).procs[Bucket].AtBucket?
      && b(k).procs[Bucket].docs == docs
      && node in b(k).procs && b(k).procs[node].AtNode?
      && id in b(k).procs[node].open
      && b(k).procs[node].open[id] == WaitGet(caller)
  }

  ghost predicate RepliesOk(docs: map<string, Temp.Doc>, b: nat -> Net<Pid, Msg, State>,
                            a: nat -> Action<Pid, Msg>, n: nat)
  {
    forall p {:trigger b(n).inflight[p]} ::
      b(n).inflight[p] > 0 && p.msg.PromiseReply? ==>
        p.src.Node? && Justified(docs, b, a, n, p.src, p.dst, p.msg.answer)
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

  lemma ClientIn(clients: set<nat>, nodes: set<nat>, c: nat)
    requires c in clients
    ensures Client(c) in Pids(clients, nodes)
  {
    assert Client(c) in (set x | x in clients :: Client(x));
  }

  lemma NodeIn(clients: set<nat>, nodes: set<nat>, i: nat)
    requires i in nodes
    ensures Node(i) in Pids(clients, nodes)
  {
    assert Node(i) in (set x | x in nodes :: Node(x));
  }

  lemma BucketIn(clients: set<nat>, nodes: set<nat>)
    ensures Bucket in Pids(clients, nodes)
  {
    assert Bucket in {Bucket};
  }

  lemma ClientIndex(clients: set<nat>, nodes: set<nat>, p: Pid)
    requires p in Pids(clients, nodes) && p.Client?
    ensures p.c in clients
  {
    if p.c !in clients {
      assert p !in (set c | c in clients :: Client(c)) by {
        if p in (set c | c in clients :: Client(c)) {
          var c :| c in clients && Client(c) == p;
          assert c == p.c;
        }
      }
      assert p !in (set i | i in nodes :: Node(i)) by {
        if p in (set i | i in nodes :: Node(i)) {
          var i :| i in nodes && Node(i) == p;
          assert p.Node?;
        }
      }
      assert p != Bucket;
    }
  }

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
    requires self.Client? ==> s.AtClient? && Node(s.node) in n.procs
    requires self.Node? ==> s.AtNode?
    requires self.Bucket? ==> s.AtBucket? && s.docs == docs
    ensures Shaped(docs, n.(procs := n.procs[self := s]))
  {
    var n' := n.(procs := n.procs[self := s]);
    assert n'.procs.Keys == n.procs.Keys;
    if self.Bucket? {
      assert n'.procs[Bucket] == s;
    } else {
      assert n'.procs[Bucket] == n.procs[Bucket];
    }
    forall p | p in n'.procs && p.Client?
      ensures n'.procs[p].AtClient? && Node(n'.procs[p].node) in n'.procs
    {
      if p == self {
        assert n'.procs[p] == s;
        assert Node(s.node) in n'.procs.Keys;
      } else {
        assert n'.procs[p] == n.procs[p];
        assert Node(n.procs[p].node) in n.procs;
        assert Node(n.procs[p].node) in n'.procs.Keys;
      }
    }
    forall p | p in n'.procs && p.Node?
      ensures n'.procs[p].AtNode?
    {
      if p == self {
        assert n'.procs[p] == s;
      } else {
        assert n'.procs[p] == n.procs[p];
      }
    }
  }

  lemma HeldLater(b: nat -> Net<Pid, Msg, State>, node: Pid, id: string, caller: Pid, i: nat, n: nat)
    requires Held(b, node, id, caller, i, n)
    requires node in b(n+1).procs && b(n+1).procs[node].AtNode?
    requires id in b(n+1).procs[node].open && b(n+1).procs[node].open[id] == WaitGet(caller)
    ensures Held(b, node, id, caller, i, n+1)
  {
    reveal Lt();
    forall m {:trigger b(m)} | i < m < n + 2
      ensures node in b(m).procs && b(m).procs[node].AtNode?
        && id in b(m).procs[node].open && b(m).procs[node].open[id] == WaitGet(caller)
    {
      if m < n + 1 {
        assert b(m).procs[node].open[id] == WaitGet(caller);
      }
    }
  }

  lemma OpenFrame(b: nat -> Net<Pid, Msg, State>, a: nat -> Action<Pid, Msg>, n: nat, node: Pid)
    requires OpenOk(b, a, n)
    requires node.Node? && node in b(n).procs && node in b(n+1).procs
    requires b(n+1).procs[node] == b(n).procs[node]
    ensures NodeOpen(b, a, n+1, node)
  {
    reveal Lt();
    var open := b(n+1).procs[node].open;
    forall id | id in open
      ensures Entry(b, a, n+1, node, id)
    {
      var caller := open[id].caller;
      assert Entry(b, a, n, node, id);
      var i :| Lt(i, n) && a(i) == Deliver(Packet(caller, node, PromiseGet(id))) && Held(b, node, id, caller, i, n);
      HeldLater(b, node, id, caller, i, n);
      assert Lt(i, n + 1);
    }
  }

  lemma OpenSame(b: nat -> Net<Pid, Msg, State>, a: nat -> Action<Pid, Msg>, n: nat)
    requires OpenOk(b, a, n)
    requires b(n+1).procs.Keys == b(n).procs.Keys
    requires forall node :: node in b(n).procs && node.Node? ==> b(n+1).procs[node] == b(n).procs[node]
    ensures OpenOk(b, a, n+1)
  {
    forall node | node in b(n+1).procs && node.Node?
      ensures NodeOpen(b, a, n+1, node)
    {
      assert node in b(n).procs;
      OpenFrame(b, a, n, node);
    }
  }

  lemma JustifyLater(docs: map<string, Temp.Doc>, b: nat -> Net<Pid, Msg, State>, a: nat -> Action<Pid, Msg>,
                     n: nat, node: Pid, caller: Pid, answer: Temp.Answer)
    requires Justified(docs, b, a, n, node, caller, answer)
    ensures Justified(docs, b, a, n+1, node, caller, answer)
  {
    reveal Lt();
    var i, k, id, doc :|
      && Lt(i, k) && Lt(k, n)
      && node.Node?
      && a(i) == Deliver(Packet(caller, node, PromiseGet(id)))
      && a(k) == Deliver(Packet(Bucket, node, Got(id, doc)))
      && doc == DocumentAt(docs, id)
      && answer == Temp.Get(doc, id, b(k).now).answer
      && Bucket in b(k).procs && b(k).procs[Bucket].AtBucket?
      && b(k).procs[Bucket].docs == docs
      && node in b(k).procs && b(k).procs[node].AtNode?
      && id in b(k).procs[node].open
      && b(k).procs[node].open[id] == WaitGet(caller);
    assert Lt(k, n + 1);
  }

  lemma Carry(docs: map<string, Temp.Doc>, b: nat -> Net<Pid, Msg, State>, a: nat -> Action<Pid, Msg>, n: nat)
    requires Inv(docs, b, a, n)
    requires Shaped(docs, b(n+1))
    requires b(n+1).procs.Keys == b(n).procs.Keys
    requires forall node :: node in b(n).procs && node.Node? ==> b(n+1).procs[node] == b(n).procs[node]
    requires forall q :: q in b(n+1).inflight && q.msg.Get? ==> q in b(n).inflight
    requires forall q :: q in b(n+1).inflight && q.msg.Got? ==> q in b(n).inflight
    requires forall q :: q in b(n+1).inflight && q.msg.PromiseReply? ==> q in b(n).inflight
    ensures Inv(docs, b, a, n+1)
  {
    forall p | p in b(n+1).inflight && p.msg.Get?
      ensures p.src.Node? && p.src in b(n+1).procs && p.dst == Bucket
    {
      assert p in b(n).inflight;
      assert p.src in b(n).procs;
      assert p.src in b(n+1).procs.Keys;
    }
    forall p | p in b(n+1).inflight && p.msg.Got?
      ensures p.src == Bucket && p.dst.Node? && p.dst in b(n+1).procs && p.msg.doc == DocumentAt(docs, p.msg.id)
    {
      assert p in b(n).inflight;
      assert p.dst in b(n).procs;
      assert p.dst in b(n+1).procs.Keys;
    }
    forall p | p in b(n+1).inflight && p.msg.PromiseReply?
      ensures p.src.Node? && Justified(docs, b, a, n+1, p.src, p.dst, p.msg.answer)
    {
      assert p in b(n).inflight;
      assert Justified(docs, b, a, n, p.src, p.dst, p.msg.answer);
      JustifyLater(docs, b, a, n, p.src, p.dst, p.msg.answer);
    }
    OpenSame(b, a, n);
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

  lemma Booted(docs: map<string, Temp.Doc>, clients: set<nat>, nodes: set<nat>, ask: nat -> Ask, n: Net<Pid, Msg, State>)
    requires Routed(clients, nodes, ask)
    requires IsInit(World(docs, clients, nodes, ask), n)
    ensures Shaped(docs, n)
    ensures n.inflight == multiset{}
    ensures forall p {:trigger n.procs[p]} :: p in n.procs && p.Node? ==> n.procs[p] == AtNode(map[])
  {
    var w := World(docs, clients, nodes, ask);
    assert n.procs == (map p | p in w.pids :: w.init(p));
    assert w.pids == Pids(clients, nodes);
    assert n.procs.Keys == w.pids;
    BucketIn(clients, nodes);
    assert n.procs[Bucket] == w.init(Bucket) == Boot(docs, ask, Bucket) == AtBucket(docs);
    forall p | p in n.procs && p.Client?
      ensures n.procs[p].AtClient? && Node(n.procs[p].node) in n.procs
    {
      ClientIndex(clients, nodes, p);
      var c := p.c;
      assert n.procs[p] == w.init(p) == Boot(docs, ask, p) == AtClient(ask(c).id, ask(c).node, true);
      NodeIn(clients, nodes, ask(c).node);
      assert Node(ask(c).node) in n.procs.Keys;
    }
    forall p | p in n.procs && p.Node?
      ensures n.procs[p] == AtNode(map[])
    {
      assert n.procs[p] == w.init(p) == Boot(docs, ask, p) == AtNode(map[]);
    }
  }

  lemma QuietStep(docs: map<string, Temp.Doc>, b: nat -> Net<Pid, Msg, State>, a: nat -> Action<Pid, Msg>,
                  n: nat, base: Net<Pid, Msg, State>, self: Pid, r: Result<Pid, Msg, State>)
    requires Inv(docs, b, a, n)
    requires self in b(n).procs && base.procs == b(n).procs
    requires forall q :: q in base.inflight ==> q in b(n).inflight
    requires b(n+1) == Advance(base, self, r)
    requires self.Node? ==> r.state == b(n).procs[self]
    requires self.Client? ==> r.state.AtClient? && Node(r.state.node) in b(n).procs
    requires self.Bucket? ==> r.state == b(n).procs[Bucket]
    requires forall i {:trigger r.sends[i]} :: 0 <= i < |r.sends| ==> !r.sends[i].msg.Get? && !r.sends[i].msg.Got? && !r.sends[i].msg.PromiseReply?
    ensures Inv(docs, b, a, n+1)
  {
    ShapeAt(docs, b(n), self, r.state);
    assert b(n+1).procs == b(n).procs[self := r.state];
    assert b(n+1).procs.Keys == b(n).procs.Keys;
    forall node | node in b(n).procs && node.Node?
      ensures b(n+1).procs[node] == b(n).procs[node]
    {
      if node == self {
        assert r.state == b(n).procs[self];
      }
    }
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
    requires self.Client? ==> s.AtClient?
    requires self.Node? ==> s.AtNode?
    requires self.Bucket? ==> s.AtBucket?
    ensures var r := Step(self, s, Timeout, now);
      if self.Client? && s.waiting then
        r == Result(AtClient(s.id, s.node, false), [Send(Node(s.node), PromiseGet(s.id))], Keep)
      else r == Result(s, [], Keep)
  {
  }

  lemma StepOk(docs: map<string, Temp.Doc>, clients: set<nat>, nodes: set<nat>, ask: nat -> Ask,
               b: nat -> Net<Pid, Msg, State>, a: nat -> Action<Pid, Msg>, n: nat)
    requires Routed(clients, nodes, ask)
    requires IsBehavior(World(docs, clients, nodes, ask), b, a) && Inv(docs, b, a, n)
    ensures Inv(docs, b, a, n+1)
  {
    var w := World(docs, clients, nodes, ask);
    assert w.step == Step;
    assert NextStep(w, b(n), b(n+1), a(n));
    match a(n)
    case Tick =>
      assert b(n+1) == b(n).(now := b(n).now + 1);
      SameShape(docs, b(n), b(n+1));
      assert b(n+1).procs.Keys == b(n).procs.Keys;
      forall node | node in b(n).procs && node.Node? ensures b(n+1).procs[node] == b(n).procs[node] {}
      forall q | q in b(n+1).inflight ensures q in b(n).inflight {}
      Carry(docs, b, a, n);
    case Drop(p) =>
      assert b(n+1) == b(n).(inflight := b(n).inflight - multiset{p});
      SameShape(docs, b(n), b(n+1));
      assert b(n+1).procs.Keys == b(n).procs.Keys;
      forall node | node in b(n).procs && node.Node? ensures b(n+1).procs[node] == b(n).procs[node] {}
      forall q | q in b(n+1).inflight ensures q in b(n).inflight {}
      Carry(docs, b, a, n);
    case Duplicate(p) =>
      assert b(n+1) == b(n).(inflight := b(n).inflight + multiset{p});
      SameShape(docs, b(n), b(n+1));
      assert b(n+1).procs.Keys == b(n).procs.Keys;
      forall node | node in b(n).procs && node.Node? ensures b(n+1).procs[node] == b(n).procs[node] {}
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
      if pid.Client? {
        assert b(n).procs[pid].AtClient?;
        assert r.state.node == b(n).procs[pid].node;
        assert Node(r.state.node) in b(n).procs;
      }
      QuietStep(docs, b, a, n, base, pid, r);
    case Deliver(p) =>
      DeliverOk(docs, clients, nodes, ask, b, a, n, p);
  }

  lemma DeliverOk(docs: map<string, Temp.Doc>, clients: set<nat>, nodes: set<nat>, ask: nat -> Ask,
                  b: nat -> Net<Pid, Msg, State>, a: nat -> Action<Pid, Msg>, n: nat, p: Packet<Pid, Msg>)
    requires Routed(clients, nodes, ask)
    requires IsBehavior(World(docs, clients, nodes, ask), b, a) && Inv(docs, b, a, n)
    requires a(n) == Deliver(p)
    ensures Inv(docs, b, a, n+1)
  {
    var w := World(docs, clients, nodes, ask);
    assert w.step == Step;
    assert NextStep(w, b(n), b(n+1), Deliver(p));
    var base := b(n).(inflight := b(n).inflight - multiset{p});
    var r := Step(p.dst, b(n).procs[p.dst], Request(p.src, p.msg), b(n).now);
    assert base.procs == b(n).procs && b(n+1) == Advance(base, p.dst, r);
    forall q | q in base.inflight ensures q in b(n).inflight {}
    match p.dst
    case Client(_) =>
      var s := b(n).procs[p.dst];
      assert s.AtClient?;
      assert r == Result(s, [], Keep);
      assert Node(r.state.node) in b(n).procs;
      QuietStep(docs, b, a, n, base, p.dst, r);
    case Bucket =>
      BucketDeliver(docs, b, a, n, base, p, r);
    case Node(_) =>
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
      assert p.src.Node? && p.src in b(n).procs && p.dst == Bucket;
      assert b(n).procs[Bucket] == AtBucket(docs);
      var who := p.src;
      var doc := DocumentAt(docs, id);
      assert r == Result(AtBucket(docs), [Send(who, Got(id, doc))], Keep);
      var born := Packet(Bucket, who, Got(id, doc));
      ShapeAt(docs, b(n), Bucket, r.state);
      assert b(n+1).procs == b(n).procs[Bucket := r.state];
      assert b(n+1).procs.Keys == b(n).procs.Keys;
      forall node | node in b(n).procs && node.Node?
        ensures b(n+1).procs[node] == b(n).procs[node]
      { assert node != Bucket; }
      forall q | q in b(n+1).inflight && q.msg.Get?
        ensures q.src.Node? && q.src in b(n+1).procs && q.dst == Bucket
      {
        OldKind(base, Bucket, r, q);
        assert q in base.inflight && q in b(n).inflight;
        assert q.src in b(n+1).procs.Keys;
      }
      forall q | q in b(n+1).inflight && q.msg.PromiseReply?
        ensures q.src.Node? && Justified(docs, b, a, n+1, q.src, q.dst, q.msg.answer)
      {
        OldPackets(base, Bucket, r, q, false);
        assert q in base.inflight && q in b(n).inflight;
        JustifyLater(docs, b, a, n, q.src, q.dst, q.msg.answer);
      }
      forall q | q in b(n+1).inflight && q.msg.Got?
        ensures q.src == Bucket && q.dst.Node? && q.dst in b(n+1).procs && q.msg.doc == DocumentAt(docs, q.msg.id)
      {
        if q == born {
          assert who in b(n+1).procs.Keys;
        } else {
          Split(base, Bucket, r, q);
          if q !in base.inflight { InSent(Bucket, r.sends, q); }
          assert q in base.inflight;
          assert q in b(n).inflight;
          assert q.dst in b(n+1).procs.Keys;
        }
      }
      OpenSame(b, a, n);
    case _ =>
      assert r == Result(b(n).procs[Bucket], [], Keep);
      QuietStep(docs, b, a, n, base, Bucket, r);
  }

  lemma NodeDeliver(docs: map<string, Temp.Doc>, b: nat -> Net<Pid, Msg, State>, a: nat -> Action<Pid, Msg>,
                    n: nat, base: Net<Pid, Msg, State>, p: Packet<Pid, Msg>, r: Result<Pid, Msg, State>)
    requires Inv(docs, b, a, n)
    requires a(n) == Deliver(p)
    requires p.dst.Node? && p.dst in b(n).procs && p in b(n).inflight
    requires base == b(n).(inflight := b(n).inflight - multiset{p})
    requires r == Step(p.dst, b(n).procs[p.dst], Request(p.src, p.msg), b(n).now)
    requires b(n+1) == Advance(base, p.dst, r)
    requires forall q :: q in base.inflight ==> q in b(n).inflight
    ensures Inv(docs, b, a, n+1)
  {
    var self := p.dst;
    var s := b(n).procs[self];
    if p.msg.PromiseGet? && p.msg.id !in s.open {
      var id := p.msg.id;
      var caller := p.src;
      var open' := s.open[id := WaitGet(caller)];
      assert r == Result(AtNode(open'), [Send(Bucket, Get(id))], Keep);
      var born := Packet(self, Bucket, Get(id));
      ShapeAt(docs, b(n), self, r.state);
      assert b(n+1).procs == b(n).procs[self := r.state];
      assert b(n+1).procs.Keys == b(n).procs.Keys;
      assert b(n+1).procs[self] == AtNode(open');
      reveal Lt();
      forall m {:trigger b(m)} | n < m < n + 2
        ensures self in b(m).procs && b(m).procs[self].AtNode?
          && id in b(m).procs[self].open && b(m).procs[self].open[id] == WaitGet(caller)
      { assert m == n + 1; }
      assert Held(b, self, id, caller, n, n + 1);
      assert a(n) == Deliver(Packet(caller, self, PromiseGet(id)));
      forall node | node in b(n+1).procs && node.Node?
        ensures NodeOpen(b, a, n+1, node)
      {
        if node == self {
          forall oid | oid in open'
            ensures Entry(b, a, n+1, self, oid)
          {
            if oid == id {
              assert Lt(n, n + 1);
            } else {
              assert oid in s.open && open'[oid] == s.open[oid];
              var c := s.open[oid].caller;
              assert Entry(b, a, n, self, oid);
              var i :| Lt(i, n) && a(i) == Deliver(Packet(c, self, PromiseGet(oid))) && Held(b, self, oid, c, i, n);
              HeldLater(b, self, oid, c, i, n);
              assert Lt(i, n + 1);
            }
          }
        } else {
          assert b(n+1).procs[node] == b(n).procs[node];
          OpenFrame(b, a, n, node);
        }
      }
      forall q | q in b(n+1).inflight && q.msg.Got? ensures q in b(n).inflight {
        OldPackets(base, self, r, q, true);
        assert q in base.inflight;
      }
      forall q | q in b(n+1).inflight && q.msg.PromiseReply? ensures q in b(n).inflight {
        OldPackets(base, self, r, q, false);
        assert q in base.inflight;
      }
      forall q | q in b(n+1).inflight && q.msg.Get?
        ensures q.src.Node? && q.src in b(n+1).procs && q.dst == Bucket
      {
        if q != born {
          Split(base, self, r, q);
          if q !in base.inflight { InSent(self, r.sends, q); assert q == born; }
          assert q in base.inflight && q in b(n).inflight;
          assert q.src in b(n+1).procs.Keys;
        } else {
          assert self in b(n+1).procs.Keys;
        }
      }
    } else if p.msg.Got? && p.msg.id in s.open {
      var id := p.msg.id;
      var caller := s.open[id].caller;
      var doc := p.msg.doc;
      assert p.src == Bucket && doc == DocumentAt(docs, id);
      var answer := Temp.Get(doc, id, b(n).now).answer;
      var open' := s.open - {id};
      assert r == Result(AtNode(open'), [Send(caller, PromiseReply(answer))], Keep);
      ShapeAt(docs, b(n), self, r.state);
      assert b(n+1).procs == b(n).procs[self := r.state];
      assert b(n+1).procs.Keys == b(n).procs.Keys;
      assert b(n+1).procs[self] == AtNode(open');
      var born := Packet(self, caller, PromiseReply(answer));
      reveal Lt();
      forall node | node in b(n+1).procs && node.Node?
        ensures NodeOpen(b, a, n+1, node)
      {
        if node == self {
          forall oid | oid in open'
            ensures Entry(b, a, n+1, self, oid)
          {
            assert oid in s.open && oid != id && open'[oid] == s.open[oid];
            var c := s.open[oid].caller;
            assert Entry(b, a, n, self, oid);
            var i :| Lt(i, n) && a(i) == Deliver(Packet(c, self, PromiseGet(oid))) && Held(b, self, oid, c, i, n);
            HeldLater(b, self, oid, c, i, n);
            assert Lt(i, n + 1);
          }
        } else {
          assert b(n+1).procs[node] == b(n).procs[node];
          OpenFrame(b, a, n, node);
        }
      }
      forall q | q in b(n+1).inflight && q.msg.Get? ensures q in b(n).inflight {
        OldKind(base, self, r, q);
        assert q in base.inflight;
      }
      forall q | q in b(n+1).inflight && q.msg.Got? ensures q in b(n).inflight {
        OldPackets(base, self, r, q, true);
        assert q in base.inflight;
      }
      forall q | q in b(n+1).inflight && q.msg.PromiseReply?
        ensures q.src.Node? && Justified(docs, b, a, n+1, q.src, q.dst, q.msg.answer)
      {
        if q == born {
          var i :| Lt(i, n) && a(i) == Deliver(Packet(caller, self, PromiseGet(id))) && Held(b, self, id, caller, i, n);
          assert Lt(n, n + 1);
          assert a(n) == Deliver(Packet(Bucket, self, Got(id, doc)));
          assert id in b(n).procs[self].open && b(n).procs[self].open[id] == WaitGet(caller);
          assert Justified(docs, b, a, n+1, self, caller, answer);
        } else {
          Split(base, self, r, q);
          if q !in base.inflight { InSent(self, r.sends, q); assert q == born; }
          assert q in base.inflight;
          assert q in b(n).inflight;
          JustifyLater(docs, b, a, n, q.src, q.dst, q.msg.answer);
        }
      }
    } else {
      assert r == Result(s, [], Keep);
      QuietStep(docs, b, a, n, base, self, r);
    }
  }

  lemma Safe(docs: map<string, Temp.Doc>, clients: set<nat>, nodes: set<nat>, ask: nat -> Ask,
             b: nat -> Net<Pid, Msg, State>, a: nat -> Action<Pid, Msg>, n: nat)
    requires Routed(clients, nodes, ask)
    requires IsBehavior(World(docs, clients, nodes, ask), b, a)
    ensures Inv(docs, b, a, n)
    decreases n
  {
    if n == 0 {
      assert IsInit(World(docs, clients, nodes, ask), b(0));
      Booted(docs, clients, nodes, ask, b(0));
      forall node | node in b(0).procs && node.Node?
        ensures NodeOpen(b, a, 0, node)
      {
        var open := b(0).procs[node].open;
        assert open == map[];
        forall id | id in open ensures Entry(b, a, 0, node, id) {}
      }
    } else {
      Safe(docs, clients, nodes, ask, b, a, n - 1);
      StepOk(docs, clients, nodes, ask, b, a, n - 1);
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

  lemma PromiseGetReceived(docs: map<string, Temp.Doc>, clients: set<nat>, nodes: set<nat>, ask: nat -> Ask,
                           b: nat -> Net<Pid, Msg, State>, a: nat -> Action<Pid, Msg>,
                           r: nat, node: Pid, from: Pid, answer: Temp.Answer)
    requires Routed(clients, nodes, ask)
    requires IsBehavior(World(docs, clients, nodes, ask), b, a)
    requires node.Node?
    requires a(r) == Deliver(Packet(node, from, PromiseReply(answer)))
    ensures exists i: nat, k: nat, id, doc {:trigger a(i), a(k), Got(id, doc)} ::
      && i < k < r
      && a(i) == Deliver(Packet(from, node, PromiseGet(id)))
      && a(k) == Deliver(Packet(Bucket, node, Got(id, doc)))
      && doc == DocumentAt(docs, id)
      && Bucket in b(k).procs && b(k).procs[Bucket].AtBucket?
      && b(k).procs[Bucket].docs == docs
      && node in b(k).procs && b(k).procs[node].AtNode?
      && id in b(k).procs[node].open
      && b(k).procs[node].open[id] == WaitGet(from)
      && answer == Temp.Get(doc, id, b(k).now).answer
      && (id !in Temp.ObjectsOf(doc) ==> answer == Temp.Answer(404, Temp.None))
      && (id in Temp.ObjectsOf(doc) ==>
           answer == Temp.Answer(200, Temp.Some(Temp.Project(Temp.ObjectsOf(doc)[id], b(k).now).promise)))
  {
    Safe(docs, clients, nodes, ask, b, a, r);
    var w := World(docs, clients, nodes, ask);
    assert NextStep(w, b(r), b(r+1), a(r));
    var pk := Packet(node, from, PromiseReply(answer));
    reveal Lt();
    assert pk in b(r).inflight;
    assert Justified(docs, b, a, r, node, from, answer);
    var i, k, id, doc :|
      && Lt(i, k) && Lt(k, r)
      && node.Node?
      && a(i) == Deliver(Packet(from, node, PromiseGet(id)))
      && a(k) == Deliver(Packet(Bucket, node, Got(id, doc)))
      && doc == DocumentAt(docs, id)
      && Bucket in b(k).procs && b(k).procs[Bucket].AtBucket?
      && b(k).procs[Bucket].docs == docs
      && node in b(k).procs && b(k).procs[node].AtNode?
      && id in b(k).procs[node].open
      && b(k).procs[node].open[id] == WaitGet(from)
      && answer == Temp.Get(doc, id, b(k).now).answer;
    Cases(doc, id, b(k).now);
  }
}
