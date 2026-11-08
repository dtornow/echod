include "world.dfy"

// The lemmas that prove Claim.

module Proof {
  import opened Network
  import opened Protocol
  import Bucket
  import Node
  import opened Worlds
  import Keys
  import Temp

  // ---- what a reply is allowed to say -------------------------------------

  ghost predicate Shaped(docs: map<string, Temp.Doc>, n: Net<Pid, Msg, State>) {
    && Bucket in n.procs
    && n.procs[Bucket].AtBucket?
    && (forall p {:trigger n.procs[p]} ::
         p in n.procs && p.Client? ==>
           && n.procs[p].AtClient?
           && Node(n.procs[p].node) in n.procs)
    && (forall p {:trigger n.procs[p]} ::
         p in n.procs && p.Node? ==> n.procs[p].AtNode?)
  }

  // A stored document that owes a deadline names a timeout still in the bucket,
  // at or before that deadline.
  ghost predicate Anchored(b: State) {
    && b.AtBucket?
    && (forall key | key in b.docs ::
         match Temp.Nearest(b.docs[key])
         case None => true
         case Some(d) =>
           && key in b.anchor
           && b.anchor[key] in b.timeouts
           && b.anchor[key].key == key
           && b.anchor[key].at <= d)
  }

  ghost predicate GetsOk(n: Net<Pid, Msg, State>) {
    forall p {:trigger n.inflight[p]} ::
      n.inflight[p] > 0 && IsGet(p.msg) ==> p.src.Node? && p.src in n.procs && p.dst == Bucket
  }

  ghost predicate GotsOk(docs: map<string, Temp.Doc>, n: Net<Pid, Msg, State>) {
    forall p {:trigger n.inflight[p]} ::
      n.inflight[p] > 0 && IsGot(p.msg) ==>
        p.src == Bucket && p.dst.Node? && p.dst in n.procs
  }

  function {:opaque} Lt(i: nat, n: nat): bool { i < n }

  // The promise get for `cid` has waited on `node` at every state strictly after the request.
  // It is registered under `Hash(cid)`, the correlation id of the store read.
  ghost predicate Held(b: nat -> Net<Pid, Msg, State>, node: Pid, id: string, caller: Pid, cid: Uuid, i: nat, n: nat) {
    forall m {:trigger b(m)} :: Lt(i, m) && Lt(m, n + 1) ==>
      && node in b(m).procs
      && b(m).procs[node].AtNode?
      && Hash(cid) in b(m).procs[node].open
      && b(m).procs[node].open[Hash(cid)] == Prepare(caller, id, AskGet, cid)
  }

  ghost predicate Entry(b: nat -> Net<Pid, Msg, State>, a: nat -> Action<Pid, Msg>, n: nat, node: Pid, rpc: Uuid) {
    && node in b(n).procs && node.Node? && b(n).procs[node].AtNode?
    && rpc in b(n).procs[node].open
    && (var c := b(n).procs[node].open[rpc];
        && rpc == Hash(c.cid)
        && exists i {:trigger a(i)} ::
          && Lt(i, n)
          && a(i) == Deliver(Packet(c.caller, node, Req(c.cid, PromiseGet(c.id))))
          && Held(b, node, c.id, c.caller, c.cid, i, n))
  }

  ghost predicate NodeOpen(b: nat -> Net<Pid, Msg, State>, a: nat -> Action<Pid, Msg>, n: nat, node: Pid) {
    && node in b(n).procs && node.Node? && b(n).procs[node].AtNode?
    && (forall rpc {:trigger b(n).procs[node].open[rpc]} ::
         rpc in b(n).procs[node].open && AwaitsGet(b(n).procs[node].open[rpc]) ==> Entry(b, a, n, node, rpc))
  }

  ghost predicate OpenOk(b: nat -> Net<Pid, Msg, State>, a: nat -> Action<Pid, Msg>, n: nat) {
    forall node {:trigger b(n).procs[node]} ::
      node in b(n).procs && node.Node? ==> NodeOpen(b, a, n, node)
  }

  function GotPacket(node: Pid, rpc: Uuid, id: string, doc: Temp.Doc, version: nat): Packet<Pid, Msg> {
    Packet(Bucket, node, Res(rpc, Got(id, doc, version)))
  }

  ghost predicate Justified(docs: map<string, Temp.Doc>, b: nat -> Net<Pid, Msg, State>,
                             a: nat -> Action<Pid, Msg>, limit: nat, node: Pid, caller: Pid, cid: Uuid, answer: Temp.Answer)
  {
    exists i, k, id, doc, version {:trigger a(i), a(k), GotPacket(node, Hash(cid), id, doc, version)} ::
      && Lt(i, k) && Lt(k, limit)
      && node.Node?
      && a(i) == Deliver(Packet(caller, node, Req(cid, PromiseGet(id))))
      && a(k) == Deliver(GotPacket(node, Hash(cid), id, doc, version))
      && answer == Temp.Get(doc, id, b(k).now).answer
      && Bucket in b(k).procs && b(k).procs[Bucket].AtBucket?
      && node in b(k).procs && b(k).procs[node].AtNode?
      && Hash(cid) in b(k).procs[node].open
      && b(k).procs[node].open[Hash(cid)] == Prepare(caller, id, AskGet, cid)
  }

  ghost predicate RepliesOk(docs: map<string, Temp.Doc>, b: nat -> Net<Pid, Msg, State>,
                            a: nat -> Action<Pid, Msg>, n: nat)
  {
    forall p {:trigger b(n).inflight[p]} ::
      b(n).inflight[p] > 0 && IsPromiseReply(p.msg) ==>
        p.src.Node? && Justified(docs, b, a, n, p.src, p.dst, p.msg.id, p.msg.ans.answer)
  }

  ghost predicate Inv(docs: map<string, Temp.Doc>, b: nat -> Net<Pid, Msg, State>,
                      a: nat -> Action<Pid, Msg>, n: nat)
  {
    && Shaped(docs, b(n))
    && GetsOk(b(n))
    && GotsOk(docs, b(n))
    && OpenOk(b, a, n)
    && RepliesOk(docs, b, a, n)
    && Anchored(b(n).procs[Bucket])
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
    requires self.Bucket? ==> s.AtBucket?
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

  lemma HeldLater(b: nat -> Net<Pid, Msg, State>, node: Pid, id: string, caller: Pid, cid: Uuid, i: nat, n: nat)
    requires Held(b, node, id, caller, cid, i, n)
    requires node in b(n+1).procs && b(n+1).procs[node].AtNode?
    requires Hash(cid) in b(n+1).procs[node].open && b(n+1).procs[node].open[Hash(cid)] == Prepare(caller, id, AskGet, cid)
    ensures Held(b, node, id, caller, cid, i, n+1)
  {
    reveal Lt();
    forall m {:trigger b(m)} | i < m < n + 2
      ensures node in b(m).procs && b(m).procs[node].AtNode?
        && Hash(cid) in b(m).procs[node].open && b(m).procs[node].open[Hash(cid)] == Prepare(caller, id, AskGet, cid)
    {
      if m < n + 1 {
        assert b(m).procs[node].open[Hash(cid)] == Prepare(caller, id, AskGet, cid);
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
    forall rpc | rpc in open && AwaitsGet(open[rpc])
      ensures Entry(b, a, n+1, node, rpc)
    {
      var c := open[rpc];
      assert Entry(b, a, n, node, rpc);
      var i :| Lt(i, n) && a(i) == Deliver(Packet(c.caller, node, Req(c.cid, PromiseGet(c.id)))) && Held(b, node, c.id, c.caller, c.cid, i, n);
      HeldLater(b, node, c.id, c.caller, c.cid, i, n);
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
                     n: nat, node: Pid, caller: Pid, cid: Uuid, answer: Temp.Answer)
    requires Justified(docs, b, a, n, node, caller, cid, answer)
    ensures Justified(docs, b, a, n+1, node, caller, cid, answer)
  {
    reveal Lt();
    var i, k, id, doc, version :|
      && Lt(i, k) && Lt(k, n)
      && node.Node?
      && a(i) == Deliver(Packet(caller, node, Req(cid, PromiseGet(id))))
      && a(k) == Deliver(GotPacket(node, Hash(cid), id, doc, version))
      && answer == Temp.Get(doc, id, b(k).now).answer
      && Bucket in b(k).procs && b(k).procs[Bucket].AtBucket?
      && node in b(k).procs && b(k).procs[node].AtNode?
      && Hash(cid) in b(k).procs[node].open
      && b(k).procs[node].open[Hash(cid)] == Prepare(caller, id, AskGet, cid);
    assert Lt(k, n + 1);
  }

  lemma Carry(docs: map<string, Temp.Doc>, b: nat -> Net<Pid, Msg, State>, a: nat -> Action<Pid, Msg>, n: nat)
    requires Inv(docs, b, a, n)
    requires Shaped(docs, b(n+1))
    requires b(n+1).procs.Keys == b(n).procs.Keys
    requires forall node :: node in b(n).procs && node.Node? ==> b(n+1).procs[node] == b(n).procs[node]
    requires Anchored(b(n+1).procs[Bucket])
    requires forall q :: q in b(n+1).inflight && IsGet(q.msg) ==> q in b(n).inflight
    requires forall q :: q in b(n+1).inflight && IsGot(q.msg) ==> q in b(n).inflight
    requires forall q :: q in b(n+1).inflight && IsPromiseReply(q.msg) ==> q in b(n).inflight
    ensures Inv(docs, b, a, n+1)
  {
    forall p | p in b(n+1).inflight && IsGet(p.msg)
      ensures p.src.Node? && p.src in b(n+1).procs && p.dst == Bucket
    {
      assert p in b(n).inflight;
      assert p.src in b(n).procs;
      assert p.src in b(n+1).procs.Keys;
    }
    forall p | p in b(n+1).inflight && IsGot(p.msg)
      ensures p.src == Bucket && p.dst.Node? && p.dst in b(n+1).procs
    {
      assert p in b(n).inflight;
      assert p.dst in b(n).procs;
      assert p.dst in b(n+1).procs.Keys;
    }
    forall p | p in b(n+1).inflight && IsPromiseReply(p.msg)
      ensures p.src.Node? && Justified(docs, b, a, n+1, p.src, p.dst, p.msg.id, p.msg.ans.answer)
    {
      assert p in b(n).inflight;
      assert Justified(docs, b, a, n, p.src, p.dst, p.msg.id, p.msg.ans.answer);
      JustifyLater(docs, b, a, n, p.src, p.dst, p.msg.id, p.msg.ans.answer);
    }
    OpenSame(b, a, n);
  }

  lemma NoSuch(self: Pid, sends: seq<Send<Pid, Msg>>, q: Packet<Pid, Msg>)
    requires q in ToPackets(self, sends)
    requires IsGot(q.msg) || IsPromiseReply(q.msg)
    requires IsGot(q.msg) ==> forall i {:trigger sends[i]} :: 0 <= i < |sends| ==> !IsGot(sends[i].msg)
    requires IsPromiseReply(q.msg) ==> forall i {:trigger sends[i]} :: 0 <= i < |sends| ==> !IsPromiseReply(sends[i].msg)
    ensures false
  {
    InSent(self, sends, q);
    var i :| 0 <= i < |sends| && q == Packet(self, sends[i].to, sends[i].msg);
    assert q.msg == sends[i].msg;
    if IsGot(q.msg) {
      assert !IsGot(sends[i].msg);
    } else {
      assert IsPromiseReply(q.msg);
      assert !IsPromiseReply(sends[i].msg);
    }
  }

  lemma OldPackets(base: Net<Pid, Msg, State>, self: Pid, r: Result<Pid, Msg, State>,
                   q: Packet<Pid, Msg>, got: bool)
    requires self in base.procs
    requires q in Advance(base, self, r).inflight
    requires if got then IsGot(q.msg) else IsPromiseReply(q.msg)
    requires forall i {:trigger r.sends[i]} :: 0 <= i < |r.sends| ==> if got then !IsGot(r.sends[i].msg) else !IsPromiseReply(r.sends[i].msg)
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

  lemma CoverStep(docs: map<string, Temp.Doc>, keys: seq<string>)
    requires forall i :: 0 <= i < |keys| ==> keys[i] in docs
    requires forall i, j :: 0 <= i < j < |keys| ==> Keys.Lt(keys[i], keys[j])
    ensures var timeouts := Bucket.CoverOf(docs, keys);
            var anchor := Bucket.AnchorOf(docs, keys);
      forall i | 0 <= i < |keys| ::
        match Temp.Nearest(docs[keys[i]])
        case None => true
        case Some(d) =>
          && keys[i] in anchor
          && anchor[keys[i]] == Due(keys[i], d, 0, 0)
          && anchor[keys[i]] in timeouts
    decreases |keys|
  {
    if |keys| > 0 {
      CoverStep(docs, keys[1..]);
      var head := keys[0];
      var timeouts := Bucket.CoverOf(docs, keys);
      var anchor := Bucket.AnchorOf(docs, keys);
      var restT := Bucket.CoverOf(docs, keys[1..]);
      var restA := Bucket.AnchorOf(docs, keys[1..]);
      forall i | 0 <= i < |keys|
        ensures match Temp.Nearest(docs[keys[i]])
          case None => true
          case Some(d) =>
            && keys[i] in anchor
            && anchor[keys[i]] == Due(keys[i], d, 0, 0)
            && anchor[keys[i]] in timeouts
      {
        if i == 0 {
          match Temp.Nearest(docs[head])
          case None =>
          case Some(d) =>
            assert anchor[head] == Due(head, d, 0, 0);
            assert Due(head, d, 0, 0) in timeouts;
        } else {
          assert keys[i] == keys[1..][i - 1];
          assert Keys.Lt(head, keys[i]);
          match Temp.Nearest(docs[keys[i]])
          case None =>
          case Some(d) =>
            assert restA[keys[i]] == Due(keys[i], d, 0, 0);
            assert restA[keys[i]] in restT;
            match Temp.Nearest(docs[head])
            case None =>
              assert anchor == restA && timeouts == restT;
            case Some(_) =>
              assert anchor == restA[head := Due(head, Temp.Nearest(docs[head]).value, 0, 0)];
              assert keys[i] != head;
              assert anchor[keys[i]] == restA[keys[i]];
              assert timeouts == restT + {Due(head, Temp.Nearest(docs[head]).value, 0, 0)};
              assert restA[keys[i]] in timeouts;
        }
      }
    }
  }

  lemma CoverLemma(docs: map<string, Temp.Doc>)
    ensures Anchored(AtBucket(docs, map[], Bucket.BootTimeouts(docs), Bucket.BootAnchor(docs)))
  {
    var keys := Keys.Sorted(docs.Keys);
    Keys.SortedProps(docs.Keys);
    assert forall i :: 0 <= i < |keys| ==> keys[i] in docs.Keys && keys[i] in docs;
    CoverStep(docs, keys);
    var bucket := AtBucket(docs, map[], Bucket.BootTimeouts(docs), Bucket.BootAnchor(docs));
    forall key | key in docs
      ensures match Temp.Nearest(docs[key])
        case None => true
        case Some(d) =>
          && key in bucket.anchor
          && bucket.anchor[key] in bucket.timeouts
          && bucket.anchor[key].key == key
          && bucket.anchor[key].at <= d
    {
      assert key in docs.Keys;
      assert key in keys;
      var i :| 0 <= i < |keys| && keys[i] == key;
      match Temp.Nearest(docs[key])
      case None =>
      case Some(d) =>
        assert bucket.anchor[key] == Due(key, d, 0, 0);
    }
  }

  lemma Booted(docs: map<string, Temp.Doc>, clients: set<nat>, nodes: set<nat>, ask: nat -> Ask, n: Net<Pid, Msg, State>)
    requires Routed(clients, nodes, ask)
    requires IsInit(World(docs, clients, nodes, ask), n)
    ensures Shaped(docs, n)
    ensures n.inflight == multiset{}
    ensures Anchored(n.procs[Bucket])
    ensures forall p {:trigger n.procs[p]} :: p in n.procs && p.Node? ==> n.procs[p] == AtNode(map[], map[], 0, p.i + 1)
  {
    var w := World(docs, clients, nodes, ask);
    assert n.procs == (map p | p in w.pids :: w.init(p));
    assert w.pids == Pids(clients, nodes);
    assert n.procs.Keys == w.pids;
    BucketIn(clients, nodes);
    assert n.procs[Bucket] == w.init(Bucket) == Boot(docs, ask, Bucket);
    CoverLemma(docs);
    forall p | p in n.procs && p.Client?
      ensures n.procs[p].AtClient? && Node(n.procs[p].node) in n.procs
    {
      ClientIndex(clients, nodes, p);
      var c := p.c;
      assert n.procs[p] == w.init(p) == Boot(docs, ask, p) == AtClient(ask(c).id, ask(c).node, ask(c).kind, true);
      NodeIn(clients, nodes, ask(c).node);
      assert Node(ask(c).node) in n.procs.Keys;
    }
    forall p | p in n.procs && p.Node?
      ensures n.procs[p] == AtNode(map[], map[], 0, p.i + 1)
    {
      assert n.procs[p] == w.init(p) == Boot(docs, ask, p) == AtNode(map[], map[], 0, p.i + 1);
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
    requires forall i {:trigger r.sends[i]} :: 0 <= i < |r.sends| ==> !IsGet(r.sends[i].msg) && !IsGot(r.sends[i].msg) && !IsPromiseReply(r.sends[i].msg)
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
    forall q | q in b(n+1).inflight && IsGet(q.msg)
      ensures q in b(n).inflight
    {
      OldKind(base, self, r, q);
    }
    forall q | q in b(n+1).inflight && IsGot(q.msg)
      ensures q in b(n).inflight
    {
      OldPackets(base, self, r, q, true);
    }
    forall q | q in b(n+1).inflight && IsPromiseReply(q.msg)
      ensures q in b(n).inflight
    {
      OldPackets(base, self, r, q, false);
    }
    if self == Bucket {
      assert r.state == b(n).procs[Bucket];
    }
    assert b(n+1).procs[Bucket] == b(n).procs[Bucket];
    assert Anchored(b(n+1).procs[Bucket]);
    Carry(docs, b, a, n);
  }

  lemma OldKind(base: Net<Pid, Msg, State>, self: Pid, r: Result<Pid, Msg, State>, q: Packet<Pid, Msg>)
    requires self in base.procs
    requires q in Advance(base, self, r).inflight && IsGet(q.msg)
    requires forall i {:trigger r.sends[i]} :: 0 <= i < |r.sends| ==> !IsGet(r.sends[i].msg)
    ensures q in base.inflight
  {
    Split(base, self, r, q);
    if q !in base.inflight {
      InSent(self, r.sends, q);
      var i :| 0 <= i < |r.sends| && q == Packet(self, r.sends[i].to, r.sends[i].msg);
      assert !IsGet(r.sends[i].msg);
    }
  }

  lemma OnTimeout(self: Pid, s: State, now: nat)
    requires self.Client? ==> s.AtClient?
    requires self.Node? ==> s.AtNode?
    requires self.Bucket? ==> s.AtBucket?
    ensures var r := Processes(self).step(self, s, Timeout, now);
      if self.Client? && s.waiting then
        var body :=
          match s.kind
          case Read => PromiseGet(s.id)
          case Create(timeout) => PromiseCreate(Temp.CreateReq(s.id, timeout, Temp.Empty(), []));
        r == Result(AtClient(s.id, s.node, s.kind, false), [ReqTo(Node(s.node), Uuid(0), body)], Keep)
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
    assert w.process == Processes;
    assert NextStep(w, b(n), b(n+1), a(n));
    match a(n)
    case Tick =>
      assert b(n+1) == b(n).(now := b(n).now + 1);
      SameShape(docs, b(n), b(n+1));
      assert b(n+1).procs.Keys == b(n).procs.Keys;
      forall node | node in b(n).procs && node.Node? ensures b(n+1).procs[node] == b(n).procs[node] {}
      assert b(n+1).procs[Bucket] == b(n).procs[Bucket];
      assert Anchored(b(n+1).procs[Bucket]);
      forall q | q in b(n+1).inflight ensures q in b(n).inflight {}
      Carry(docs, b, a, n);
    case Drop(p) =>
      assert b(n+1) == b(n).(inflight := b(n).inflight - multiset{p});
      SameShape(docs, b(n), b(n+1));
      assert b(n+1).procs.Keys == b(n).procs.Keys;
      forall node | node in b(n).procs && node.Node? ensures b(n+1).procs[node] == b(n).procs[node] {}
      assert b(n+1).procs[Bucket] == b(n).procs[Bucket];
      assert Anchored(b(n+1).procs[Bucket]);
      forall q | q in b(n+1).inflight ensures q in b(n).inflight {}
      Carry(docs, b, a, n);
    case Duplicate(p) =>
      assert b(n+1) == b(n).(inflight := b(n).inflight + multiset{p});
      SameShape(docs, b(n), b(n+1));
      assert b(n+1).procs.Keys == b(n).procs.Keys;
      forall node | node in b(n).procs && node.Node? ensures b(n+1).procs[node] == b(n).procs[node] {}
      assert b(n+1).procs[Bucket] == b(n).procs[Bucket];
      assert Anchored(b(n+1).procs[Bucket]);
      forall q | q in b(n+1).inflight ensures q in b(n).inflight {
        if q != p { assert b(n).inflight[q] == b(n+1).inflight[q]; }
      }
      Carry(docs, b, a, n);
    case Fire(pid) =>
      var base := b(n).(timers := b(n).timers - {pid});
      var r := w.process(pid).step(pid, b(n).procs[pid], Timeout, b(n).now);
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
    assert w.process == Processes;
    assert NextStep(w, b(n), b(n+1), Deliver(p));
    var base := b(n).(inflight := b(n).inflight - multiset{p});
    var r := w.process(p.dst).step(p.dst, b(n).procs[p.dst], Request(p.src, p.msg), b(n).now);
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

  lemma BucketKept(docs: map<string, Temp.Doc>, b: nat -> Net<Pid, Msg, State>, a: nat -> Action<Pid, Msg>,
                   n: nat, base: Net<Pid, Msg, State>, r: Result<Pid, Msg, State>)
    requires Inv(docs, b, a, n)
    requires base.procs == b(n).procs
    requires forall q :: q in base.inflight ==> q in b(n).inflight
    requires b(n+1) == Advance(base, Bucket, r)
    requires r.state.AtBucket? && Anchored(r.state)
    requires forall i {:trigger r.sends[i]} :: 0 <= i < |r.sends| ==> !IsGet(r.sends[i].msg) && !IsGot(r.sends[i].msg) && !IsPromiseReply(r.sends[i].msg)
    ensures Inv(docs, b, a, n+1)
  {
    ShapeAt(docs, b(n), Bucket, r.state);
    assert b(n+1).procs == b(n).procs[Bucket := r.state];
    assert b(n+1).procs.Keys == b(n).procs.Keys;
    forall node | node in b(n).procs && node.Node?
      ensures b(n+1).procs[node] == b(n).procs[node]
    { assert node != Bucket; }
    forall q | q in b(n+1).inflight && IsGet(q.msg)
      ensures q in b(n).inflight
    { OldKind(base, Bucket, r, q); }
    forall q | q in b(n+1).inflight && IsGot(q.msg)
      ensures q in b(n).inflight
    { OldPackets(base, Bucket, r, q, true); }
    forall q | q in b(n+1).inflight && IsPromiseReply(q.msg)
      ensures q in b(n).inflight
    { OldPackets(base, Bucket, r, q, false); }
    assert b(n+1).procs[Bucket] == r.state;
    assert Anchored(b(n+1).procs[Bucket]);
    Carry(docs, b, a, n);
  }

  lemma PutKeeps(s: State, clock: Clock)
    requires s.AtBucket? && Anchored(s)
    ensures Anchored(AtBucket(s.docs, s.ver, s.timeouts + {clock}, s.anchor))
  {
    var s' := AtBucket(s.docs, s.ver, s.timeouts + {clock}, s.anchor);
    forall key | key in s'.docs
      ensures match Temp.Nearest(s'.docs[key])
        case None => true
        case Some(d) => key in s'.anchor && s'.anchor[key] in s'.timeouts && s'.anchor[key].key == key && s'.anchor[key].at <= d
    {
      match Temp.Nearest(s.docs[key])
      case None =>
      case Some(d) =>
        assert s.anchor[key] in s.timeouts;
        assert s.anchor[key] in s'.timeouts;
    }
  }

  lemma DropKeeps(s: State, clock: Clock)
    requires s.AtBucket? && Anchored(s) && !Bucket.LiveAnchor(s, clock)
    ensures Anchored(AtBucket(s.docs, s.ver, s.timeouts - {clock}, s.anchor))
  {
    var s' := AtBucket(s.docs, s.ver, s.timeouts - {clock}, s.anchor);
    forall key | key in s'.docs
      ensures match Temp.Nearest(s'.docs[key])
        case None => true
        case Some(d) => key in s'.anchor && s'.anchor[key] in s'.timeouts && s'.anchor[key].key == key && s'.anchor[key].at <= d
    {
      match Temp.Nearest(s.docs[key])
      case None =>
      case Some(d) =>
        assert s.anchor[key] in s.timeouts;
        if s.anchor[key] == clock {
          assert clock.key == key;
          assert Bucket.LiveAnchor(s, clock);
        }
        assert s.anchor[key] != clock;
        assert s.anchor[key] in s'.timeouts;
    }
  }

  lemma WriteKeeps(s: State, key: string, doc: Temp.Doc, version: nat, cover: Temp.Opt<Clock>)
    requires s.AtBucket? && Anchored(s)
    requires VersionOf(s.ver, key) == version && Bucket.Accept(s, key, doc, cover)
    ensures var anchor' :=
              match (Temp.Nearest(doc), cover)
              case (None, _) => s.anchor - {key}
              case (Some(_), Some(clock)) => s.anchor[key := clock]
              case (Some(_), None) => s.anchor;
      Anchored(AtBucket(s.docs[key := doc], s.ver[key := version + 1], s.timeouts, anchor'))
  {
    var anchor' :=
      match (Temp.Nearest(doc), cover)
      case (None, _) => s.anchor - {key}
      case (Some(_), Some(clock)) => s.anchor[key := clock]
      case (Some(_), None) => s.anchor;
    var s' := AtBucket(s.docs[key := doc], s.ver[key := version + 1], s.timeouts, anchor');
    forall k | k in s'.docs
      ensures match Temp.Nearest(s'.docs[k])
        case None => true
        case Some(d) => k in s'.anchor && s'.anchor[k] in s'.timeouts && s'.anchor[k].key == k && s'.anchor[k].at <= d
    {
      if k == key {
        match Temp.Nearest(doc)
        case None =>
        case Some(d) =>
          assert cover.Some?;
          assert cover.value in s.timeouts;
          assert cover.value.key == key && cover.value.at <= d;
          assert anchor' == s.anchor[key := cover.value];
          assert s'.anchor[key] == cover.value;
          assert s'.anchor[key] in s'.timeouts;
      } else {
        match Temp.Nearest(s.docs[k])
        case None =>
        case Some(d) =>
          assert k in s.anchor && s.anchor[k] in s.timeouts && s.anchor[k].key == k && s.anchor[k].at <= d;
          assert k != key;
          match (Temp.Nearest(doc), cover)
          case (None, _) =>
            assert anchor' == s.anchor - {key};
            assert s'.anchor[k] == s.anchor[k];
          case (Some(_), Some(clock)) =>
            assert anchor' == s.anchor[key := clock];
            assert s'.anchor[k] == s.anchor[k];
          case (Some(_), None) =>
            assert anchor' == s.anchor;
      }
    }
  }

  lemma BucketDeliver(docs: map<string, Temp.Doc>, b: nat -> Net<Pid, Msg, State>, a: nat -> Action<Pid, Msg>,
                      n: nat, base: Net<Pid, Msg, State>, p: Packet<Pid, Msg>, r: Result<Pid, Msg, State>)
    requires Inv(docs, b, a, n)
    requires p.dst == Bucket && p in b(n).inflight
    requires base == b(n).(inflight := b(n).inflight - multiset{p})
    requires r == Processes(Bucket).step(Bucket, b(n).procs[Bucket], Request(p.src, p.msg), b(n).now)
    requires b(n+1) == Advance(base, Bucket, r)
    requires forall q :: q in base.inflight ==> q in b(n).inflight
    ensures Inv(docs, b, a, n+1)
  {
    var s0 := b(n).procs[Bucket];
    match p.msg
    case Req(rpc, Get(id)) =>
      assert p.src.Node? && p.src in b(n).procs && p.dst == Bucket;
      var who := p.src;
      var key := DocKey(id);
      var doc := DocumentAt(s0.docs, id);
      var version := VersionOf(s0.ver, key);
      assert r == Result(s0, [ResTo(who, rpc, Got(id, doc, version))], Keep);
      var born := Packet(Bucket, who, Res(rpc, Got(id, doc, version)));
      ShapeAt(docs, b(n), Bucket, r.state);
      assert b(n+1).procs == b(n).procs[Bucket := r.state];
      assert b(n+1).procs.Keys == b(n).procs.Keys;
      forall node | node in b(n).procs && node.Node?
        ensures b(n+1).procs[node] == b(n).procs[node]
      { assert node != Bucket; }
      forall q | q in b(n+1).inflight && IsGet(q.msg)
        ensures q.src.Node? && q.src in b(n+1).procs && q.dst == Bucket
      {
        OldKind(base, Bucket, r, q);
        assert q in base.inflight && q in b(n).inflight;
        assert q.src in b(n+1).procs.Keys;
      }
      forall q | q in b(n+1).inflight && IsPromiseReply(q.msg)
        ensures q.src.Node? && Justified(docs, b, a, n+1, q.src, q.dst, q.msg.id, q.msg.ans.answer)
      {
        OldPackets(base, Bucket, r, q, false);
        assert q in base.inflight && q in b(n).inflight;
        JustifyLater(docs, b, a, n, q.src, q.dst, q.msg.id, q.msg.ans.answer);
      }
      forall q | q in b(n+1).inflight && IsGot(q.msg)
        ensures q.src == Bucket && q.dst.Node? && q.dst in b(n+1).procs
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
      assert b(n+1).procs[Bucket] == s0;
      assert Anchored(b(n+1).procs[Bucket]);
      OpenSame(b, a, n);
    case Req(rpc, PutTimeout(id, clock)) =>
      assert r == Result(AtBucket(s0.docs, s0.ver, s0.timeouts + {clock}, s0.anchor), [ResTo(p.src, rpc, TimeoutPut(id, clock))], Keep);
      PutKeeps(s0, clock);
      BucketKept(docs, b, a, n, base, r);
    case Req(rpc, WriteDoc(id, key, doc, version, cover)) =>
      if VersionOf(s0.ver, key) == version && Bucket.Accept(s0, key, doc, cover) {
        WriteKeeps(s0, key, doc, version, cover);
        var anchor' :=
          match (Temp.Nearest(doc), cover)
          case (None, _) => s0.anchor - {key}
          case (Some(_), Some(clock)) => s0.anchor[key := clock]
          case (Some(_), None) => s0.anchor;
        assert r == Result(AtBucket(s0.docs[key := doc], s0.ver[key := version + 1], s0.timeouts, anchor'),
                           [ResTo(p.src, rpc, DocWrote(id, key))], Keep);
        BucketKept(docs, b, a, n, base, r);
      } else {
        assert r == Result(s0, [ResTo(p.src, rpc, DocRejected(id))], Keep);
        BucketKept(docs, b, a, n, base, r);
      }
    case Req(rpc, DropTimeout(id, clock)) =>
      if Bucket.LiveAnchor(s0, clock) {
        assert r == Result(s0, [ResTo(p.src, rpc, TimeoutDropped(id, clock))], Keep);
        BucketKept(docs, b, a, n, base, r);
      } else {
        DropKeeps(s0, clock);
        assert r == Result(AtBucket(s0.docs, s0.ver, s0.timeouts - {clock}, s0.anchor), [ResTo(p.src, rpc, TimeoutDropped(id, clock))], Keep);
        BucketKept(docs, b, a, n, base, r);
      }
    case _ =>
      assert r == Result(s0, [], Keep);
      QuietStep(docs, b, a, n, base, Bucket, r);
  }

  lemma NodeDeliver(docs: map<string, Temp.Doc>, b: nat -> Net<Pid, Msg, State>, a: nat -> Action<Pid, Msg>,
                    n: nat, base: Net<Pid, Msg, State>, p: Packet<Pid, Msg>, r: Result<Pid, Msg, State>)
    requires Inv(docs, b, a, n)
    requires a(n) == Deliver(p)
    requires p.dst.Node? && p.dst in b(n).procs && p in b(n).inflight
    requires base == b(n).(inflight := b(n).inflight - multiset{p})
    requires r == Processes(p.dst).step(p.dst, b(n).procs[p.dst], Request(p.src, p.msg), b(n).now)
    requires b(n+1) == Advance(base, p.dst, r)
    requires forall q :: q in base.inflight ==> q in b(n).inflight
    ensures Inv(docs, b, a, n+1)
  {
    var self := p.dst;
    var s := b(n).procs[self];
    if IsPromiseGet(p.msg) && Hash(p.msg.id) !in s.open {
      var id := p.msg.ask.id;
      var cid := p.msg.id;
      var caller := p.src;
      var rpc := Hash(cid);
      var open' := s.open[rpc := Prepare(caller, id, AskGet, cid)];
      assert r == Result(AtNode(open', s.armed, s.next, s.owner), [ReqTo(Bucket, rpc, Get(id))], Keep);
      var born := Packet(self, Bucket, Req(rpc, Get(id)));
      ShapeAt(docs, b(n), self, r.state);
      assert b(n+1).procs == b(n).procs[self := r.state];
      assert b(n+1).procs.Keys == b(n).procs.Keys;
      assert b(n+1).procs[self] == AtNode(open', s.armed, s.next, s.owner);
      assert b(n+1).procs[Bucket] == b(n).procs[Bucket];
      assert Anchored(b(n+1).procs[Bucket]);
      reveal Lt();
      forall m {:trigger b(m)} | n < m < n + 2
        ensures self in b(m).procs && b(m).procs[self].AtNode?
          && rpc in b(m).procs[self].open && b(m).procs[self].open[rpc] == Prepare(caller, id, AskGet, cid)
      { assert m == n + 1; }
      assert Held(b, self, id, caller, cid, n, n + 1);
      assert a(n) == Deliver(Packet(caller, self, Req(cid, PromiseGet(id))));
      forall node | node in b(n+1).procs && node.Node?
        ensures NodeOpen(b, a, n+1, node)
      {
        if node == self {
          forall oid | oid in open' && AwaitsGet(open'[oid])
            ensures Entry(b, a, n+1, self, oid)
          {
            if oid == rpc {
              assert Lt(n, n + 1);
            } else {
              assert oid in s.open && open'[oid] == s.open[oid];
              var c := s.open[oid];
              assert Entry(b, a, n, self, oid);
              var i :| Lt(i, n) && a(i) == Deliver(Packet(c.caller, self, Req(c.cid, PromiseGet(c.id)))) && Held(b, self, c.id, c.caller, c.cid, i, n);
              HeldLater(b, self, c.id, c.caller, c.cid, i, n);
              assert Lt(i, n + 1);
            }
          }
        } else {
          assert b(n+1).procs[node] == b(n).procs[node];
          OpenFrame(b, a, n, node);
        }
      }
      forall q | q in b(n+1).inflight && IsGot(q.msg) ensures q in b(n).inflight {
        OldPackets(base, self, r, q, true);
        assert q in base.inflight;
      }
      forall q | q in b(n+1).inflight && IsPromiseReply(q.msg)
        ensures q.src.Node? && Justified(docs, b, a, n+1, q.src, q.dst, q.msg.id, q.msg.ans.answer)
      {
        OldPackets(base, self, r, q, false);
        assert q in base.inflight && q in b(n).inflight;
        JustifyLater(docs, b, a, n, q.src, q.dst, q.msg.id, q.msg.ans.answer);
      }
      forall q | q in b(n+1).inflight && IsGet(q.msg)
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
    } else if IsGot(p.msg) && p.msg.id in s.open && AwaitsGet(s.open[p.msg.id]) && s.open[p.msg.id].id == p.msg.ans.id {
      var rpc := p.msg.id;
      var id := p.msg.ans.id;
      var caller := s.open[rpc].caller;
      var cid := s.open[rpc].cid;
      var doc := p.msg.ans.doc;
      var version := p.msg.ans.version;
      assert p.src == Bucket;
      var answer := Temp.Get(doc, id, b(n).now).answer;
      var open' := s.open - {rpc};
      assert r == Result(AtNode(open', s.armed, s.next, s.owner), [ResTo(caller, cid, PromiseReply(answer))], Keep);
      ShapeAt(docs, b(n), self, r.state);
      assert b(n+1).procs == b(n).procs[self := r.state];
      assert b(n+1).procs.Keys == b(n).procs.Keys;
      assert b(n+1).procs[self] == AtNode(open', s.armed, s.next, s.owner);
      assert b(n+1).procs[Bucket] == b(n).procs[Bucket];
      assert Anchored(b(n+1).procs[Bucket]);
      var born := Packet(self, caller, Res(cid, PromiseReply(answer)));
      reveal Lt();
      forall node | node in b(n+1).procs && node.Node?
        ensures NodeOpen(b, a, n+1, node)
      {
        if node == self {
          forall oid | oid in open' && AwaitsGet(open'[oid])
            ensures Entry(b, a, n+1, self, oid)
          {
            assert oid in s.open && oid != rpc && open'[oid] == s.open[oid];
            var c := s.open[oid];
            assert Entry(b, a, n, self, oid);
            var i :| Lt(i, n) && a(i) == Deliver(Packet(c.caller, self, Req(c.cid, PromiseGet(c.id)))) && Held(b, self, c.id, c.caller, c.cid, i, n);
            HeldLater(b, self, c.id, c.caller, c.cid, i, n);
            assert Lt(i, n + 1);
          }
        } else {
          assert b(n+1).procs[node] == b(n).procs[node];
          OpenFrame(b, a, n, node);
        }
      }
      forall q | q in b(n+1).inflight && IsGet(q.msg) ensures q in b(n).inflight {
        OldKind(base, self, r, q);
        assert q in base.inflight;
      }
      forall q | q in b(n+1).inflight && IsGot(q.msg) ensures q in b(n).inflight {
        OldPackets(base, self, r, q, true);
        assert q in base.inflight;
      }
      forall q | q in b(n+1).inflight && IsPromiseReply(q.msg)
        ensures q.src.Node? && Justified(docs, b, a, n+1, q.src, q.dst, q.msg.id, q.msg.ans.answer)
      {
        if q == born {
          var i :| Lt(i, n) && a(i) == Deliver(Packet(caller, self, Req(cid, PromiseGet(id)))) && Held(b, self, id, caller, cid, i, n);
          assert Lt(n, n + 1);
          assert a(n) == Deliver(GotPacket(self, Hash(cid), id, doc, version));
          assert Hash(cid) in b(n).procs[self].open && b(n).procs[self].open[Hash(cid)] == Prepare(caller, id, AskGet, cid);
          assert Justified(docs, b, a, n+1, self, caller, cid, answer);
        } else {
          Split(base, self, r, q);
          if q !in base.inflight { InSent(self, r.sends, q); assert q == born; }
          assert q in base.inflight;
          assert q in b(n).inflight;
          JustifyLater(docs, b, a, n, q.src, q.dst, q.msg.id, q.msg.ans.answer);
        }
      }
    } else {
      KeepsGets(self, s, Request(p.src, p.msg), b(n).now);
      NodeKept(docs, b, a, n, base, p, r);
    }
  }

  lemma KeepsGets(self: Pid, s: State, i: Input<Pid, Msg>, now: nat)
    requires self.Node? && s.AtNode?
    requires !(i.Request? && IsPromiseGet(i.msg) && Hash(i.msg.id) !in s.open)
    requires !(i.Request? && IsGot(i.msg) && i.msg.id in s.open && AwaitsGet(s.open[i.msg.id]) && s.open[i.msg.id].id == i.msg.ans.id)
    ensures var r := Node.step(self, s, i, now);
      && r.state.AtNode?
      && (forall rpc :: rpc in r.state.open && AwaitsGet(r.state.open[rpc]) ==>
           rpc in s.open && s.open[rpc] == r.state.open[rpc])
      && (forall j :: 0 <= j < |r.sends| ==> !IsPromiseReply(r.sends[j].msg) && !IsGot(r.sends[j].msg))
      && (forall j :: 0 <= j < |r.sends| && IsGet(r.sends[j].msg) ==> r.sends[j].to == Bucket)
  {
    var r := Node.step(self, s, i, now);
    match i
    case Request(from, Req(cid, PromiseCreate(req))) =>
      var rpc := Hash(cid);
      if rpc !in s.open {
        var open' := s.open[rpc := Prepare(from, req.id, AskCreate(req), cid)];
        assert r == Result(AtNode(open', s.armed, s.next, s.owner), [ReqTo(Bucket, rpc, Get(req.id))], Keep);
        forall k | k in open' && AwaitsGet(open'[k])
          ensures k in s.open && s.open[k] == open'[k]
        {
          assert k != rpc;
        }
      }
    case Request(_, Res(rpc, Got(id, doc, version))) =>
      if rpc in s.open && AwaitsGet(s.open[rpc]) && s.open[rpc].id == id {
      } else if rpc in s.open && s.open[rpc].Prepare? && s.open[rpc].job.AskCreate? && s.open[rpc].id == id {
        assert r.state.AtNode?;
      }
    case _ =>
  }

  lemma NodeKept(docs: map<string, Temp.Doc>, b: nat -> Net<Pid, Msg, State>, a: nat -> Action<Pid, Msg>,
                 n: nat, base: Net<Pid, Msg, State>, p: Packet<Pid, Msg>, r: Result<Pid, Msg, State>)
    requires Inv(docs, b, a, n)
    requires a(n) == Deliver(p)
    requires p.dst.Node? && p.dst in b(n).procs && p in b(n).inflight
    requires base == b(n).(inflight := b(n).inflight - multiset{p})
    requires r == Processes(p.dst).step(p.dst, b(n).procs[p.dst], Request(p.src, p.msg), b(n).now)
    requires b(n+1) == Advance(base, p.dst, r)
    requires forall q :: q in base.inflight ==> q in b(n).inflight
    requires !(IsPromiseGet(p.msg) && Hash(p.msg.id) !in b(n).procs[p.dst].open)
    requires !(IsGot(p.msg) && p.msg.id in b(n).procs[p.dst].open && AwaitsGet(b(n).procs[p.dst].open[p.msg.id]) && b(n).procs[p.dst].open[p.msg.id].id == p.msg.ans.id)
    ensures Inv(docs, b, a, n+1)
  {
    var self := p.dst;
    var s := b(n).procs[self];
    KeepsGets(self, s, Request(p.src, p.msg), b(n).now);
    assert r.state.AtNode?;
    ShapeAt(docs, b(n), self, r.state);
    assert b(n+1).procs == b(n).procs[self := r.state];
    assert b(n+1).procs.Keys == b(n).procs.Keys;
    assert b(n+1).procs[Bucket] == b(n).procs[Bucket];
    assert Anchored(b(n+1).procs[Bucket]);
    reveal Lt();
    forall node | node in b(n+1).procs && node.Node?
      ensures NodeOpen(b, a, n+1, node)
    {
      if node == self {
        var open' := r.state.open;
        forall oid | oid in open' && AwaitsGet(open'[oid])
          ensures Entry(b, a, n+1, self, oid)
        {
          assert oid in s.open && s.open[oid] == open'[oid];
          var c := s.open[oid];
          assert Entry(b, a, n, self, oid);
          var i :| Lt(i, n) && a(i) == Deliver(Packet(c.caller, self, Req(c.cid, PromiseGet(c.id)))) && Held(b, self, c.id, c.caller, c.cid, i, n);
          HeldLater(b, self, c.id, c.caller, c.cid, i, n);
          assert Lt(i, n + 1);
          assert open'[oid] == Prepare(c.caller, c.id, AskGet, c.cid);
        }
      } else {
        assert b(n+1).procs[node] == b(n).procs[node];
        OpenFrame(b, a, n, node);
      }
    }
    forall q | q in b(n+1).inflight && IsGet(q.msg)
      ensures q.src.Node? && q.src in b(n+1).procs && q.dst == Bucket
    {
      Split(base, self, r, q);
      if q in base.inflight {
        assert q in b(n).inflight;
        assert q.src in b(n+1).procs.Keys;
      } else {
        InSent(self, r.sends, q);
        var j :| 0 <= j < |r.sends| && q == Packet(self, r.sends[j].to, r.sends[j].msg);
        assert IsGet(r.sends[j].msg);
        assert r.sends[j].to == Bucket;
        assert self in b(n+1).procs.Keys;
      }
    }
    forall q | q in b(n+1).inflight && IsGot(q.msg)
      ensures q.src == Bucket && q.dst.Node? && q.dst in b(n+1).procs
    {
      OldPackets(base, self, r, q, true);
      assert q in base.inflight && q in b(n).inflight;
      assert q.dst in b(n+1).procs.Keys;
    }
    forall q | q in b(n+1).inflight && IsPromiseReply(q.msg)
      ensures q.src.Node? && Justified(docs, b, a, n+1, q.src, q.dst, q.msg.id, q.msg.ans.answer)
    {
      OldPackets(base, self, r, q, false);
      assert q in base.inflight && q in b(n).inflight;
      JustifyLater(docs, b, a, n, q.src, q.dst, q.msg.id, q.msg.ans.answer);
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
        forall id | id in open && AwaitsGet(open[id]) ensures Entry(b, a, 0, node, id) {}
      }
    } else {
      Safe(docs, clients, nodes, ask, b, a, n - 1);
      StepOk(docs, clients, nodes, ask, b, a, n - 1);
    }
  }

  // Every document the world is holding: stored, in flight, or waiting in a continuation.
  ghost predicate StoredOk(s: State, now: nat) {
    s.AtBucket? ==> forall key | key in s.docs :: Temp.WellFormed(s.docs[key], now)
  }

  ghost predicate HeldOk(s: State, now: nat) {
    s.AtNode? ==>
      forall rpc | rpc in s.open && s.open[rpc].Process? ::
        forall k | 0 <= k < |s.open[rpc].effects| && s.open[rpc].effects[k].Write? ::
          Temp.WellFormed(s.open[rpc].effects[k].doc, now)
  }

  ghost predicate FlightOk(flight: multiset<Packet<Pid, Msg>>, now: nat) {
    && (forall p {:trigger flight[p]} :: flight[p] > 0 && p.msg.Res? && p.msg.ans.Got? ==>
         Temp.WellFormed(p.msg.ans.doc, now))
    && (forall p {:trigger flight[p]} :: flight[p] > 0 && p.msg.Req? && p.msg.ask.WriteDoc? ==>
         Temp.WellFormed(p.msg.ask.doc, now))
  }

  ghost predicate Formed(n: Net<Pid, Msg, State>) {
    && (forall pid {:trigger n.procs[pid]} :: pid in n.procs ==>
         && StoredOk(n.procs[pid], n.now)
         && HeldOk(n.procs[pid], n.now))
    && FlightOk(n.inflight, n.now)
  }

  lemma EmptyFormed(now: nat)
    ensures Temp.WellFormed(Empty(), now)
  {
  }

  lemma NodeStepForms(self: Pid, s: State, i: Input<Pid, Msg>, now: nat)
    requires self.Node? && s.AtNode?
    requires HeldOk(s, now)
    requires i.Request? && IsGot(i.msg) ==> Temp.WellFormed(i.msg.ans.doc, now)
    ensures var r := Node.step(self, s, i, now);
      && r.state.AtNode?
      && HeldOk(r.state, now)
      && (forall j | 0 <= j < |r.sends| && r.sends[j].msg.Req? && r.sends[j].msg.ask.WriteDoc? ::
           Temp.WellFormed(r.sends[j].msg.ask.doc, now))
      && (forall j | 0 <= j < |r.sends| && r.sends[j].msg.Res? && r.sends[j].msg.ans.Got? ::
           Temp.WellFormed(r.sends[j].msg.ans.doc, now))
  {
    var r := Node.step(self, s, i, now);
    match i
    case Timeout =>
      assert r == Result(s, [], Keep);
    case Request(_, Res(rpc, Got(id, doc, version))) =>
      if rpc in s.open && s.open[rpc].Prepare? && s.open[rpc].id == id {
        Node.StepKeepsWellFormed(self, s, i, now);
        var plan := Node.Prepare(s, s.open[rpc].job, id, doc, version, now);
        if |plan.effects| == 0 {
          assert r.state.open == s.open - {rpc};
        } else {
          var next := Hash(rpc);
          assert next in r.state.open && r.state.open[next].effects == plan.effects;
          forall rpc' | rpc' in r.state.open && r.state.open[rpc'].Process?
            ensures forall k | 0 <= k < |r.state.open[rpc'].effects| && r.state.open[rpc'].effects[k].Write? ::
              Temp.WellFormed(r.state.open[rpc'].effects[k].doc, now)
          {
            if rpc' == next {
              forall k | 0 <= k < |plan.effects| && plan.effects[k].Write?
                ensures Temp.WellFormed(plan.effects[k].doc, now)
              {
                Node.RequestKeepsWellFormed(s, s.open[rpc].job, id, doc, version, now);
              }
            } else {
              assert rpc' in s.open && r.state.open[rpc'] == s.open[rpc'];
            }
          }
        }
      } else {
        assert r == Result(s, [], Keep);
      }
    case Request(_, Res(rpc, TimeoutPut(id, clock))) =>
      if rpc in s.open && s.open[rpc].id == id && Node.Head(s, rpc, Put(clock)) {
        assert r == Node.Reschedule(s, rpc);
        KeptTail(s, rpc, now, r);
      } else {
        assert r == Result(s, [], Keep);
      }
    case Request(_, Res(rpc, DocWrote(id, _))) =>
      if rpc in s.open && s.open[rpc].id == id && s.open[rpc].Process? && |s.open[rpc].effects| > 0 && s.open[rpc].effects[0].Write? {
        assert r == Node.Reschedule(s, rpc);
        KeptTail(s, rpc, now, r);
      } else {
        assert r == Result(s, [], Keep);
      }
    case Request(_, Res(rpc, DocRejected(id))) =>
      if rpc in s.open && s.open[rpc].id == id && s.open[rpc].Process? && |s.open[rpc].effects| > 0 && s.open[rpc].effects[0].Write? {
        assert r.state.open == s.open - {rpc};
        assert r.sends == [];
      } else {
        assert r == Result(s, [], Keep);
      }
    case Request(_, Res(rpc, TimeoutDropped(id, clock))) =>
      if rpc in s.open && s.open[rpc].id == id && Node.Head(s, rpc, Effect.Drop(clock)) {
        assert r == Node.Reschedule(s, rpc);
        KeptTail(s, rpc, now, r);
      } else {
        assert r == Result(s, [], Keep);
      }
    case _ =>
      assert |r.sends| == 0 || r.sends[0].msg.Req?;
      if |r.sends| == 1 {
        assert !r.sends[0].msg.ask.WriteDoc?;
      }
      forall rpc' | rpc' in r.state.open && r.state.open[rpc'].Process?
        ensures forall k | 0 <= k < |r.state.open[rpc'].effects| && r.state.open[rpc'].effects[k].Write? ::
          Temp.WellFormed(r.state.open[rpc'].effects[k].doc, now)
      {
        if r.state == s {
        } else {
          assert !r.state.open[rpc'].Process? || rpc' in s.open;
          if rpc' in s.open && r.state.open[rpc'] == s.open[rpc'] {
          } else {
            assert !r.state.open[rpc'].Process?;
          }
        }
      }
  }

  lemma KeptTail(s: State, rpc: Uuid, now: nat, r: Result<Pid, Msg, State>)
    requires s.AtNode? && rpc in s.open && s.open[rpc].Process? && |s.open[rpc].effects| > 0
    requires HeldOk(s, now)
    requires r == Node.Reschedule(s, rpc)
    ensures HeldOk(r.state, now)
    ensures forall j | 0 <= j < |r.sends| && r.sends[j].msg.Req? && r.sends[j].msg.ask.WriteDoc? ::
      Temp.WellFormed(r.sends[j].msg.ask.doc, now)
    ensures forall j | 0 <= j < |r.sends| && r.sends[j].msg.Res? && r.sends[j].msg.ans.Got? ::
      true
  {
    var phase := s.open[rpc];
    var tail := phase.effects[1..];
    if |tail| == 0 {
      assert r.state.open == s.open - {rpc};
      assert |r.sends| == 1 && r.sends[0].msg.Res?;
    } else {
      var next := Hash(rpc);
      assert r.state.open[next].effects == tail;
      assert r.sends == [ReqTo(Bucket, next, Node.SendEffect(phase.id, tail[0]))];
      forall rpc' | rpc' in r.state.open && r.state.open[rpc'].Process?
        ensures forall k | 0 <= k < |r.state.open[rpc'].effects| && r.state.open[rpc'].effects[k].Write? ::
          Temp.WellFormed(r.state.open[rpc'].effects[k].doc, now)
      {
        if rpc' == next {
          forall k | 0 <= k < |tail| && tail[k].Write?
            ensures Temp.WellFormed(tail[k].doc, now)
          {
            assert phase.effects[k + 1] == tail[k];
          }
        } else {
          assert rpc' in s.open && r.state.open[rpc'] == s.open[rpc'];
        }
      }
      if r.sends[0].msg.ask.WriteDoc? {
        assert tail[0].Write? && r.sends[0].msg.ask.doc == tail[0].doc;
      }
    }
  }

  lemma BucketStepForms(self: Pid, s: State, i: Input<Pid, Msg>, now: nat)
    requires self.Bucket? && s.AtBucket?
    requires StoredOk(s, now)
    requires i.Request? && i.msg.Req? && i.msg.ask.WriteDoc? ==> Temp.WellFormed(i.msg.ask.doc, now)
    ensures var r := Bucket.step(self, s, i, now);
      && StoredOk(r.state, now)
      && (forall j | 0 <= j < |r.sends| && r.sends[j].msg.Res? && r.sends[j].msg.ans.Got? ::
           Temp.WellFormed(r.sends[j].msg.ans.doc, now))
      && (forall j | 0 <= j < |r.sends| && r.sends[j].msg.Req? && r.sends[j].msg.ask.WriteDoc? ::
           Temp.WellFormed(r.sends[j].msg.ask.doc, now))
  {
    var r := Bucket.step(self, s, i, now);
    match i
    case Timeout =>
      assert r == Result(s, [], Keep);
    case Request(_, Req(_, Get(id))) =>
      var got := DocumentAt(s.docs, id);
      if DocKey(id) in s.docs {
        assert got == s.docs[DocKey(id)];
      } else {
        EmptyFormed(now);
        assert got == Empty();
      }
      assert r.sends == [Answer(i.from, i.msg, Got(id, got, VersionOf(s.ver, DocKey(id))))];
      assert r.state == s;
    case Request(_, Req(_, WriteDoc(_, key, doc, version, cover))) =>
      if VersionOf(s.ver, key) == version && Bucket.Accept(s, key, doc, cover) {
        assert r.state.docs == s.docs[key := doc];
        forall k | k in r.state.docs
          ensures Temp.WellFormed(r.state.docs[k], now)
        {
          if k == key {
            assert r.state.docs[k] == doc;
          } else {
            assert r.state.docs[k] == s.docs[k];
          }
        }
      } else {
        assert r.state == s;
      }
      assert |r.sends| == 1 && r.sends[0].msg.Res? && !r.sends[0].msg.ans.Got?;
    case _ =>
      assert r.state.AtBucket? && r.state.docs == s.docs;
      assert forall j :: 0 <= j < |r.sends| ==> r.sends[j].msg.Res? && !r.sends[j].msg.ans.Got?;
  }

  lemma FlightAdd(before: multiset<Packet<Pid, Msg>>, src: Pid, sends: seq<Send<Pid, Msg>>, now: nat, gone: Packet<Pid, Msg>)
    requires FlightOk(before, now)
    requires gone in before
    requires forall j | 0 <= j < |sends| && sends[j].msg.Res? && sends[j].msg.ans.Got? ::
      Temp.WellFormed(sends[j].msg.ans.doc, now)
    requires forall j | 0 <= j < |sends| && sends[j].msg.Req? && sends[j].msg.ask.WriteDoc? ::
      Temp.WellFormed(sends[j].msg.ask.doc, now)
    ensures FlightOk(before - multiset{gone} + ToPackets(src, sends), now)
  {
    var flight := before - multiset{gone} + ToPackets(src, sends);
    forall p | p in flight && p.msg.Res? && p.msg.ans.Got?
      ensures Temp.WellFormed(p.msg.ans.doc, now)
    {
      if p in before - multiset{gone} {
        assert p in before;
      } else {
        InToPackets(src, sends, p);
        var j :| 0 <= j < |sends| && p == Packet(src, sends[j].to, sends[j].msg);
      }
    }
    forall p | p in flight && p.msg.Req? && p.msg.ask.WriteDoc?
      ensures Temp.WellFormed(p.msg.ask.doc, now)
    {
      if p in before - multiset{gone} {
        assert p in before;
      } else {
        InToPackets(src, sends, p);
        var j :| 0 <= j < |sends| && p == Packet(src, sends[j].to, sends[j].msg);
      }
    }
  }

  lemma FormedLater(n: Net<Pid, Msg, State>)
    requires Formed(n)
    ensures Formed(n.(now := n.now + 1))
  {
    var n' := n.(now := n.now + 1);
    forall pid | pid in n'.procs
      ensures StoredOk(n'.procs[pid], n'.now) && HeldOk(n'.procs[pid], n'.now)
    {
      assert n'.procs[pid] == n.procs[pid];
      if n.procs[pid].AtBucket? {
        forall key | key in n.procs[pid].docs
          ensures Temp.WellFormed(n.procs[pid].docs[key], n'.now)
        { Temp.WellFormedLater(n.procs[pid].docs[key], n.now, n'.now); }
      }
      if n.procs[pid].AtNode? {
        forall rpc | rpc in n.procs[pid].open && n.procs[pid].open[rpc].Process?
          ensures forall k | 0 <= k < |n.procs[pid].open[rpc].effects| && n.procs[pid].open[rpc].effects[k].Write? ::
            Temp.WellFormed(n.procs[pid].open[rpc].effects[k].doc, n'.now)
        {
          forall k | 0 <= k < |n.procs[pid].open[rpc].effects| && n.procs[pid].open[rpc].effects[k].Write?
            ensures Temp.WellFormed(n.procs[pid].open[rpc].effects[k].doc, n'.now)
          { Temp.WellFormedLater(n.procs[pid].open[rpc].effects[k].doc, n.now, n'.now); }
        }
      }
    }
    forall p | p in n'.inflight && p.msg.Res? && p.msg.ans.Got?
      ensures Temp.WellFormed(p.msg.ans.doc, n'.now)
    { Temp.WellFormedLater(p.msg.ans.doc, n.now, n'.now); }
    forall p | p in n'.inflight && p.msg.Req? && p.msg.ask.WriteDoc?
      ensures Temp.WellFormed(p.msg.ask.doc, n'.now)
    { Temp.WellFormedLater(p.msg.ask.doc, n.now, n'.now); }
  }

  // One step. Documents that were well-formed are well-formed afterwards.
  lemma FormedStep(docs: map<string, Temp.Doc>, clients: set<nat>, nodes: set<nat>, ask: nat -> Ask,
                   n: Net<Pid, Msg, State>, n': Net<Pid, Msg, State>, a: Action<Pid, Msg>)
    requires Routed(clients, nodes, ask)
    requires Formed(n)
    requires NextStep(World(docs, clients, nodes, ask), n, n', a)
    ensures Formed(n')
  {
    var w := World(docs, clients, nodes, ask);
    assert w.process == Processes;
    match a
    case Tick =>
      assert n' == n.(now := n.now + 1);
      FormedLater(n);
    case Drop(p) =>
      assert n'.procs == n.procs && n'.now == n.now;
      forall q | q in n'.inflight ensures q in n.inflight {}
    case Duplicate(p) =>
      assert n'.procs == n.procs && n'.now == n.now;
      forall q | q in n'.inflight
        ensures q in n.inflight
      {
        if q != p { assert n.inflight[q] == n'.inflight[q]; }
      }
    case Fire(pid) =>
      var s0 := n.procs[pid];
      var r := w.process(pid).step(pid, s0, Timeout, n.now);
      if pid.Client? && s0.AtClient? && s0.waiting {
        OnTimeout(pid, s0, n.now);
        assert |r.sends| == 1 && r.sends[0].msg.Req? && !r.sends[0].msg.ask.WriteDoc?;
        assert r.state.AtClient?;
      } else {
        assert r == Result(s0, [], Keep);
      }
      var base := n.(timers := n.timers - {pid});
      assert n' == Advance(base, pid, r);
      assert n'.now == n.now;
      forall id | id in n'.procs
        ensures StoredOk(n'.procs[id], n'.now) && HeldOk(n'.procs[id], n'.now)
      {
        if id == pid {
          if pid.Client? && s0.AtClient? && s0.waiting {
            assert n'.procs[id].AtClient?;
          } else {
            assert n'.procs[id] == n.procs[id];
          }
        } else {
          assert n'.procs[id] == n.procs[id];
        }
      }
      if |r.sends| == 0 {
        assert n'.inflight == base.inflight;
        forall q | q in n'.inflight ensures q in n.inflight {}
      } else {
        assert n'.inflight == n.inflight + ToPackets(pid, r.sends);
        forall q | q in n'.inflight && q.msg.Res? && q.msg.ans.Got?
          ensures Temp.WellFormed(q.msg.ans.doc, n.now)
        {
          if q in n.inflight {
          } else {
            InToPackets(pid, r.sends, q);
            var j :| 0 <= j < |r.sends| && q == Packet(pid, r.sends[j].to, r.sends[j].msg);
            assert !r.sends[j].msg.Res?;
          }
        }
        forall q | q in n'.inflight && q.msg.Req? && q.msg.ask.WriteDoc?
          ensures Temp.WellFormed(q.msg.ask.doc, n.now)
        {
          if q in n.inflight {
          } else {
            InToPackets(pid, r.sends, q);
            var j :| 0 <= j < |r.sends| && q == Packet(pid, r.sends[j].to, r.sends[j].msg);
            assert !r.sends[j].msg.ask.WriteDoc?;
          }
        }
      }
    case Deliver(p) =>
      var r := w.process(p.dst).step(p.dst, n.procs[p.dst], Request(p.src, p.msg), n.now);
      var base := n.(inflight := n.inflight - multiset{p});
      assert n' == Advance(base, p.dst, r);
      assert n'.now == n.now;
      match p.dst
      case Client(_) =>
        assert r == Result(n.procs[p.dst], [], Keep);
        assert n'.procs == n.procs;
        assert n'.inflight == base.inflight;
        forall q | q in n'.inflight ensures q in n.inflight {}
      case Bucket =>
        if n.procs[Bucket].AtBucket? {
          BucketStepForms(Bucket, n.procs[Bucket], Request(p.src, p.msg), n.now);
        } else {
          assert r == Result(n.procs[Bucket], [], Keep);
        }
        assert n'.procs == n.procs[Bucket := r.state];
        forall id | id in n'.procs
          ensures StoredOk(n'.procs[id], n'.now) && HeldOk(n'.procs[id], n'.now)
        {
          if id == Bucket {
            assert n'.procs[id] == r.state;
          } else {
            assert n'.procs[id] == n.procs[id];
          }
        }
        FlightAdd(n.inflight, Bucket, r.sends, n.now, p);
      case Node(i) =>
        if n.procs[p.dst].AtNode? {
          NodeStepForms(p.dst, n.procs[p.dst], Request(p.src, p.msg), n.now);
        } else {
          assert r == Result(n.procs[p.dst], [], Keep);
        }
        assert n'.procs == n.procs[p.dst := r.state];
        forall id | id in n'.procs
          ensures StoredOk(n'.procs[id], n'.now) && HeldOk(n'.procs[id], n'.now)
        {
          if id == p.dst {
            assert n'.procs[id] == r.state;
            if n.procs[p.dst].AtNode? {
              assert r.state.AtNode?;
            } else {
              assert r.state == n.procs[p.dst];
            }
          } else {
            assert n'.procs[id] == n.procs[id];
          }
        }
        FlightAdd(n.inflight, p.dst, r.sends, n.now, p);
  }

  lemma FormedBoot(docs: map<string, Temp.Doc>, clients: set<nat>, nodes: set<nat>, ask: nat -> Ask,
                   n: Net<Pid, Msg, State>)
    requires Routed(clients, nodes, ask)
    requires IsInit(World(docs, clients, nodes, ask), n)
    requires forall key | key in docs :: Temp.WellFormed(docs[key], 0)
    ensures Formed(n)
  {
    Booted(docs, clients, nodes, ask, n);
    var bucket := n.procs[Bucket];
    assert bucket == AtBucket(docs, map[], Bucket.BootTimeouts(docs), Bucket.BootAnchor(docs));
    forall key | key in bucket.docs
      ensures Temp.WellFormed(bucket.docs[key], 0)
    {
      assert bucket.docs[key] == docs[key];
    }
    assert n.inflight == multiset{};
    forall pid | pid in n.procs && pid.Node?
      ensures n.procs[pid].open == map[]
    {
      assert n.procs[pid] == AtNode(map[], map[], 0, pid.i + 1);
    }
  }

  lemma DocumentsStay(docs: map<string, Temp.Doc>, clients: set<nat>, nodes: set<nat>, ask: nat -> Ask,
                      b: nat -> Net<Pid, Msg, State>, a: nat -> Action<Pid, Msg>, n: nat)
    requires Routed(clients, nodes, ask)
    requires forall key | key in docs :: Temp.WellFormed(docs[key], 0)
    requires IsBehavior(World(docs, clients, nodes, ask), b, a)
    ensures Formed(b(n))
    decreases n
  {
    if n == 0 {
      assert IsInit(World(docs, clients, nodes, ask), b(0));
      FormedBoot(docs, clients, nodes, ask, b(0));
    } else {
      DocumentsStay(docs, clients, nodes, ask, b, a, n - 1);
      FormedStep(docs, clients, nodes, ask, b(n - 1), b(n), a(n - 1));
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
}
