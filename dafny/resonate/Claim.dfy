include "Proof.dfy"

// The theorems about a world of clients, nodes, and one bucket.
// Proof holds the invariant and the lemmas these two call.

module Claim {
  import opened Network
  import opened Protocol
  import opened Worlds
  import Temp
  import opened Proof

  // A delivered promise reply is the Get of the document the bucket returned
  // on that node, strictly between the request and the reply, while that
  // continuation was open. A missing id is 404. An id that is present is the
  // projection of that promise at the instant of the read.
  lemma PromiseGetReceived(docs: map<string, Temp.Doc>, clients: set<nat>, nodes: set<nat>, ask: nat -> Ask,
                           b: nat -> Net<Pid, Msg, State>, a: nat -> Action<Pid, Msg>,
                           r: nat, node: Pid, from: Pid, cid: nat, answer: Temp.Answer)
    requires Routed(clients, nodes, ask)
    requires IsBehavior(World(docs, clients, nodes, ask), b, a)
    requires node.Node?
    requires a(r) == Deliver(Packet(node, from, Res(cid, PromiseReply(answer))))
    ensures exists i: nat, k: nat, id, doc, version, rpc {:trigger a(i), a(k), GotPacket(node, rpc, id, doc, version)} ::
      && i < k < r
      && a(i) == Deliver(Packet(from, node, Req(cid, PromiseGet(id))))
      && a(k) == Deliver(Packet(Bucket, node, Res(rpc, Got(id, doc, version))))
      && Bucket in b(k).procs && b(k).procs[Bucket].AtBucket?
      && node in b(k).procs && b(k).procs[node].AtNode?
      && id in b(k).procs[node].open
      && b(k).procs[node].open[id] == Reading(from, AskGet, cid, rpc)
      && answer == Temp.Get(doc, id, b(k).now).answer
      && (id !in Temp.ObjectsOf(doc) ==> answer == Temp.Answer(404, Temp.None))
      && (id in Temp.ObjectsOf(doc) ==>
           answer == Temp.Answer(200, Temp.Some(Temp.Project(Temp.ObjectsOf(doc)[id], b(k).now).promise)))
  {
    Safe(docs, clients, nodes, ask, b, a, r);
    var w := World(docs, clients, nodes, ask);
    assert NextStep(w, b(r), b(r+1), a(r));
    var pk := Packet(node, from, Res(cid, PromiseReply(answer)));
    reveal Lt();
    assert pk in b(r).inflight;
    assert Justified(docs, b, a, r, node, from, cid, answer);
    var i, k, id, doc, version, rpc :|
      && Lt(i, k) && Lt(k, r)
      && node.Node?
      && a(i) == Deliver(Packet(from, node, Req(cid, PromiseGet(id))))
      && a(k) == Deliver(GotPacket(node, rpc, id, doc, version))
      && Bucket in b(k).procs && b(k).procs[Bucket].AtBucket?
      && node in b(k).procs && b(k).procs[node].AtNode?
      && id in b(k).procs[node].open
      && b(k).procs[node].open[id] == Reading(from, AskGet, cid, rpc)
      && answer == Temp.Get(doc, id, b(k).now).answer;
    Cases(doc, id, b(k).now);
  }

  // Every stored document that owes a deadline has a timeout at or before it.
  // A document that owes nothing does not need one.
  lemma WorkflowsHaveTimeouts(docs: map<string, Temp.Doc>, clients: set<nat>, nodes: set<nat>, ask: nat -> Ask,
                              b: nat -> Net<Pid, Msg, State>, a: nat -> Action<Pid, Msg>, n: nat)
    requires Routed(clients, nodes, ask)
    requires IsBehavior(World(docs, clients, nodes, ask), b, a)
    ensures Bucket in b(n).procs && b(n).procs[Bucket].AtBucket?
    ensures forall key | key in b(n).procs[Bucket].docs ::
      match Temp.Nearest(b(n).procs[Bucket].docs[key])
      case None => true
      case Some(d) => exists t :: t in b(n).procs[Bucket].timeouts && t.key == key && t.at <= d
  {
    Safe(docs, clients, nodes, ask, b, a, n);
    var bucket := b(n).procs[Bucket];
    assert Anchored(bucket);
    forall key | key in bucket.docs
      ensures match Temp.Nearest(bucket.docs[key])
        case None => true
        case Some(d) => exists t :: t in bucket.timeouts && t.key == key && t.at <= d
    {
      match Temp.Nearest(bucket.docs[key])
      case None =>
      case Some(d) =>
        var t := bucket.anchor[key];
        assert t in bucket.timeouts && t.key == key && t.at <= d;
    }
  }
}
