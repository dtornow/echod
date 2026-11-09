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
  lemma PromiseGetReceived(docs: map<string, Temp.Doc>, clients: set<nat>, nodes: set<nat>,
                           tr: nat -> Moment<Pid, Msg, State>,
                           r: nat, node: Pid, from: Pid, cid: Uuid, answer: Temp.Answer)
    requires Behavior(docs, clients, nodes, tr)
    requires node.Node?
    requires tr(r).event == Deliver(Packet(node, from, Res(cid, PromiseReply(answer))))
    ensures exists i: nat, k: nat, id, doc, version {:trigger tr(i).event, tr(k).event, GotPacket(node, Hash(cid), id, doc, version)} ::
      && i < k < r
      && tr(i).event == Deliver(Packet(from, node, Req(cid, PromiseGet(id))))
      && tr(k).event == Deliver(Packet(Bucket, node, Res(Hash(cid), Got(id, doc, version))))
      && Bucket in tr(k).state.procs && tr(k).state.procs[Bucket].AtBucket?
      && node in tr(k).state.procs && tr(k).state.procs[node].AtNode?
      && Hash(cid) in tr(k).state.procs[node].open
      && tr(k).state.procs[node].open[Hash(cid)] == Prepare(from, id, AskGet, cid)
      && answer == Temp.Get(doc, id, tr(k).state.now).answer
      && (id !in Temp.ObjectsOf(doc) ==> answer == Temp.Answer(404, Temp.None))
      && (id in Temp.ObjectsOf(doc) ==>
           answer == Temp.Answer(200, Temp.Some(Temp.Project(Temp.ObjectsOf(doc)[id], tr(k).state.now).promise)))
  {
    Safe(docs, clients, nodes, tr, r);
    var w := World(docs, clients, nodes);
    assert NextStep(w, tr(r).state, tr(r+1).state, tr(r).event);
    var pk := Packet(node, from, Res(cid, PromiseReply(answer)));
    reveal Lt();
    assert pk in tr(r).state.inflight;
    assert Justified(docs, tr, r, node, from, cid, answer);
    var i, k, id, doc, version :|
      && Lt(i, k) && Lt(k, r)
      && node.Node?
      && tr(i).event == Deliver(Packet(from, node, Req(cid, PromiseGet(id))))
      && tr(k).event == Deliver(GotPacket(node, Hash(cid), id, doc, version))
      && Bucket in tr(k).state.procs && tr(k).state.procs[Bucket].AtBucket?
      && node in tr(k).state.procs && tr(k).state.procs[node].AtNode?
      && Hash(cid) in tr(k).state.procs[node].open
      && tr(k).state.procs[node].open[Hash(cid)] == Prepare(from, id, AskGet, cid)
      && answer == Temp.Get(doc, id, tr(k).state.now).answer;
    Cases(doc, id, tr(k).state.now);
  }

  // Every trace of a world whose bucket starts empty. Every document is well-formed
  // at every time: stored in the bucket, in flight, or waiting on a continuation.
  lemma DocumentsStayWellFormed(tr: nat -> Moment<Pid, Msg, State>)
    requires exists clients: set<nat>, nodes: set<nat> :: Behavior(map[], clients, nodes, tr)
    ensures forall t: nat :: Formed(tr(t).state)
  {
    var clients, nodes :| Behavior(map[], clients, nodes, tr);
    forall t: nat ensures Formed(tr(t).state) {
      DocumentsStay(map[], clients, nodes, tr, t);
    }
  }

  // Every stored document that owes a deadline has a timeout at or before it.
  // A document that owes nothing does not need one.
  lemma WorkflowsHaveTimeouts(docs: map<string, Temp.Doc>, clients: set<nat>, nodes: set<nat>,
                              tr: nat -> Moment<Pid, Msg, State>, n: nat)
    requires Behavior(docs, clients, nodes, tr)
    ensures Bucket in tr(n).state.procs && tr(n).state.procs[Bucket].AtBucket?
    ensures forall key | key in tr(n).state.procs[Bucket].docs ::
      match Temp.Nearest(tr(n).state.procs[Bucket].docs[key])
      case None => true
      case Some(d) => exists t :: t in tr(n).state.procs[Bucket].timeouts && t.key == key && t.at <= d
  {
    Safe(docs, clients, nodes, tr, n);
    var bucket := tr(n).state.procs[Bucket];
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
