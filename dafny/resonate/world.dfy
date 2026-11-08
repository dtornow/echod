include "client.dfy"
include "bucket.dfy"
include "node.dfy"

// Any number of clients, any number of Resonate servers, and one document store.

module Worlds {
  import opened Network
  import opened Protocol
  import opened Client
  import opened Bucket
  import opened Node
  import Temp

  function Pids(clients: set<nat>, nodes: set<nat>): set<Pid> {
    (set c | c in clients :: Client(c)) + (set i | i in nodes :: Node(i)) + {Bucket}
  }

  ghost predicate Routed(clients: set<nat>, nodes: set<nat>, ask: nat -> Ask) {
    forall c {:trigger ask(c)} :: c in clients ==> ask(c).node in nodes
  }

  function Boot(docs: map<string, Temp.Doc>, ask: nat -> Ask, self: Pid): State {
    match self
    case Client(c) => AtClient(ask(c).id, ask(c).node, ask(c).kind, true)
    case Node(i) => AtNode(map[], map[], 0, i + 1)
    case Bucket => AtBucket(docs, map[], BootTimeouts(docs), BootAnchor(docs))
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
}
