include "client.dfy"
include "bucket.dfy"
include "node.dfy"

// Any number of clients, any number of Resonate servers, and one document store.

module Worlds {
  import opened Network
  import opened Protocol
  import Client
  import Bucket
  import Node
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
    case Bucket => AtBucket(docs, map[], Bucket.BootTimeouts(docs), Bucket.BootAnchor(docs))
  }

  function ProcessOf(self: Pid): Process<Pid, Msg, State> {
    match self
    case Client(_) => Process(Client.Step)
    case Node(_) => Process(Node.Step)
    case Bucket => Process(Bucket.Step)
  }

  // The network calls this. The id picks a process, and that process's step runs.
  function Step(self: Pid, s: State, i: Input<Pid, Msg>, now: nat): Result<Pid, Msg, State> {
    ProcessOf(self).step(self, s, i, now)
  }

  function World(docs: map<string, Temp.Doc>, clients: set<nat>, nodes: set<nat>, ask: nat -> Ask): Sys<Pid, Msg, State>
    requires Routed(clients, nodes, ask)
  {
    Sys(Pids(clients, nodes), true, self => Boot(docs, ask, self), Step)
  }
}
