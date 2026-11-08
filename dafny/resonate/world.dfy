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
    case Node(i) => AtNode(map[], map[], 0, i + 1, 0)
    case Bucket => AtBucket(docs, map[], Bucket.BootTimeouts(docs), Bucket.BootAnchor(docs))
  }

  // What the world installs. The network holds these and calls process.step.
  function Processes(self: Pid): Process<Pid, Msg, State> {
    match self
    case Client(_) => Process(Client.step)
    case Node(_) => Process(Node.step)
    case Bucket => Process(Bucket.step)
  }

  function World(docs: map<string, Temp.Doc>, clients: set<nat>, nodes: set<nat>, ask: nat -> Ask): Sys<Pid, Msg, State>
    requires Routed(clients, nodes, ask)
  {
    Sys(Pids(clients, nodes), true, self => Boot(docs, ask, self), Processes)
  }
}
