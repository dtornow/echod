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

  function Boot(docs: map<string, Temp.Doc>, self: Pid): State {
    match self
    case Client(_) => AtClient
    case Node(i) => AtNode(map[], map[], 0, i + 1)
    case Bucket => AtBucket(docs, map[], Bucket.BootTimeouts(docs), Bucket.BootAnchor(docs))
  }

  // What the world installs. The network holds these and calls process.step.
  function Processes(self: Pid): Process<Pid, Msg, State> {
    match self
    case Client(_) => Network.Process(Client.step)
    case Node(_) => Network.Process(Node.step)
    case Bucket => Network.Process(Bucket.step)
  }

  function World(docs: map<string, Temp.Doc>, clients: set<nat>, nodes: set<nat>): Sys<Pid, Msg, State>
  {
    Sys(Pids(clients, nodes), true, self => Boot(docs, self), Processes)
  }

  // A trace of this world: at every time, the state and the event that takes it to the next state.
  ghost predicate Behavior(docs: map<string, Temp.Doc>, clients: set<nat>, nodes: set<nat>,
                           tr: nat -> Moment<Pid, Msg, State>)
  {
    IsBehavior(World(docs, clients, nodes), tr)
  }
}
