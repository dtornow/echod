include "../framework/framework.dfy"
include "temp.dfy"

// The ids, the messages, and the state of a world: clients, Resonate servers,
// and one document store. Each process's step lives in its own file.

module Protocol {
  import opened Network
  import Temp

  datatype Pid = Client(c: nat) | Node(i: nat) | Bucket
  datatype Kind = Read | Create(timeout: nat)
  datatype Clock = Due(key: string, at: nat, owner: nat, token: nat)
  datatype Cont =
    | WaitGet(caller: Pid)
    | Load(caller: Pid, req: Temp.CreateReq)
    | Arm(caller: Pid, key: string, after: Temp.Doc, version: nat, answer: Temp.Answer, clock: Clock, forget: Temp.Opt<Clock>)
    | Writing(caller: Pid, key: string, answer: Temp.Answer, kept: Temp.Opt<Clock>, forget: Temp.Opt<Clock>)
    | Disarm(caller: Pid, answer: Temp.Answer, kept: Temp.Opt<Clock>, gone: Clock)
  datatype Ask = Ask(id: string, node: nat, kind: Kind)
  datatype Msg =
    | PromiseGet(id: string)
    | PromiseCreate(req: Temp.CreateReq)
    | PromiseReply(answer: Temp.Answer)
    | Created(answer: Temp.Answer)
    | Get(id: string)
    | Got(id: string, doc: Temp.Doc, version: nat)
    | PutTimeout(id: string, clock: Clock)
    | TimeoutPut(id: string, clock: Clock)
    | WriteDoc(id: string, key: string, doc: Temp.Doc, version: nat, cover: Temp.Opt<Clock>)
    | DocWrote(id: string, key: string)
    | DocRejected(id: string)
    | DropTimeout(id: string, clock: Clock)
    | TimeoutDropped(id: string, clock: Clock)
  datatype State =
    | AtClient(id: string, node: nat, kind: Kind, waiting: bool)
    | AtNode(open: map<string, Cont>, armed: map<string, Clock>, next: nat, owner: nat)
    | AtBucket(docs: map<string, Temp.Doc>, ver: map<string, nat>, timeouts: set<Clock>, anchor: map<string, Clock>)

  function Empty(): Temp.Doc { Temp.Origin(0, map[]) }
  function DocKey(id: string): string { "wf/" + Temp.OriginOf(id) }

  function DocumentAt(docs: map<string, Temp.Doc>, id: string): Temp.Doc {
    var key := DocKey(id);
    if key in docs then docs[key] else Empty()
  }

  function VersionOf(ver: map<string, nat>, key: string): nat {
    if key in ver then ver[key] else 0
  }
}
