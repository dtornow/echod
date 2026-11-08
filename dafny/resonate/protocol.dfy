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
  // What the read was for. Every handler starts as one of these.
  datatype Job = AskGet | AskCreate(req: Temp.CreateReq)
  // The store commands a prepared handler runs, in order.
  datatype Cmd =
    | Put(clock: Clock)
    | Write(key: string, doc: Temp.Doc, version: nat, cover: Temp.Opt<Clock>)
    | Drop(clock: Clock)
  // Reading: the document is in flight. Running: the commands still to send,
  // head first. `remember` writes `keep` into the armed map when the write lands.
  datatype Cont =
    | Reading(caller: Pid, job: Job)
    | Running(caller: Pid, reply: Temp.Answer, cmds: seq<Cmd>, keep: Temp.Opt<Clock>, remember: bool)

  predicate AwaitsGet(c: Cont) { c.Reading? && c.job.AskGet? }
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

  // Everything before the first `:`, or the whole string when there is none.
  function OriginOf(s: string): string
    decreases |s|
  {
    if |s| == 0 then ""
    else if s[0] == ':' then ""
    else [s[0]] + OriginOf(s[1..])
  }

  function EmptyDoc(): Temp.Doc { Temp.Origin(0, map[]) }
  function DocKey(id: string): string { "wf/" + OriginOf(id) }

  function DocumentAt(docs: map<string, Temp.Doc>, id: string): Temp.Doc {
    var key := DocKey(id);
    if key in docs then docs[key] else EmptyDoc()
  }

  function VersionOf(ver: map<string, nat>, key: string): nat {
    if key in ver then ver[key] else 0
  }
}
