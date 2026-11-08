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
  // What a prepared handler still has to do to the store, head first.
  datatype Effect =
    | Put(clock: Clock)
    | Write(key: string, doc: Temp.Doc, version: nat, cover: Temp.Opt<Clock>)
    | Drop(clock: Clock)
  // The phase is named for what runs next. Prepare: the document is in flight.
  // Process: the effects still to send. Process is rescheduled until that list
  // is empty. `remember` writes `keep` into the armed map when the write lands.
  // `cid` is the caller's request. `rpc` is the store request in flight.
  datatype Cont =
    | Prepare(caller: Pid, job: Job, cid: Uuid, rpc: Uuid)
    | Process(caller: Pid, reply: Temp.Answer, effects: seq<Effect>, keep: Temp.Opt<Clock>, remember: bool, cid: Uuid, rpc: Uuid)

  predicate AwaitsGet(c: Cont) { c.Prepare? && c.job.AskGet? }
  datatype Ask = Ask(id: string, node: nat, kind: Kind)
  // The two bodies of one exchange. A request carries a ReqBody. A response
  // carries a ResBody and cites the request's id.
  datatype ReqBody =
    | PromiseGet(id: string)
    | PromiseCreate(req: Temp.CreateReq)
    | Get(id: string)
    | PutTimeout(id: string, clock: Clock)
    | WriteDoc(id: string, key: string, doc: Temp.Doc, version: nat, cover: Temp.Opt<Clock>)
    | DropTimeout(id: string, clock: Clock)
  datatype ResBody =
    | PromiseReply(answer: Temp.Answer)
    | Created(answer: Temp.Answer)
    | Got(id: string, doc: Temp.Doc, version: nat)
    | TimeoutPut(id: string, clock: Clock)
    | DocWrote(id: string, key: string)
    | DocRejected(id: string)
    | TimeoutDropped(id: string, clock: Clock)
  type Msg = RR<ReqBody, ResBody>
  datatype State =
    | AtClient(id: string, node: nat, kind: Kind, waiting: bool)
    | AtNode(open: map<string, Cont>, armed: map<string, Clock>, next: nat, owner: nat, ids: Supply)
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

  predicate IsGet(m: Msg) { m.Req? && m.ask.Get? }
  predicate IsGot(m: Msg) { m.Res? && m.ans.Got? }
  predicate IsPromiseGet(m: Msg) { m.Req? && m.ask.PromiseGet? }
  predicate IsPromiseReply(m: Msg) { m.Res? && m.ans.PromiseReply? }
}
