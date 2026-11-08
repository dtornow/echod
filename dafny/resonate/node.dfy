include "../framework/framework.dfy"
include "temp.dfy"

// A promise get and a promise create, across the clients, the nodes, and
// the one bucket.
//
// A world names its clients and its nodes. The bucket is the single store.
// It holds the documents and the timeout keys. A missing key is the empty
// origin. Each client asks one node, for a get or a create. Each node holds
// the set of operations in flight, one continuation per id.
//
// A create runs the handler, sweep then promise create. When the document
// changes and still owes a deadline — the nearest of a pending promise, a
// lease, a retry, or a schedule's next run — the node puts a timeout for
// that instant before it writes the document, then deletes the timeout it
// had remembered for the origin. The bucket keeps the timeout the last
// write named while the document still owes a deadline. The theorems about
// a world are in Claim, and their proof is in Proof.

module Node {
  import opened Network
  import Keys
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

  const Retry: nat := 1

  function Empty(): Temp.Doc { Temp.Origin(0, map[]) }
  function DocKey(id: string): string { "wf/" + Temp.OriginOf(id) }

  function DocumentAt(docs: map<string, Temp.Doc>, id: string): Temp.Doc {
    var key := DocKey(id);
    if key in docs then docs[key] else Empty()
  }

  function VersionOf(ver: map<string, nat>, key: string): nat {
    if key in ver then ver[key] else 0
  }

  function Pids(clients: set<nat>, nodes: set<nat>): set<Pid> {
    (set c | c in clients :: Client(c)) + (set i | i in nodes :: Node(i)) + {Bucket}
  }

  ghost predicate Routed(clients: set<nat>, nodes: set<nat>, ask: nat -> Ask) {
    forall c {:trigger ask(c)} :: c in clients ==> ask(c).node in nodes
  }

  function CoverOf(docs: map<string, Temp.Doc>, keys: seq<string>): set<Clock>
    decreases |keys|
  {
    if |keys| == 0 then {}
    else
      var rest := CoverOf(docs, keys[1..]);
      if keys[0] in docs then
        match Temp.Nearest(docs[keys[0]])
        case None => rest
        case Some(d) => rest + {Due(keys[0], d, 0, 0)}
      else rest
  }

  function AnchorOf(docs: map<string, Temp.Doc>, keys: seq<string>): map<string, Clock>
    decreases |keys|
  {
    if |keys| == 0 then map[]
    else
      var rest := AnchorOf(docs, keys[1..]);
      if keys[0] in docs then
        match Temp.Nearest(docs[keys[0]])
        case None => rest
        case Some(d) => rest[keys[0] := Due(keys[0], d, 0, 0)]
      else rest
  }

  function BootTimeouts(docs: map<string, Temp.Doc>): set<Clock> {
    CoverOf(docs, Keys.Sorted(docs.Keys))
  }

  function BootAnchor(docs: map<string, Temp.Doc>): map<string, Clock> {
    AnchorOf(docs, Keys.Sorted(docs.Keys))
  }

  function Boot(docs: map<string, Temp.Doc>, ask: nat -> Ask, self: Pid): State {
    match self
    case Client(c) => AtClient(ask(c).id, ask(c).node, ask(c).kind, true)
    case Node(i) => AtNode(map[], map[], 0, i + 1)
    case Bucket => AtBucket(docs, map[], BootTimeouts(docs), BootAnchor(docs))
  }

  function ClientOn(s: State, i: Input<Pid, Msg>): Result<Pid, Msg, State>
    requires s.AtClient?
  {
    if s.waiting && i.Timeout? then
      var msg :=
        match s.kind
        case Read => PromiseGet(s.id)
        case Create(timeout) => PromiseCreate(Temp.CreateReq(s.id, timeout, Temp.Empty(), []));
      Result(AtClient(s.id, s.node, s.kind, false), [Send(Node(s.node), msg)], Keep)
    else Result(s, [], Keep)
  }

  predicate Accept(s: State, key: string, doc: Temp.Doc, cover: Temp.Opt<Clock>)
    requires s.AtBucket?
  {
    match Temp.Nearest(doc)
    case None => true
    case Some(d) =>
      && cover.Some?
      && (cover.Some? ==> cover.value in s.timeouts && cover.value.key == key && cover.value.at <= d)
  }

  predicate LiveAnchor(s: State, t: Clock)
    requires s.AtBucket?
  {
    && t.key in s.docs && t.key in s.anchor && s.anchor[t.key] == t
    && (t.key in s.docs ==> Temp.Nearest(s.docs[t.key]).Some?)
  }

  function BucketOn(s: State, i: Input<Pid, Msg>): Result<Pid, Msg, State>
    requires s.AtBucket?
  {
    match i
    case Request(from, Get(id)) =>
      var key := DocKey(id);
      Result(s, [Send(from, Got(id, DocumentAt(s.docs, id), VersionOf(s.ver, key)))], Keep)
    case Request(from, PutTimeout(id, clock)) =>
      Result(AtBucket(s.docs, s.ver, s.timeouts + {clock}, s.anchor), [Send(from, TimeoutPut(id, clock))], Keep)
    case Request(from, WriteDoc(id, key, doc, version, cover)) =>
      if VersionOf(s.ver, key) == version && Accept(s, key, doc, cover) then
        var anchor' :=
          match (Temp.Nearest(doc), cover)
          case (None, _) => s.anchor - {key}
          case (Some(_), Some(clock)) => s.anchor[key := clock]
          case (Some(_), None) => s.anchor;
        Result(AtBucket(s.docs[key := doc], s.ver[key := version + 1], s.timeouts, anchor'),
               [Send(from, DocWrote(id, key))], Keep)
      else Result(s, [Send(from, DocRejected(id))], Keep)
    case Request(from, DropTimeout(id, clock)) =>
      if LiveAnchor(s, clock) then Result(s, [Send(from, TimeoutDropped(id, clock))], Keep)
      else Result(AtBucket(s.docs, s.ver, s.timeouts - {clock}, s.anchor), [Send(from, TimeoutDropped(id, clock))], Keep)
    case _ => Result(s, [], Keep)
  }

  function Decide(s: State, id: string, doc: Temp.Doc, version: nat, now: nat): Result<Pid, Msg, State>
    requires s.AtNode? && id in s.open && s.open[id].Load?
  {
    var caller := s.open[id].caller;
    var req := s.open[id].req;
    var applied := Temp.Handle(doc, Temp.PromiseCreate(req), now, Retry);
    if applied.doc == doc then
      Result(AtNode(s.open - {id}, s.armed, s.next, s.owner), [Send(caller, Created(applied.answer))], Keep)
    else
      var key := DocKey(req.id);
      var drop := if key in s.armed then Temp.Some(s.armed[key]) else Temp.None;
      match Temp.Nearest(applied.doc)
      case None =>
        var open' := s.open[id := Writing(caller, key, applied.answer, Temp.None, drop)];
        Result(AtNode(open', s.armed, s.next, s.owner),
               [Send(Bucket, WriteDoc(id, key, applied.doc, version, Temp.None))], Keep)
      case Some(d) =>
        var put := Due(key, d, s.owner, s.next);
        var open' := s.open[id := Arm(caller, key, applied.doc, version, applied.answer, put, drop)];
        Result(AtNode(open', s.armed, s.next + 1, s.owner),
               [Send(Bucket, PutTimeout(id, put))], Keep)
  }

  function GotOn(s: State, id: string, doc: Temp.Doc, version: nat, now: nat): Result<Pid, Msg, State>
    requires s.AtNode?
  {
    if id !in s.open then Result(s, [], Keep)
    else if s.open[id].WaitGet? then
      var answer := Temp.Get(doc, id, now).answer;
      Result(AtNode(s.open - {id}, s.armed, s.next, s.owner), [Send(s.open[id].caller, PromiseReply(answer))], Keep)
    else if s.open[id].Load? then Decide(s, id, doc, version, now)
    else Result(s, [], Keep)
  }

  function ArmOn(s: State, id: string, clock: Clock): Result<Pid, Msg, State>
    requires s.AtNode?
  {
    if id in s.open && s.open[id].Arm? && s.open[id].clock == clock then
      var c := s.open[id];
      var open' := s.open[id := Writing(c.caller, c.key, c.answer, Temp.Some(c.clock), c.forget)];
      Result(AtNode(open', s.armed, s.next, s.owner),
             [Send(Bucket, WriteDoc(id, c.key, c.after, c.version, Temp.Some(c.clock)))], Keep)
    else Result(s, [], Keep)
  }

  function WroteOn(s: State, id: string): Result<Pid, Msg, State>
    requires s.AtNode?
  {
    if id !in s.open then Result(s, [], Keep)
    else match s.open[id] {
      case Writing(caller, key, answer, put, drop) =>
        var armed' :=
          match put
          case None => s.armed - {key}
          case Some(clock) => s.armed[key := clock];
        match drop {
          case None =>
            Result(AtNode(s.open - {id}, armed', s.next, s.owner), [Send(caller, Created(answer))], Keep)
          case Some(t) =>
            if put == Temp.Some(t) then
              Result(AtNode(s.open - {id}, armed', s.next, s.owner), [Send(caller, Created(answer))], Keep)
            else
              var open' := s.open[id := Disarm(caller, answer, put, t)];
              Result(AtNode(open', armed', s.next, s.owner), [Send(Bucket, DropTimeout(id, t))], Keep)
        }
      case _ => Result(s, [], Keep)
    }
  }

  function NodeOn(s: State, i: Input<Pid, Msg>, now: nat): Result<Pid, Msg, State>
    requires s.AtNode?
  {
    match i
    case Request(from, PromiseGet(id)) =>
      if id in s.open then Result(s, [], Keep)
      else Result(AtNode(s.open[id := WaitGet(from)], s.armed, s.next, s.owner), [Send(Bucket, Msg.Get(id))], Keep)
    case Request(from, PromiseCreate(req)) =>
      if req.id in s.open then Result(s, [], Keep)
      else Result(AtNode(s.open[req.id := Load(from, req)], s.armed, s.next, s.owner), [Send(Bucket, Msg.Get(req.id))], Keep)
    case Request(_, Got(id, doc, version)) => GotOn(s, id, doc, version, now)
    case Request(_, TimeoutPut(id, clock)) => ArmOn(s, id, clock)
    case Request(_, DocWrote(id, _)) => WroteOn(s, id)
    case Request(_, DocRejected(id)) =>
      if id in s.open && s.open[id].Writing? then
        Result(AtNode(s.open - {id}, s.armed, s.next, s.owner), [], Keep)
      else Result(s, [], Keep)
    case Request(_, TimeoutDropped(id, _)) =>
      if id in s.open && s.open[id].Disarm? then
        Result(AtNode(s.open - {id}, s.armed, s.next, s.owner), [Send(s.open[id].caller, Created(s.open[id].answer))], Keep)
      else Result(s, [], Keep)
    case _ => Result(s, [], Keep)
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
