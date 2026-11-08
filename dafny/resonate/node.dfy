include "protocol.dfy"

// The Resonate server. One continuation per id in flight.
//
// A promise get reads the origin document from the bucket and answers with
// that document's Get. A promise create runs the handler, sweep then create.
// When the document changes and still owes a deadline — the nearest of a
// pending promise, a lease, a retry, or a schedule's next run — the server
// puts a timeout for that instant before it writes the document, then deletes
// the timeout it had remembered for the origin.

module Node {
  import opened Network
  import opened Protocol
  import Temp

  const Retry: nat := 1

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

  function Step(self: Pid, s: State, i: Input<Pid, Msg>, now: nat): Result<Pid, Msg, State>
  {
    if self.Node? && s.AtNode? then
      match i {
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
    else Result(s, [], Keep)
  }

  datatype Machine extends Process<Pid, Msg, State> = Proc {
    function step(self: Pid, s: State, i: Input<Pid, Msg>, now: nat): Result<Pid, Msg, State>
      decreases now
    { Step(self, s, i, now) }
  }
}
