include "protocol.dfy"

// The Resonate server. One continuation per id in flight.
//
// A handler reads the document, prepares, then processes the store commands
// in order. A promise get prepares a reply and no commands. A promise create
// runs the handler, sweep then create. When the document changes, the
// commands are the timeout for the nearest deadline, the write, and the
// timeout that write replaces. The head command is the one in flight.

module Node {
  import opened Network
  import opened Protocol
  import Temp

  const Retry: nat := 1

  datatype Plan = Plan(
    reply: Temp.Answer,
    created: bool,
    cmds: seq<Cmd>,
    keep: Temp.Opt<Clock>,
    remember: bool,
    next: nat)

  function Prepare(s: State, job: Job, id: string, doc: Temp.Doc, version: nat, now: nat): Plan
    requires s.AtNode?
  {
    match job
    case AskGet => Plan(Temp.Get(doc, id, now).answer, false, [], Temp.None, false, s.next)
    case AskCreate(req) =>
      var applied := Temp.Handle(doc, Temp.PromiseCreate(req), now, Retry);
      if applied.doc == doc then Plan(applied.answer, true, [], Temp.None, false, s.next)
      else
        var key := DocKey(req.id);
        var prev := if key in s.armed then Temp.Some(s.armed[key]) else Temp.None;
        match Temp.Nearest(applied.doc)
        case None =>
          var drop := match prev case None => [] case Some(t) => [Cmd.Drop(t)];
          Plan(applied.answer, true, [Write(key, applied.doc, version, Temp.None)] + drop, Temp.None, true, s.next)
        case Some(d) =>
          var put := Due(key, d, s.owner, s.next);
          var drop := match prev case None => [] case Some(t) => if t == put then [] else [Cmd.Drop(t)];
          Plan(applied.answer, true,
               [Cmd.Put(put), Write(key, applied.doc, version, Temp.Some(put))] + drop,
               Temp.Some(put), true, s.next + 1)
  }

  function Reply(created: bool, answer: Temp.Answer): Msg {
    if created then Created(answer) else PromiseReply(answer)
  }

  function SendCmd(id: string, cmd: Cmd): Msg {
    match cmd
    case Put(clock) => PutTimeout(id, clock)
    case Write(key, doc, version, cover) => WriteDoc(id, key, doc, version, cover)
    case Drop(clock) => DropTimeout(id, clock)
  }

  // The armed map after a write command lands.
  function Remember(armed: map<string, Clock>, cmd: Cmd, keep: Temp.Opt<Clock>, remember: bool): map<string, Clock> {
    if remember && cmd.Write? then
      match keep
      case None => armed - {cmd.key}
      case Some(clock) => armed[clock.key := clock]
    else armed
  }

  // Process the commands. An empty list answers the caller.
  function Process(s: State, id: string, caller: Pid, plan: Plan): Result<Pid, Msg, State>
    requires s.AtNode?
  {
    if plan.cmds == [] then
      Result(AtNode(s.open - {id}, s.armed, plan.next, s.owner), [Send(caller, Reply(plan.created, plan.reply))], Keep)
    else
      var run := Running(caller, plan.reply, plan.cmds, plan.keep, plan.remember);
      Result(AtNode(s.open[id := run], s.armed, plan.next, s.owner), [Send(Bucket, SendCmd(id, plan.cmds[0]))], Keep)
  }

  // The head command was accepted. Remember a write, then send the next command or the reply.
  function Advance(s: State, id: string): Result<Pid, Msg, State>
    requires s.AtNode? && id in s.open && s.open[id].Running? && |s.open[id].cmds| > 0
  {
    var run := s.open[id];
    var armed := Remember(s.armed, run.cmds[0], run.keep, run.remember);
    var rest := run.cmds[1..];
    if rest == [] then
      Result(AtNode(s.open - {id}, armed, s.next, s.owner), [Send(run.caller, Created(run.reply))], Keep)
    else
      var run' := Running(run.caller, run.reply, rest, run.keep, run.remember && !run.cmds[0].Write?);
      Result(AtNode(s.open[id := run'], armed, s.next, s.owner), [Send(Bucket, SendCmd(id, rest[0]))], Keep)
  }

  predicate Head(s: State, id: string, cmd: Cmd)
    requires s.AtNode?
  {
    && id in s.open && s.open[id].Running? && |s.open[id].cmds| > 0 && s.open[id].cmds[0] == cmd
  }

  function step(self: Pid, s: State, i: Input<Pid, Msg>, now: nat): Result<Pid, Msg, State>
  {
    if self.Node? && s.AtNode? then
      match i {
        case Request(from, PromiseGet(id)) =>
          if id in s.open then Result(s, [], Keep)
          else Result(AtNode(s.open[id := Reading(from, AskGet)], s.armed, s.next, s.owner), [Send(Bucket, Msg.Get(id))], Keep)
        case Request(from, PromiseCreate(req)) =>
          if req.id in s.open then Result(s, [], Keep)
          else Result(AtNode(s.open[req.id := Reading(from, AskCreate(req))], s.armed, s.next, s.owner), [Send(Bucket, Msg.Get(req.id))], Keep)
        case Request(_, Got(id, doc, version)) =>
          if id in s.open && s.open[id].Reading? then
            Process(s, id, s.open[id].caller, Prepare(s, s.open[id].job, id, doc, version, now))
          else Result(s, [], Keep)
        case Request(_, TimeoutPut(id, clock)) =>
          if Head(s, id, Cmd.Put(clock)) then Advance(s, id) else Result(s, [], Keep)
        case Request(_, DocWrote(id, _)) =>
          if id in s.open && s.open[id].Running? && |s.open[id].cmds| > 0 && s.open[id].cmds[0].Write? then
            Advance(s, id)
          else Result(s, [], Keep)
        case Request(_, DocRejected(id)) =>
          if id in s.open && s.open[id].Running? && |s.open[id].cmds| > 0 && s.open[id].cmds[0].Write? then
            Result(AtNode(s.open - {id}, s.armed, s.next, s.owner), [], Keep)
          else Result(s, [], Keep)
        case Request(_, TimeoutDropped(id, clock)) =>
          if Head(s, id, Cmd.Drop(clock)) then Advance(s, id) else Result(s, [], Keep)
        case _ => Result(s, [], Keep)
      }
    else Result(s, [], Keep)
  }
}
