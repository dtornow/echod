include "protocol.dfy"

module Node {

  import opened Network
  import opened Protocol
  import Temp

  const Retry: nat := 1

  datatype Plan = Plan(
    reply: Temp.Answer,
    created: bool,
    effects: seq<Effect>,
    keep: Temp.Opt<Clock>,
    remember: bool,
    next: nat)

  function step(self: Pid, s: State, i: Input<Pid, Msg>, now: nat): Result<Pid, Msg, State>
  {
    if self.Node? && s.AtNode? then
      match i {
        case Request(from, Req(cid, PromiseGet(id))) =>
          if id in s.open then
            Result(s, [], Keep)
          else
            var drawn := Draw(s.ids);
            Result(AtNode(s.open[id := Cont.Prepare(from, AskGet, cid, drawn.id)], s.armed, s.next, s.owner, drawn.supply),
                   [ReqTo(Bucket, drawn.id, Get(id))], Keep)
        case Request(from, Req(cid, PromiseCreate(req))) =>
          if req.id in s.open then
            Result(s, [], Keep)
          else
            var drawn := Draw(s.ids);
            Result(AtNode(s.open[req.id := Cont.Prepare(from, AskCreate(req), cid, drawn.id)], s.armed, s.next, s.owner, drawn.supply),
                   [ReqTo(Bucket, drawn.id, Get(req.id))], Keep)
        case Request(_, Res(rpc, Got(id, doc, version))) =>
          if id in s.open && s.open[id].Prepare? && s.open[id].rpc == rpc then
            var plan := Prepare(s, s.open[id].job, id, doc, version, now);
            Process(s, id, s.open[id].caller, s.open[id].cid, plan)
          else
            Result(s, [], Keep)
        case Request(_, Res(rpc, TimeoutPut(id, clock))) =>
          if Live(s, id, rpc) && Head(s, id, Put(clock)) then
            Reschedule(s, id)
          else
            Result(s, [], Keep)
        case Request(_, Res(rpc, DocWrote(id, _))) =>
          if Live(s, id, rpc) && s.open[id].Process? && |s.open[id].effects| > 0 && s.open[id].effects[0].Write? then
            Reschedule(s, id)
          else
            Result(s, [], Keep)
        case Request(_, Res(rpc, DocRejected(id))) =>
          if Live(s, id, rpc) && s.open[id].Process? && |s.open[id].effects| > 0 && s.open[id].effects[0].Write? then
            Result(AtNode(s.open - {id}, s.armed, s.next, s.owner, s.ids), [], Keep)
          else
            Result(s, [], Keep)
        case Request(_, Res(rpc, TimeoutDropped(id, clock))) =>
          if Live(s, id, rpc) && Head(s, id, Effect.Drop(clock)) then
            Reschedule(s, id)
          else
            Result(s, [], Keep)
        case _ =>
          Result(s, [], Keep)
      }
    else
      Result(s, [], Keep)
  }

  // Promise get reads the projection and does not write it back.
  function HandlePromiseGet(doc: Temp.Doc, id: string, now: nat): (r: Temp.Applied)
    ensures Temp.WellFormed(doc, now) ==> Temp.WellFormed(r.doc, now)
    ensures Temp.CaughtUp(doc, now) ==> Temp.CaughtUp(r.doc, now)
  {
    var shown := Temp.Opened(doc);
    assert Temp.WellFormed(doc, now) ==> Temp.WellFormed(shown, now) by {
      if Temp.WellFormed(doc, now) { Temp.OpenOk(doc, now); }
    }
    var objects := Temp.ObjectsOf(shown);
    if id !in objects then Temp.Applied(shown, Temp.Answer(404, Temp.None), [])
    else Temp.Applied(shown, Temp.Answer(200, Temp.Some(Temp.Project(objects[id], now).promise)), [])
  }

  // Promise create sweeps, then creates. A timer that is also targeted is refused.
  // An id already present is answered from the projection and not written back.
  function HandlePromiseCreate(doc: Temp.Doc, req: Temp.CreateReq, now: nat): (r: Temp.Applied)
    ensures Temp.WellFormed(doc, now) ==> Temp.WellFormed(r.doc, now)
    ensures Temp.CaughtUp(r.doc, now)
  {
    var swept := Temp.Sweep(doc, now, Retry);
    assert Temp.WellFormed(doc, now) ==> Temp.WellFormed(swept.doc, now);
    var objects := Temp.ObjectsOf(swept.doc);
    if Temp.Timer(req.tags) && Temp.Targeted(req.tags) then
      Temp.Applied(swept.doc, Temp.Answer(400, Temp.None), swept.notes)
    else if req.id in objects then
      var seen := Temp.Project(objects[req.id], now);
      Temp.Applied(swept.doc, Temp.Answer(200, Temp.Some(seen.promise)), swept.notes)
    else
      var obj := Temp.NewObj(req.timeoutAt, now, req.param, req.tags, Temp.Targeted(req.tags));
      var doc' := Temp.Origin(now, objects[req.id := obj]);
      assert Temp.WellFormed(swept.doc, now) ==> Temp.WellFormed(doc', now) by {
        if Temp.WellFormed(swept.doc, now) { Temp.InsertOk(swept.doc, req.id, obj, now); }
      }
      Temp.Applied(doc', Temp.Answer(200, Temp.Some(obj.promise)), swept.notes)
  }

  function Prepare(s: State, job: Job, id: string, doc: Temp.Doc, version: nat, now: nat): Plan
    requires s.AtNode?
  {
    match job
    case AskGet => Plan(HandlePromiseGet(doc, id, now).answer, false, [], Temp.None, false, s.next)
    case AskCreate(req) =>
      var applied := HandlePromiseCreate(doc, req, now);
      if applied.doc == doc then Plan(applied.answer, true, [], Temp.None, false, s.next)
      else
        var key := DocKey(req.id);
        var prev := if key in s.armed then Temp.Some(s.armed[key]) else Temp.None;
        match Temp.Nearest(applied.doc)
        case None =>
          var drop := match prev case None => [] case Some(t) => [Effect.Drop(t)];
          Plan(applied.answer, true, [Write(key, applied.doc, version, Temp.None)] + drop, Temp.None, true, s.next)
        case Some(d) =>
          var put := Due(key, d, s.owner, s.next);
          var drop := match prev case None => [] case Some(t) => if t == put then [] else [Effect.Drop(t)];
          Plan(applied.answer, true,
               [Put(put), Write(key, applied.doc, version, Temp.Some(put))] + drop,
               Temp.Some(put), true, s.next + 1)
  }

  function Reply(created: bool, answer: Temp.Answer): ResBody {
    if created then Created(answer) else PromiseReply(answer)
  }

  function SendEffect(id: string, effect: Effect): ReqBody {
    match effect
    case Put(clock) => PutTimeout(id, clock)
    case Write(key, doc, version, cover) => WriteDoc(id, key, doc, version, cover)
    case Drop(clock) => DropTimeout(id, clock)
  }

  // The armed map after a write effect lands.
  function Remember(armed: map<string, Clock>, effect: Effect, keep: Temp.Opt<Clock>, remember: bool): map<string, Clock> {
    if remember && effect.Write? then
      match keep
      case None => armed - {effect.key}
      case Some(clock) => armed[clock.key := clock]
    else armed
  }

  // An empty effect list answers the caller. Otherwise the head goes to the
  // store and Process stays scheduled on the whole list.
  function Process(s: State, id: string, caller: Pid, cid: Uuid, plan: Plan): Result<Pid, Msg, State>
    requires s.AtNode?
  {
    if plan.effects == [] then
      Result(AtNode(s.open - {id}, s.armed, plan.next, s.owner, s.ids),
             [ResTo(caller, cid, Reply(plan.created, plan.reply))], Keep)
    else
      var drawn := Draw(s.ids);
      var phase := Cont.Process(caller, plan.reply, plan.effects, plan.keep, plan.remember, cid, drawn.id);
      Result(AtNode(s.open[id := phase], s.armed, plan.next, s.owner, drawn.supply),
             [ReqTo(Bucket, drawn.id, SendEffect(id, plan.effects[0]))], Keep)
  }

  // The head effect landed. Remember a write, then schedule Process on what remains.
  function Reschedule(s: State, id: string): Result<Pid, Msg, State>
    requires s.AtNode? && id in s.open && s.open[id].Process? && |s.open[id].effects| > 0
  {
    var phase := s.open[id];
    var head := phase.effects[0];
    var armed := Remember(s.armed, head, phase.keep, phase.remember);
    var plan := Plan(phase.reply, true, phase.effects[1..], phase.keep, phase.remember && !head.Write?, s.next);
    Process(AtNode(s.open, armed, s.next, s.owner, s.ids), id, phase.caller, phase.cid, plan)
  }

  predicate Live(s: State, id: string, rpc: Uuid)
    requires s.AtNode?
  {
    id in s.open && s.open[id].rpc == rpc
  }

  predicate Head(s: State, id: string, effect: Effect)
    requires s.AtNode?
  {
    && id in s.open && s.open[id].Process? && |s.open[id].effects| > 0 && s.open[id].effects[0] == effect
  }


}
