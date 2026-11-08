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
          var rpc := Hash(cid);
          if rpc in s.open then
            Result(s, [], Keep)
          else
            Result(AtNode(s.open[rpc := Cont.Prepare(from, id, AskGet, cid)], s.armed, s.next, s.owner),
                   [ReqTo(Bucket, rpc, Get(id))], Keep)
        case Request(from, Req(cid, PromiseCreate(req))) =>
          var rpc := Hash(cid);
          if rpc in s.open then
            Result(s, [], Keep)
          else
            Result(AtNode(s.open[rpc := Cont.Prepare(from, req.id, AskCreate(req), cid)], s.armed, s.next, s.owner),
                   [ReqTo(Bucket, rpc, Get(req.id))], Keep)
        case Request(_, Res(rpc, Got(id, doc, version))) =>
          if rpc in s.open && s.open[rpc].Prepare? && s.open[rpc].id == id then
            var plan := Prepare(s, s.open[rpc].job, id, doc, version, now);
            Process(s, rpc, plan)
          else
            Result(s, [], Keep)
        case Request(_, Res(rpc, TimeoutPut(id, clock))) =>
          if rpc in s.open && s.open[rpc].id == id && Head(s, rpc, Put(clock)) then
            Reschedule(s, rpc)
          else
            Result(s, [], Keep)
        case Request(_, Res(rpc, DocWrote(id, _))) =>
          if rpc in s.open && s.open[rpc].id == id && s.open[rpc].Process? && |s.open[rpc].effects| > 0 && s.open[rpc].effects[0].Write? then
            Reschedule(s, rpc)
          else
            Result(s, [], Keep)
        case Request(_, Res(rpc, DocRejected(id))) =>
          if rpc in s.open && s.open[rpc].id == id && s.open[rpc].Process? && |s.open[rpc].effects| > 0 && s.open[rpc].effects[0].Write? then
            Result(AtNode(s.open - {rpc}, s.armed, s.next, s.owner), [], Keep)
          else
            Result(s, [], Keep)
        case Request(_, Res(rpc, TimeoutDropped(id, clock))) =>
          if rpc in s.open && s.open[rpc].id == id && Head(s, rpc, Effect.Drop(clock)) then
            Reschedule(s, rpc)
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
    var done := Temp.Create(swept.doc, req, now);
    Temp.Applied(done.doc, done.answer, swept.notes + done.notes)
  }

  function Prepare(s: State, job: Job, id: string, doc: Temp.Doc, version: nat, now: nat): (plan: Plan)
    requires s.AtNode?
    ensures Temp.WellFormed(doc, now) ==>
      forall i | 0 <= i < |plan.effects| && plan.effects[i].Write? ::
        Temp.WellFormed(plan.effects[i].doc, now)
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

  // Any request. A well-formed document comes back well-formed in every write the plan schedules.
  lemma RequestKeepsWellFormed(s: State, job: Job, id: string, doc: Temp.Doc, version: nat, now: nat)
    requires s.AtNode?
    requires Temp.WellFormed(doc, now)
    ensures var plan := Prepare(s, job, id, doc, version, now);
      forall i | 0 <= i < |plan.effects| && plan.effects[i].Write? ::
        Temp.WellFormed(plan.effects[i].doc, now)
  {
  }

  // The same fact over `step`, for whichever request the continuation was preparing.
  // A write the step sends, and a write it stores on the new continuation, is one the plan scheduled.
  lemma StepKeepsWellFormed(self: Pid, s: State, i: Input<Pid, Msg>, now: nat)
    requires self.Node? ==> s.AtNode?
    requires i.Request? && IsGot(i.msg) ==> Temp.WellFormed(i.msg.ans.doc, now)
    ensures var r := step(self, s, i, now);
      i.Request? && IsGot(i.msg) && self.Node? && s.AtNode? &&
      i.msg.id in s.open && s.open[i.msg.id].Prepare? && s.open[i.msg.id].id == i.msg.ans.id ==>
        var plan := Prepare(s, s.open[i.msg.id].job, i.msg.ans.id, i.msg.ans.doc, i.msg.ans.version, now);
        && (forall j | 0 <= j < |r.sends| && r.sends[j].msg.Req? && r.sends[j].msg.ask.WriteDoc? ::
             Temp.WellFormed(r.sends[j].msg.ask.doc, now))
        && (|plan.effects| > 0 ==>
             var next := Hash(i.msg.id);
             && next in r.state.open && r.state.open[next].effects == plan.effects)
  {
    if i.Request? && IsGot(i.msg) && self.Node? && s.AtNode? &&
       i.msg.id in s.open && s.open[i.msg.id].Prepare? && s.open[i.msg.id].id == i.msg.ans.id {
      var job := s.open[i.msg.id].job;
      var id := i.msg.ans.id;
      var doc := i.msg.ans.doc;
      var version := i.msg.ans.version;
      var plan := Prepare(s, job, id, doc, version, now);
      RequestKeepsWellFormed(s, job, id, doc, version, now);
      var r := step(self, s, i, now);
      if |plan.effects| > 0 {
        var next := Hash(i.msg.id);
        assert r.sends == [ReqTo(Bucket, next, SendEffect(id, plan.effects[0]))];
        assert r.state.open[next].effects == plan.effects;
        if r.sends[0].msg.ask.WriteDoc? {
          assert plan.effects[0].Write? && r.sends[0].msg.ask.doc == plan.effects[0].doc;
        }
      }
    }
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

  // An empty effect list answers the caller and drops the registration.
  // Otherwise the next request is the hash of this one, and the continuation
  // moves to that id. The response will cite it.
  function Process(s: State, rpc: Uuid, plan: Plan): Result<Pid, Msg, State>
    requires s.AtNode? && rpc in s.open
  {
    var c := s.open[rpc];
    if plan.effects == [] then
      Result(AtNode(s.open - {rpc}, s.armed, plan.next, s.owner),
             [ResTo(c.caller, c.cid, Reply(plan.created, plan.reply))], Keep)
    else
      var next := Hash(rpc);
      var phase := Cont.Process(c.caller, c.id, plan.reply, plan.effects, plan.keep, plan.remember, c.cid);
      Result(AtNode((s.open - {rpc})[next := phase], s.armed, plan.next, s.owner),
             [ReqTo(Bucket, next, SendEffect(c.id, plan.effects[0]))], Keep)
  }

  // The head effect landed. Remember a write, then schedule Process on what remains.
  function Reschedule(s: State, rpc: Uuid): Result<Pid, Msg, State>
    requires s.AtNode? && rpc in s.open && s.open[rpc].Process? && |s.open[rpc].effects| > 0
  {
    var phase := s.open[rpc];
    var head := phase.effects[0];
    var armed := Remember(s.armed, head, phase.keep, phase.remember);
    var plan := Plan(phase.reply, true, phase.effects[1..], phase.keep, phase.remember && !head.Write?, s.next);
    Process(AtNode(s.open, armed, s.next, s.owner), rpc, plan)
  }

  predicate Head(s: State, rpc: Uuid, effect: Effect)
    requires s.AtNode?
  {
    && rpc in s.open && s.open[rpc].Process? && |s.open[rpc].effects| > 0 && s.open[rpc].effects[0] == effect
  }


}
