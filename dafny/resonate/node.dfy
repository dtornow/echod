include "s3.dfy"

// The node, as a process. It receives a message and sends messages. Its
// local state is who it is waiting on.
//
// A promise get is two steps. The ask is remembered, and a get for that
// promise's origin document goes to the bucket. The bucket's reply is the
// answer, sent back to the caller. A second get while one is outstanding
// waits; the node does not forget the first caller.

module Node {
  import opened Network
  import S3

  datatype Pid = Node | Bucket | Client(name: string)

  datatype Msg =
    | PromiseGet(id: string)
    | PromiseReply(out: S3.Outcome)
    | Store(m: S3.Msg)

  datatype State = Idle | Getting(caller: Pid, id: string)

  const Pids: set<Pid> := {Node}

  // Everything before the first `:`, or the whole string when there is none.
  function OriginOf(s: string): string
    decreases |s|
  {
    if |s| == 0 then ""
    else if s[0] == ':' then ""
    else [s[0]] + OriginOf(s[1..])
  }

  // The origin document. A deployment prefix is not part of this key.
  function DocKey(id: string): string { "wf/" + OriginOf(id) }

  function Init(self: Pid): State { Idle }

  function Step(self: Pid, s: State, i: Input<Pid, Msg>): Result<Pid, Msg, State> {
    if self != Node then Result(s, [], Keep)
    else
      match i
      case Timeout => Result(s, [], Cancel)
      case Request(from, PromiseGet(id)) =>
        (match s
         case Idle =>
           Result(Getting(from, id), [Send(Bucket, Store(S3.Ask(S3.Get(DocKey(id)))))], Keep)
         case Getting(_, _) => Result(s, [], Keep))
      case Request(from, Store(m)) =>
        if m.Reply? && from == Bucket && s.Getting? then
          Result(Idle, [Send(s.caller, PromiseReply(m.out))], Keep)
        else Result(s, [], Keep)
      case Request(_, PromiseReply(_)) => Result(s, [], Keep)
  }

  function World(): Sys<Pid, Msg, State> { Sys(Pids, true, Init, Step) }

  lemma GetAsks(from: Pid, id: string)
    ensures var r := Step(Node, Idle, Request(from, PromiseGet(id)));
      && r.state == Getting(from, id)
      && r.sends == [Send(Bucket, Store(S3.Ask(S3.Get(DocKey(id)))))]
      && r.timer == Keep
  {
  }

  lemma GetReplies(caller: Pid, id: string, out: S3.Outcome)
    ensures var r := Step(Node, Getting(caller, id), Request(Bucket, Store(S3.Reply(out))));
      && r.state == Idle
      && r.sends == [Send(caller, PromiseReply(out))]
      && r.timer == Keep
  {
  }

  lemma GetWaits(caller: Pid, held: string, from: Pid, id: string)
    ensures Step(Node, Getting(caller, held), Request(from, PromiseGet(id))).state == Getting(caller, held)
    ensures Step(Node, Getting(caller, held), Request(from, PromiseGet(id))).sends == []
  {
  }
}
