include "../framework/framework.dfy"

// One process. Idle, or waiting to answer one caller.
// A promise get sends a get to the bucket. The bucket's reply is the answer.

module Node {
  import opened Network

  datatype Pid = Node | Bucket

  datatype Msg =
    | PromiseGet(id: string)
    | PromiseReply
    | Get(id: string)
    | Got

  datatype State = Idle | Getting(caller: Pid)

  function Init(self: Pid): State { Idle }

  function Step(self: Pid, s: State, i: Input<Pid, Msg>): Result<Pid, Msg, State>
    requires self == Node
  {
    match i
    case Timeout => Result(s, [], Keep)
    case Request(from, PromiseGet(id)) =>
      (match s
       case Idle => Result(Getting(from), [Send(Bucket, Get(id))], Keep)
       case Getting(_) => Result(s, [], Keep))
    case Request(_, Got) =>
      (match s
       case Getting(caller) => Result(Idle, [Send(caller, PromiseReply)], Keep)
       case Idle => Result(s, [], Keep))
    case Request(_, _) => Result(s, [], Keep)
  }

  lemma GetAsks(from: Pid, id: string)
    ensures var r := Step(Node, Idle, Request(from, PromiseGet(id)));
      && r.state == Getting(from)
      && r.sends == [Send(Bucket, Get(id))]
      && r.timer == Keep
  {
  }

  lemma GetReplies(caller: Pid)
    ensures var r := Step(Node, Getting(caller), Request(Bucket, Got));
      && r.state == Idle
      && r.sends == [Send(caller, PromiseReply)]
      && r.timer == Keep
  {
  }
}
