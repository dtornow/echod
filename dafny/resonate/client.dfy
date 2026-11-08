include "protocol.dfy"

// A client asks one Resonate server, once. A read sends a promise get.
// A create sends a promise create. After that it waits.

module Client {
  import opened Network
  import opened Protocol
  import Temp

  function step(self: Pid, s: State, i: Input<Pid, Msg>, now: nat): Result<Pid, Msg, State>
  {
    if self.Client? && s.AtClient? && s.waiting && i.Timeout? then
      var body :=
        match s.kind
        case Read => PromiseGet(s.id)
        case Create(timeout) => PromiseCreate(Temp.CreateReq(s.id, timeout, Temp.Empty(), []));
      Result(AtClient(s.id, s.node, s.kind, false), [ReqTo(Node(s.node), 0, body)], Keep)
    else Result(s, [], Keep)
  }
}
