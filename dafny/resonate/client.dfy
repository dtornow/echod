include "protocol.dfy"

// A client asks one Resonate server, once. A read sends a promise get.
// A create sends a promise create. After that it waits.

module Client {
  import opened Network
  import opened Protocol
  import Temp

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
}
