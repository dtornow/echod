include "protocol.dfy"

// A client is a process. A request it makes is a message, the same shape as
// any other request. This step sends nothing.

module Client {
  import opened Network
  import opened Protocol

  function step(self: Pid, s: State, i: Input<Pid, Msg>, now: nat): Result<Pid, Msg, State>
  {
    Result(s, [], Keep)
  }
}
