import «concrete».Model

/-! Executable protocol tests for cache and conditional-write behavior. -/

namespace Resonate.Concrete.Tests

open Rover

def id : ServerModel.Ident := { origin := "test", suffix := "p" }

def getCall : Call := {
  client := "client"
  id := 1
  requestedAt := 4
  request := .promiseGet { id }
}

def key : DocumentKey := .origin "test"

def cachedNode : Node :=
  ({} : Node).cachePut key { document := [], version := 7 }

-- A miss performs GET and retains the request continuation locally.
#guard match start {} {} (.external getCall) key with
  | { send := [(.store, .storeRequest {
        payload := .get (.origin "test"), .. })], .. } => true
  | _ => false

-- A hit is never authoritative: it skips GET but always emits a raw
-- conditional PUT, even though the read-only decision leaves the row unchanged.
#guard match start {} cachedNode (.external getCall) key with
  | { send := [(.store, .storeRequest {
        payload := .put (.origin "test") [] (some 7), .. })], .. } => true
  | _ => false

def staleFlight : Flight := {
  key
  transaction := .external getCall
  loaded := some ([], 7)
  document := some []
  phase := .writing
}

def staleNode : Node :=
  { cachedNode with flights := [(3, staleFlight)] }

def conflictResult : Result Pid Local Msg :=
  (step {} { retries := 2 } (.node "test") (.node staleNode) 5
    (.receive .store (.storeReply { op := 3, payload := .conflict }))).val
      |>.headD { state := .node {}, send := [] }

-- A stale hit conflict invalidates the cache and retries from GET.
#guard match conflictResult with
  | { state := .node node
      send := [(.store, .storeRequest {
        payload := .get (.origin "test"), .. })] } =>
      (node.cacheRead key).isNone
  | _ => false

-- Invalidation is key-local.
#guard ((cachedNode.cacheInvalidate key).cacheRead key).isNone

-- Flaky PUT models written, landed-failed, and fenced not-landed failure.
#guard (storePut { flaky := true } (.node "test") {} 9 key [] none).val.length == 3

-- A duplicate conditional absent-version PUT cannot land twice.
def once : Store := ({} : Store).commit key []

#guard match (storePut { conditional := true } (.node "test") once
    10 key [] none).val with
  | [{ state := .store store
       send := [(.node "test", .storeReply { payload := .conflict, .. })] }] =>
      store.version key == some 1
  | _ => false

end Resonate.Concrete.Tests
