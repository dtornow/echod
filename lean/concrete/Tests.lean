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

-- A conflict restores the in-flight write and does not decide again.
#guard match conflictResult with
  | { state := .node node, send := [] } =>
      match node.flights with
      | [(3, flight)] =>
          flight.phase == .writing && (node.cacheRead key).isSome
      | _ => false
  | _ => false

-- Invalidation is key-local.
#guard ((cachedNode.cacheInvalidate key).cacheRead key).isNone

-- Flaky PUT models written, landed-failed, and fenced not-landed failure.
#guard (storePut { flaky := true } (.node "test") {} 9 key [] none).val.length == 3

-- A duplicate conditional absent-version PUT cannot land twice.
def once : Store := ({} : Store).commit key []

#guard match (storePut {} (.node "test") once
    10 key [] none).val with
  | [{ state := .store store
       send := [(.node "test", .storeReply { payload := .conflict, .. })] }] =>
      store.version key == some 1
  | _ => false

def timer : TimerKey := {
  deadline := 12
  target := .origin "test"
  token := 7
  armedBy := "node-a"
}

def successorTimer : TimerKey := { timer with token := 8 }

#guard bucketOf 10 12 == 10
#guard timer.bucket 10 == 10
#guard timer ∈ (({} : TimerObjects).arm timer).keys

-- Exact identity includes the arm token: deleting a predecessor never
-- deletes a successor for the same target and deadline.
#guard successorTimer ∈
  (((( {} : TimerObjects).arm timer).arm successorTimer).delete timer).keys

def membershipStore : MembershipObjects :=
  { announcements := [
      { id := "node-a", url := "a", announcedAt := 20 },
      { id := "node-b", url := "b", announcedAt := 20 }
    ] }

#guard membershipStore.liveIds 20 5 == ["node-a", "node-b"]
#guard membershipStore.liveIds 30 5 == []

def configuredMembership : MembershipObjects :=
  (membershipStore.putConfig 0
    { epoch := 1, members := ["node-a", "node-b"] }).getD {}

#guard configuredMembership.configuration.epoch == 1
#guard (configuredMembership.putConfig 0
  { epoch := 2, members := ["node-a"] }).isNone

def view : MembershipView := {
  epoch := 1
  members := ["node-a", "node-b"]
  lastRead := 20
  readAny := true
}

-- Every fresh view selects exactly the same hash-mod-n owner.
#guard match owner? view.members timer.target with
  | some owner =>
      view.owns owner 20 5 timer.target &&
        !view.owns (if owner == "node-a" then "node-b" else "node-a")
          20 5 timer.target
  | none => false

-- Ownership expires with the membership view.
#guard !(view.owns "node-a" 30 5 timer.target)
#guard !(view.owns "node-b" 30 5 timer.target)

def createCall : Call := {
  client := "client"
  id := 2
  requestedAt := 4
  request := .promiseCreate {
    id
    timeoutAt := 12
    param := {}
    tags := []
  }
}

def createCachedNode : Node :=
  ({} : Node).cachePut key { document := [], version := 0 }

def armingResult : Result Pid Local Msg :=
  start {} createCachedNode (.external createCall) key "node-a"

-- The durable key is armed before the document PUT is submitted.
#guard match armingResult with
  | { state := .node node
      send := [(.store, .storeRequest {
        op
        payload := .armTimer armed
      })] } =>
      armed.deadline == 12 && armed.armedBy == "node-a" &&
        match node.flights.find? (·.1 == op) with
        | some (_, flight) => flight.phase == .arming
        | none => false
  | _ => false

def afterArmResult : Result Pid Local Msg :=
  match armingResult.state with
  | .node node =>
      (step {} {} (.node "node-a") (.node node) 4
        (.receive .store
          (.storeReply { op := 0, payload := .done }))).val.headD
        { state := .node {}, send := [] }
  | _ => { state := .node {}, send := [] }

#guard match afterArmResult with
  | { send := [(.store, .storeRequest {
        payload := .put (.origin "test") _ (some 0), ..
      })], .. } => true
  | _ => false

def predecessor : TimerKey := {
  deadline := 10
  target := .origin "test"
  token := 1
  armedBy := "node-a"
}

def replacement : TimerKey := { predecessor with deadline := 12, token := 2 }

def cleanupFlight : Flight := {
  key
  transaction := .external createCall
  loaded := some ([], 7)
  document := some []
  selected := [.response "client" 2 (.promiseCreate {
    status := 200
    promise := none
  })]
  phase := .writing
  address := "node-a"
  armed := some replacement
}

def cleanupNode : Node := {
  nextOp := 4
  flights := [(3, cleanupFlight)]
  armed := [{ target := key, timer := predecessor, version := 7 }]
}

def cleanupStarted : Result Pid Local Msg :=
  (step {} {} (.node "node-a") (.node cleanupNode) 5
    (.receive .store
      (.storeReply { op := 3, payload := .written }))).val.headD
    { state := .node {}, send := [] }

-- A predecessor key is deleted only after the document write, and outputs
-- stay withheld until cleanup completes.
#guard match cleanupStarted with
  | { state := .node node
      send := [(.store, .storeRequest {
        op := 4
        payload := .deleteTimers deleted
      })] } =>
      deleted == [predecessor] && node.armed.any (·.timer == replacement)
  | _ => false

def futureDocument : OriginDocument "test" := [{
  suffix := "p"
  promise := {
    state := .pending
    param := {}
    tags := []
    timeoutAt := 10
    createdAt := 0
  }
}]

def staleTimer : TimerKey := {
  deadline := 5
  target := .origin "test"
  token := 3
  armedBy := "node-a"
}

def futureCached : Node :=
  ({} : Node).cachePut key { document := futureDocument, version := 1 }

-- An idle stale fire still arms the current deadline and performs a
-- conditional document rewrite before deleting the fired key.
#guard match start {} futureCached (.sweep staleTimer 5 []) key
    "node-a" (some staleTimer) with
  | { send := [(.store, .storeRequest {
        payload := .armTimer armed
        ..
      })], .. } =>
      armed.deadline == 10
  | _ => false

-- A node starts membership through the shared store, not a peer message.
#guard match (step {} {} (.node "node-a") (.node {}) 0 .timeout).val with
  | [{ send := [(.store, .storeRequest {
        payload := .announce {
          id := "node-a"
          announcedAt := 0
          ..
        }
        ..
      })]
      ..
    }] => true
  | _ => false

end Resonate.Concrete.Tests
