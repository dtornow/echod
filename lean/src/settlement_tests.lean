import «abstract».External
import «concrete».External

namespace Resonate.SettlementTests

open ServerModel

def awaited : Ident := ⟨"wf", "awaited"⟩
def awaiter : Ident := ⟨"wf", "awaiter"⟩
def foreignAwaiter : Ident := ⟨"other", "awaiter"⟩

def pending : PromiseObject :=
  { state := .pending, param := {}, tags := [], timeoutAt := 1000, createdAt := 0 }

def initial (state : TaskState) (retry : Option Nat) : Store :=
  { objects := [
      { id := awaited, promise := { pending with
          callbacks := [awaiter, foreignAwaiter], listeners := ["listener"] } },
      { id := awaiter, promise := { pending with tags := [("resonate:target", "worker")] },
        task := some { state, version := 7, retryTimeoutAt := retry } },
      { id := foreignAwaiter, promise := pending,
        task := some { state := .suspended, version := 9 } }
    ] }

def request : PromiseSettleReq :=
  { id := awaited, state := .resolved, value := {} }

def abstractResult (state : TaskState) (retry : Option Nat) :=
  Abstract.promiseSettle request 10 { config := { retryTimeout := 100 } } (initial state retry)

def concreteResult (state : TaskState) (retry : Option Nat) :=
  let store := initial state retry
  let (response, document, messages) :=
    Concrete.Decision.promiseSettle request 10
      { config := { retryTimeout := 100 } } (store.read (.origin "wf"))
  (response, store.write (.origin "wf") document, messages)

def resumed (result : PromiseSettleRes × Store × List OutboxEntry) : Bool :=
  let (response, store, messages) := result
  response.status == 200 &&
  (store.getObject awaited).any (fun o =>
    o.promise.state == .resolved && o.promise.callbacks == [foreignAwaiter] &&
    o.promise.listeners.isEmpty) &&
  (store.getObject awaiter).any (fun o => o.task.any (fun t =>
    t.state == .pending && t.resumes == [awaited] && t.retryTimeoutAt == some 110)) &&
  (store.getObject foreignAwaiter).any (fun o => o.task.any (·.state == .suspended)) &&
  messages.map (·.address) == ["listener", "worker"] &&
  messages.any (fun entry => entry.message == .execute awaiter 7)

#guard resumed (abstractResult .suspended none)
#guard resumed (concreteResult .suspended none)

def alreadyDue (result : PromiseSettleRes × Store × List OutboxEntry) : Bool :=
  let (_, store, messages) := result
  messages.map (·.address) == ["listener"] &&
  (store.getObject awaiter).any (fun o => o.task.any (fun t =>
    t.resumes == [awaited] && t.retryTimeoutAt == some 5))

#guard alreadyDue (abstractResult .pending (some 5))
#guard alreadyDue (concreteResult .pending (some 5))

def repeatedAbstract :=
  let (_, store, _) := abstractResult .suspended none
  Abstract.promiseSettle request 10 { config := { retryTimeout := 100 } } store

def repeatedConcrete :=
  let (_, store, _) := concreteResult .suspended none
  Concrete.Decision.promiseSettle request 10
    { config := { retryTimeout := 100 } } (store.read (.origin "wf"))

#guard repeatedAbstract.2.2.isEmpty
#guard repeatedConcrete.2.2.isEmpty

end Resonate.SettlementTests
