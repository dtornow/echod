import Rover
import «concrete».Messages

/-!
# The store process

One object store holding independently versioned documents, durable timer
keys, and the membership objects. It answers each request on its own: a GET
reads, a PUT is conditional on the expected version, a timer request arms,
deletes, or lists keys, and a membership write is conditional on its version.
`storeStep` is parametric in how the caller wraps the store state.
-/

namespace Resonate.Concrete

open Rover

/-- The timer-key part of the object store. -/
structure TimerObjects where
  keys : List TimerKey := []
  deriving Repr

def TimerObjects.arm (objects : TimerObjects) (key : TimerKey) : TimerObjects :=
  if objects.keys.contains key then objects
  else { keys := objects.keys ++ [key] }

/-- Exact-key deletion: the arm token and arming node are part of identity. -/
def TimerObjects.delete (objects : TimerObjects) (key : TimerKey) :
    TimerObjects :=
  { keys := objects.keys.filter (· != key) }

def TimerObjects.listThrough (objects : TimerObjects) (through : Time) :
    List TimerKey :=
  objects.keys.filter (·.deadline ≤ through)

/-- Store objects used for indirect node coordination. -/
structure MembershipObjects where
  announcements : List Announcement := []
  configuration : MembershipConfig := {}
  version : Nat := 0
  deriving Repr

def MembershipObjects.announce
    (objects : MembershipObjects) (announcement : Announcement) :
    MembershipObjects :=
  { objects with
    announcements :=
      announcement ::
        objects.announcements.filter (·.id != announcement.id) }

/-- Conditional write of the shared membership object. -/
def MembershipObjects.putConfig
    (objects : MembershipObjects) (expected : Nat)
    (next : MembershipConfig) : Option MembershipObjects :=
  if expected = objects.version then
    some {
      objects with
      configuration := next
      version := objects.version + 1
    }
  else
    none

/-- The physical store has one optional, independently versioned value for
each dependent document key. `keys` is only the finite discovery index. -/
structure Store where
  keys : List DocumentKey := []
  values : (key : DocumentKey) → Option (Versioned key) := fun _ => none
  timers : TimerObjects := {}
  membership : MembershipObjects := {}

def Store.read (store : Store) (key : DocumentKey) :
    Option (Document key × Version) :=
  (store.values key).map fun value => (value.document, value.version)

def Store.version (store : Store) (key : DocumentKey) : Option Version :=
  (store.values key).map (·.version)

theorem Store.version_eq_read (store : Store) (key : DocumentKey) :
    store.version key = (store.read key).map (·.2) := by
  unfold Store.version Store.read
  cases store.values key <;> rfl

def Store.commit (store : Store) (key : DocumentKey)
    (document : Document key) : Store :=
  let version := (store.version key).getD 0 + 1
  { store with
    keys :=
      if store.keys.contains key then store.keys else store.keys ++ [key]
    values := fun other =>
      if h : other = key then
        some {
          document := h ▸ document
          version
        }
      else
        store.values other }

@[simp] theorem Store.read_commit_same (store : Store) (key : DocumentKey)
    (document : Document key) :
    (store.commit key document).read key =
      some (document, (store.version key).getD 0 + 1) := by
  simp [Store.commit, Store.read]

@[simp] theorem Store.read_commit_other (store : Store)
    (key other : DocumentKey) (document : Document key)
    (h : other ≠ key) :
    (store.commit key document).read other = store.read other := by
  simp [Store.commit, Store.read, h]

/-- A value outside `keys` is not part of the finite store. Reachable stores
satisfy this because every commit records the key it writes. -/
def Store.indexed (store : Store) : Prop :=
  ∀ key, store.values key ≠ none → key ∈ store.keys

theorem Store.indexed_empty : Store.indexed {} := by
  intro key hvalue
  simp at hvalue

theorem Store.indexed_commit (store : Store) (key : DocumentKey)
    (document : Document key) (hindexed : store.indexed) :
    (store.commit key document).indexed := by
  intro query hvalue
  by_cases hquery : query = key
  · subst hquery
    by_cases hk : query ∈ store.keys <;>
      simp [Store.commit, hk, List.mem_append]
  · have hprevious : store.values query ≠ none := by
      simpa [Store.commit, hquery] using hvalue
    have hmem := hindexed query hprevious
    by_cases hk : key ∈ store.keys <;>
      simp [Store.commit, hk, hquery, hmem, List.mem_append]

theorem Store.indexed_congr {left right : Store}
    (hvalues : left.values = right.values) (hkeys : left.keys = right.keys)
    (hindexed : right.indexed) : left.indexed := by
  intro key hvalue
  have hright : right.values key ≠ none := by
    simpa [hvalues] using hvalue
  simpa [hkeys] using hindexed key hright

def Store.documentAt (store : Store) (key : DocumentKey) : Document key :=
  match store.values key with
  | some value => value.document
  | none => emptyDocument key

/-- Consume a successful conditional attempt without installing its candidate
payload. This is the not-landed failure fence: the logical document is
unchanged, but replaying the same expected version can no longer land later
after its node-local continuation has been discarded. -/
def Store.fence (store : Store) (key : DocumentKey) : Store :=
  store.commit key (store.documentAt key)

def storePut {S : Type} (wrap : Store → S) (config : Config) (sender : Pid) (store : Store)
    (op : OpId) (key : DocumentKey) (document : Document key)
    (expectedVersion : Option Version) :
    Outcomes (Result Pid S Msg) :=
  if expectedVersion != store.version key then
    Outcomes.one {
      state := wrap store
      send := [(sender, .storeReply { op, payload := .conflict })]
    }
  else
    let committed := store.commit key document
    if config.flaky then
      ⟨[
        { state := wrap committed
          send := [(sender, .storeReply { op, payload := .written })] },
        { state := wrap committed
          send := [(sender, .storeReply { op, payload := .failed })] },
        { state := wrap (store.fence key)
          send := [(sender, .storeReply { op, payload := .failed })] }
      ], by simp⟩
    else
      Outcomes.one {
        state := wrap committed
        send := [(sender, .storeReply { op, payload := .written })]
      }

def storeStep {S : Type} (wrap : Store → S) (config : Config) (store : Store)
    (event : Event Pid Msg) : Outcomes (Result Pid S Msg) :=
  match event with
  | .receive sender (.storeRequest { op, payload := .get key }) =>
      Outcomes.one {
        state := wrap store
        send := [(sender, .storeReply {
          op, payload := .got key (store.read key) })]
      }
  | .receive sender (.storeRequest { op, payload := .armTimer timer }) =>
      Outcomes.one {
        state := wrap { store with timers := store.timers.arm timer }
        send := [(sender, .storeReply { op, payload := .done })]
      }
  | .receive sender (.storeRequest { op, payload := .deleteTimer timer }) =>
      Outcomes.one {
        state := wrap { store with timers := store.timers.delete timer }
        send := [(sender, .storeReply { op, payload := .done })]
      }
  | .receive sender (.storeRequest { op, payload := .deleteTimers timers }) =>
      Outcomes.one {
        state := wrap {
          store with
          timers := timers.foldl TimerObjects.delete store.timers }
        send := [(sender, .storeReply { op, payload := .done })]
      }
  | .receive sender (.storeRequest { op, payload := .listTimers through }) =>
      Outcomes.one {
        state := wrap store
        send := [(sender, .storeReply {
          op, payload := .timers (store.timers.listThrough through) })]
      }
  | .receive sender (.storeRequest { op, payload := .announce announcement }) =>
      Outcomes.one {
        state := wrap {
          store with
          membership := store.membership.announce announcement }
        send := [(sender, .storeReply { op, payload := .done })]
      }
  | .receive sender (.storeRequest { op, payload := .listAnnouncements }) =>
      Outcomes.one {
        state := wrap store
        send := [(sender, .storeReply {
          op, payload := .announcements store.membership.announcements })]
      }
  | .receive sender (.storeRequest { op, payload := .getMembership }) =>
      Outcomes.one {
        state := wrap store
        send := [(sender, .storeReply {
          op
          payload := .membership store.membership.configuration
            store.membership.version })]
      }
  | .receive sender
        (.storeRequest { op, payload := .putMembership expected next }) =>
      match store.membership.putConfig expected next with
      | some membership =>
          Outcomes.one {
            state := wrap { store with membership }
            send := [(sender, .storeReply { op, payload := .done })]
          }
      | none =>
          Outcomes.one {
            state := wrap store
            send := [(sender, .storeReply { op, payload := .conflict })]
          }
  | .receive sender
        (.storeRequest { op, payload := .put key document expected }) =>
      storePut wrap config sender store op key document expected
  | _ => Outcomes.one { state := wrap store, send := [] }

end Resonate.Concrete
