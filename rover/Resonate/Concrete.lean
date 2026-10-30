import Rover.World
import Experiment.Storage

/-!
# Narrow promise-slice concrete store

This module deliberately does not claim to implement the full fused Resonate
machine. It preserves the faithful raw conditional PUT model used by the old
four-operation promise slice, under an explicit namespace.
-/

namespace Resonate.PromiseSlice.Concrete

open Rover

abbrev Key := Experiment.Ident
abbrev Promise := Experiment.Promise
abbrev Version := Experiment.Storage.Version
abbrev Store := Experiment.Storage.Store

inductive StoreRequest where
  | get (key : Key)
  | put (key : Key) (document : Promise)
      (expectedVersion : Option Version)
  deriving DecidableEq, Repr

inductive StoreReply where
  | got (document : Option (Promise × Version))
  | written
  | conflict
  /-- A failed write may have landed. -/
  | failed
  deriving DecidableEq, Repr

structure Config where
  conditional : Bool := true
  flaky : Bool := false

def Store.document (store : Store) (key : Key) :
    Option (Promise × Version) :=
  store.docs.find? (·.1 == key) |>.map fun (_, promise, version) =>
    (promise, version)

def Store.version (store : Store) (key : Key) : Option Version :=
  (store.document key).map (·.2)

def Store.commit (store : Store) (key : Key) (document : Promise) : Store :=
  let version := (store.version key).getD 0 + 1
  { docs := (key, document, version) ::
      store.docs.filter (·.1 != key) }

structure PutResult where
  store : Store
  reply : StoreReply

/-- Exact conditional-write outcomes: conflict; acknowledged land; or, for a
flaky store, failed-after-land and failed-without-landing. -/
def put (config : Config) (store : Store) (key : Key)
    (document : Promise) (expectedVersion : Option Version) :
    Outcomes PutResult :=
  if config.conditional && expectedVersion != store.version key then
    Outcomes.one { store, reply := .conflict }
  else
    let committed := store.commit key document
    if config.flaky then
      ⟨[
        { store := committed, reply := .written },
        { store := committed, reply := .failed },
        { store, reply := .failed }
      ], by simp⟩
    else
      Outcomes.one { store := committed, reply := .written }

end Resonate.PromiseSlice.Concrete
