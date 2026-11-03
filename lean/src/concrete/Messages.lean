import «concrete».Document

/-!
# Concrete wire vocabulary

The process identities and the request and reply payloads that nodes and the
store exchange, together with the timer and membership values those payloads
carry. Timer keys are durable empty objects: their identity includes the
deadline, target, arm token, and arming node.
-/

namespace Resonate.Concrete

open Rover

abbrev TimerToken := Nat

inductive TimerTarget where
  | origin (origin : String)
  | schedule (id : ServerModel.Ident)
  deriving Repr, BEq, ReflBEq, LawfulBEq, DecidableEq

def TimerTarget.key : TimerTarget → DocumentKey
  | TimerTarget.origin name => DocumentKey.origin name
  | TimerTarget.schedule ident => DocumentKey.schedule ident

/-- The stable value on which membership ownership is partitioned. -/
def TimerTarget.partitionKey : TimerTarget → String
  | TimerTarget.origin name => name
  | TimerTarget.schedule ident => ident.origin ++ ":" ++ ident.suffix

/-- A durable empty object under `t/<bucket>/...` in echod. -/
structure TimerKey where
  deadline : Time
  target : TimerTarget
  token : TimerToken
  armedBy : Addr
  deriving Repr, BEq, ReflBEq, LawfulBEq, DecidableEq

def TimerTarget.ofDocumentKey : DocumentKey → TimerTarget
  | .origin name => .origin name
  | .schedule ident => .schedule ident

structure Announcement where
  id : Addr
  announcedAt : Time
  deriving Repr, BEq, DecidableEq

structure MembershipConfig where
  members : List Addr := []
  deriving Repr, DecidableEq

abbrev Version := Nat
abbrev OpId := Nat

structure Config where
  flaky : Bool := false
  retries : Nat := 3
  bucketWidth : Time := 1000
  loadAhead : Time := 2000
  heartbeat : Time := 1000
  nodeTtl : Time := 5000

inductive Pid where
  | outside
  | node (address : Addr)
  | store
  deriving DecidableEq, Repr

/-- Application payload of a store request. Correlation is deliberately not
part of this type. -/
inductive StoreRequest where
  | get (key : DocumentKey)
  | put (key : DocumentKey) (document : Document key)
      (expectedVersion : Option Version)
  | armTimer (key : TimerKey)
  | deleteTimers (keys : List TimerKey)
  | listTimers (through : Time)
  | announce (announcement : Announcement)
  | listAnnouncements
  | getMembership
  | putMembership (expectedVersion : Version) (next : MembershipConfig)

/-- Application payload of a store reply. The key on `got` is the dependent
index needed to type the returned document; correlation remains external. -/
inductive StoreReply where
  | got (key : DocumentKey)
      (document : Option (Document key × Version))
  | written
  | conflict
  /-- The write may have landed. -/
  | failed
  | done
  | timers (keys : List TimerKey)
  | announcements (values : List Announcement)
  | membership (configuration : MembershipConfig) (version : Version)

structure RpcRequest where
  op : OpId
  payload : StoreRequest

structure RpcReply where
  op : OpId
  payload : StoreReply

inductive Msg where
  | request (call : Call)
  | output (output : Output)
  | storeRequest (rpc : RpcRequest)
  | storeReply (rpc : RpcReply)

structure Versioned (key : DocumentKey) where
  document : Document key
  version : Version

end Resonate.Concrete
