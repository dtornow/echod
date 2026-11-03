import «concrete».Document

/-!
# Echod-style durable timers and membership

This file models the concrete coordination data stored beside documents in
the object store.  Nodes never exchange ownership messages.  They publish
announcements, converge on one conditionally-versioned membership object, and
derive ownership from that shared ordered membership.

Timer keys are durable empty objects.  Their identity includes the deadline,
target, arm token, and arming node.  A timer wheel is only a local index of
those keys; deleting a wheel entry cannot delete the durable key.
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

/-- The one timer key a node associates with a document version.  It is a
cache hint for predecessor cleanup, never the source of timer safety. -/
structure ArmedEntry where
  target : DocumentKey
  timer : TimerKey
  version : Nat
  deriving Repr

/-- Start of the time bucket containing `instant`. -/
def bucketOf (bucketWidth instant : Time) : Time :=
  let width := max bucketWidth 1
  instant / width * width

def TimerTarget.ofDocumentKey : DocumentKey → TimerTarget
  | .origin name => .origin name
  | .schedule ident => .schedule ident

def minimumTime? : List Time → Option Time
  | [] => none
  | first :: rest => some (rest.foldl min first)

def OriginObject.deadlines {origin : String}
    (object : OriginObject origin) (now : Time) : List Time :=
  let promise :=
    if object.promise.state == .pending then
      [object.promise.timeoutAt]
    else if !object.promise.callbacks.isEmpty ||
        !object.promise.listeners.isEmpty then
      [now]
    else
      []
  let task :=
    match object.task with
    | none => []
    | some task =>
        (if task.state == .acquired then task.leaseTimeoutAt.toList else []) ++
        (if task.state == .pending then task.retryTimeoutAt.toList else [])
  promise ++ task

def documentDeadline?
    (key : DocumentKey) (document : Document key) (now : Time) :
    Option Time :=
  match key with
  | .origin _ =>
      minimumTime?
        (document.flatMap fun object => OriginObject.deadlines object now)
  | .schedule _ =>
      document.map (·.nextRunAt)

def timerForDocument
    (key : DocumentKey) (document : Document key) (now : Time)
    (token : TimerToken) (armedBy : Addr) : Option TimerKey :=
  (documentDeadline? key document now).map fun deadline =>
    { deadline
      target := TimerTarget.ofDocumentKey key
      token
      armedBy }

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

structure Announcement where
  id : Addr
  announcedAt : Time
  deriving Repr, BEq, DecidableEq

structure MembershipConfig where
  members : List Addr := []
  deriving Repr, DecidableEq

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

/-- FNV-1a over UTF-8, matching echod's stable ownership hash. -/
def fnv1a (value : String) : UInt64 :=
  value.toUTF8.foldl
    (fun hash byte => (hash ^^^ byte.toUInt64) * 0x00000100000001b3)
    0xcbf29ce484222325

def owner? (members : List Addr) (target : TimerTarget) : Option Addr :=
  if h : members.length = 0 then
    none
  else
    members[(fnv1a target.partitionKey).toNat.mod members.length]?

structure MembershipView where
  members : List Addr := []
  version : Nat := 0
  lastRead : Time := 0
  readAny : Bool := false
  deriving Repr

def MembershipView.fresh
    (view : MembershipView) (now ttl : Time) : Bool :=
  view.readAny && now ≤ view.lastRead + ttl

def MembershipView.owns
    (view : MembershipView) (me : Addr) (now ttl : Time)
    (target : TimerTarget) : Bool :=
  view.fresh now ttl && owner? view.members target == some me

/-- Node-local index of durable keys.  `loadedThrough` is the look-ahead
horizon; `closedThrough` records the last bucket that received its mandatory
second listing, which closes the gap that can occur while another node arms a
key in a bucket already loaded by this node. -/
structure TimerWheel where
  entries : List TimerKey := []
  loadedThrough : Time := 0
  closedThrough : Time := 0
  backlog : List TimerKey := []
  deriving Repr

def TimerWheel.insert (wheel : TimerWheel) (key : TimerKey) : TimerWheel :=
  if wheel.entries.contains key then wheel
  else { wheel with entries := wheel.entries ++ [key] }

def TimerWheel.load
    (wheel : TimerWheel) (view : MembershipView) (me : Addr)
    (now ttl through : Time) (keys : List TimerKey) : TimerWheel :=
  let owned :=
    keys.filter fun key =>
      key.deadline ≤ through && view.owns me now ttl key.target
  { wheel with
    entries := (owned.foldl TimerWheel.insert wheel).entries
    loadedThrough := max wheel.loadedThrough through }

def TimerWheel.due (wheel : TimerWheel) (now : Time) : List TimerKey :=
  wheel.entries.filter (·.deadline ≤ now)

def TimerWheel.takeDue (wheel : TimerWheel) (now limit : Time) : TimerWheel :=
  let due := (wheel.due now).take limit
  { wheel with
    entries := wheel.entries.filter fun key => !(due.contains key)
    backlog := wheel.backlog ++ due }

def TimerWheel.beginOne (wheel : TimerWheel) : Option (TimerKey × TimerWheel) :=
  match wheel.backlog with
  | [] => none
  | key :: rest => some (key, { wheel with backlog := rest })

end Resonate.Concrete
