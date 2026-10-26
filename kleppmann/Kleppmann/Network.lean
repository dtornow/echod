/-!
# The world, in Kleppmann's terms

After Martin Kleppmann, "Verifying distributed systems with Isabelle/HOL"
(2022): processes, each with a local state and one step function; a step is
one event at one process; the network is the set of every message ever
sent. Nothing else is assumed: a message may be delayed, reordered,
duplicated or never delivered, and any process may step at any time.

His definitions, transcribed:

```isabelle
datatype ('proc, 'msg, 'val) event
  = Receive (msg_sender: 'proc) (recv_msg: 'msg) | Request 'val | Timeout

type_synonym ('proc, 'state, 'msg, 'val) step_func =
  ‹'proc ⇒ 'state ⇒ ('proc, 'msg, 'val) event ⇒ ('state × ('proc × 'msg) set)›

valid_event (Receive sender msg) recpt msgs = ((sender, recpt, msg) ∈ msgs)
valid_event (Request _) _ _ = True
valid_event Timeout _ _ = True
```

Two deviations, both because Resonate's handlers need them, and both
marked where they are made:

1. **Time.** Every step happens at an instant `now`, passed to the step
   function, and instants never decrease along an execution. His model has
   no clock; Resonate's handlers read one.
2. **Which timeout.** `Timeout` carries a value saying which timeout
   elapsed. His carries nothing, and a process works out what to do from
   its state; Resonate names its internal steps (`promiseTimeout id`,
   `taskLeaseTimeout id`, ...), and any of them may fire at any time, so
   the event names one. With `T := Unit` this is his `Timeout` again.

Sets are lists here (`msgs ++ sent` for his `msgs ∪ sent`): membership is
all the model asks of them, and a list has no decidability strings attached.
-/

namespace Kleppmann

abbrev Time := Nat

/-- What happens at a process in one step. `T` says which timeout. -/
inductive Event (P M V T : Type) where
  /-- A message from `sender` arrives. -/
  | receive (sender : P) (msg : M)
  /-- User input. -/
  | request (val : V)
  /-- A timeout elapses. -/
  | timeout (which : T)

/-- A process's step: its id, its state, the instant, the event; the new
    state, and the messages it sends, each to a recipient. -/
abbrev StepFunc (P S M V T : Type) := P → S → Time → Event P M V T → S × List (P × M)

/-- The one assumption about the network: a message received was sent, to
    this process, by its sender. Requests and timeouts may happen anytime. -/
def ValidEvent {P M V T : Type} : Event P M V T → P → List (P × P × M) → Prop
  | .receive sender msg, recpt, msgs => (sender, recpt, msg) ∈ msgs
  | .request _, _, _ => True
  | .timeout _, _, _ => True

/-- The executions of the system: `events` is a valid sequence of steps;
    `msgs`, every message sent so far, as (sender, recipient, message);
    `states`, each process's state; `clock`, the instant of the last step. -/
inductive Execute {P S M V T : Type} [DecidableEq P]
    (step : StepFunc P S M V T) (init : P → S) (procs : P → Prop) :
    List (P × Time × Event P M V T) → List (P × P × M) → (P → S) → Time → Prop where
  | nil : Execute step init procs [] [] init 0
  | step {events msgs states clock proc now event new sent} :
      Execute step init procs events msgs states clock →
      procs proc →
      clock ≤ now →                                      -- deviation 1: time moves forward
      ValidEvent event proc msgs →
      step proc (states proc) now event = (new, sent) →
      Execute step init procs (events ++ [(proc, now, event)])
        (msgs ++ sent.map fun (recpt, msg) => (proc, recpt, msg))
        (fun p => if p = proc then new else states p)
        now

/-! ## The proof method: an invariant, by induction over the execution -/

/-- A property of the network and the states that holds initially and that
    every step preserves holds in every execution. His `List.rev_induct`
    argument, once and for all. -/
theorem Execute.invariant {P S M V T : Type} [DecidableEq P]
    {step : StepFunc P S M V T} {init : P → S} {procs : P → Prop}
    (inv : List (P × P × M) → (P → S) → Prop)
    (h₀ : inv [] init)
    (h₁ : ∀ msgs states clock proc now event new sent,
      inv msgs states → procs proc → clock ≤ now → ValidEvent event proc msgs →
      step proc (states proc) now event = (new, sent) →
      inv (msgs ++ sent.map fun (recpt, msg) => (proc, recpt, msg))
          (fun p => if p = proc then new else states p))
    {events msgs states clock} (h : Execute step init procs events msgs states clock) :
    inv msgs states := by
  induction h with
  | nil => exact h₀
  | step _ hp hc hv hs ih => exact h₁ _ _ _ _ _ _ _ _ ih hp hc hv hs

end Kleppmann
