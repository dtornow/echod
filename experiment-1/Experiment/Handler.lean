/-!
# The handler monad, from scratch

A handler reads an environment `E`, updates a state `S`, and emits `W`s:

* **read** the environment: configuration, such as default timeouts, so
  no number in a handler is magic;
* **update** the state, and see its own writes: a handler is ordinary
  sequential code;
* **emit**: what goes out (messages) and what is noted on the way
  (assertions for fuzzing). Emitting is write-only: a handler can never
  read back what it emitted, so an assertion cannot change what it does.

Time is not in the environment: handlers take `now` as a parameter.
-/

namespace Experiment

/-- A handler: given the environment and the state, a result, the next
    state, and what it emitted. -/
def H (E S W α : Type) : Type := E → S → α × S × List W

variable {E S W : Type}

instance : Monad (H E S W) where
  pure a   := fun _ s => (a, s, [])
  bind x f := fun e s =>
    let (a, s₁, w₁) := x e s
    let (b, s₂, w₂) := f a e s₁        -- the rest sees the updated state
    (b, s₂, w₁ ++ w₂)

/-- `read` gives the environment. -/
instance : MonadReaderOf E (H E S W) where
  read := fun e s => (e, s, [])

/-- `get`, `set` and `modify` work on the state. -/
instance : MonadStateOf S (H E S W) where
  get := fun _ s => (s, s, [])
  set s := fun _ _ => ((), s, [])
  modifyGet f := fun _ s => let (a, s') := f s; (a, s', [])

def emit (w : W) : H E S W Unit := fun _ s => ((), s, [w])

def H.run {α : Type} (x : H E S W α) (e : E) (s : S) : α × S × List W := x e s

end Experiment
