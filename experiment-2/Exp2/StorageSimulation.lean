import Exp2.SystemRefinement
import Experiment.PromiseFrame

/-!
# Storage simulation facts

The global abstract state is related to the object store extensionally, by
promise id. A node computes on one loaded document; `request_transport`
lifts that outcome to the global state without depending on list order.
-/

namespace Exp2

open Experiment
open Experiment.Storage

theorem matches_hidden {cfg : Storage.Config}
    {a : Experiment.Conf promises} {l : Network.Label system.Msg}
    (hview : clientView l = none) :
    Network.Matches { cfg.app with unreliable := true } clientView a l a := by
  refine ⟨[], trivial, ?_, rfl⟩
  rw [hview]
  rfl

theorem matches_client_request {cfg : Storage.Config}
    {a : Experiment.Conf promises} {client to : Addr} {t : Time} {m : Msg}
    (ht : a.now ≤ t) :
    let a' : Experiment.Conf promises :=
      ⟨a.net ++ [(.client client, .server, m)], a.state, t⟩
    Network.Matches { cfg.app with unreliable := true } clientView a
      (.client client, t, .request to (CMsg.app m)) a' := by
  dsimp
  refine ⟨[((.client client, t, .request m), [],
    ⟨a.net ++ [(.client client, .server, m)], a.state, t⟩)],
    ⟨.request ht, trivial⟩, ?_, rfl⟩
  simp [Experiment.observe, Experiment.seen, clientView]

theorem matches_client_receive {cfg : Storage.Config}
    {a : Experiment.Conf promises} {client : Addr} {sender : Network.Who}
    {t : Time} {m : Msg}
    {pre post : List (Experiment.Proc × Experiment.Proc × Msg)}
    (ht : a.now ≤ t)
    (hnet : a.net = pre ++ (.server, .client client, m) :: post) :
    let a' : Experiment.Conf promises := ⟨pre ++ post, a.state, t⟩
    Network.Matches { cfg.app with unreliable := true } clientView a
      (.client client, t, .receive sender (CMsg.app m)) a' := by
  dsimp
  refine ⟨[((.client client, t, .receive .server m), [],
    ⟨pre ++ post, a.state, t⟩)],
    ⟨.deliver ht hnet, trivial⟩, ?_, rfl⟩
  simp [Experiment.observe, Experiment.seen, clientView]

structure Call where
  client : Addr
  id     : CallId
  req    : Request
  now    : Time

def Call.retry (call : Call) (tries : Nat) :
    (k : Nat) → k < tries → NodeP Unit :=
  fun k _ => serve call.client call.id call.req call.now k

def Candidate.call (cand : Candidate) : Call :=
  ⟨cand.client, cand.id, cand.req, cand.now⟩

def AppOnly (mailbox : List (Addr × CMsg)) : Prop :=
  ∀ sender m, (sender, m) ∈ mailbox → ∃ app, m = .app app

theorem AppOnly.append_app {mailbox : List (Addr × CMsg)} (h : AppOnly mailbox)
    (sender : Addr) (m : Msg) : AppOnly (mailbox ++ [(sender, .app m)]) := by
  intro a n hn
  rw [List.mem_append] at hn
  rcases hn with hn | hn
  · exact h a n hn
  · simp only [List.mem_singleton, Prod.mk.injEq] at hn
    obtain ⟨rfl, rfl⟩ := hn
    exact ⟨m, rfl⟩

theorem answers_none_of_appOnly (mailbox : List (Addr × CMsg)) (op : Nat)
    (h : AppOnly mailbox) : take? (answers op) mailbox = none := by
  induction mailbox with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨sender, m⟩ := entry
    obtain ⟨app, rfl⟩ := h sender m (List.mem_cons_self)
    simp only [take?, answers, Bool.false_eq_true, if_false]
    rw [ih (fun a n hn => h a n (List.mem_cons_of_mem _ hn))]
    rfl

theorem take?_some_accept {M : Type} {accept : Addr → M → Bool}
    {mailbox rest : List (Addr × M)} {sender : Addr} {m : M}
    (h : take? accept mailbox = some (sender, m, rest)) :
    accept sender m = true := by
  induction mailbox generalizing rest sender m with
  | nil => simp [take?] at h
  | cons entry tail ih =>
    obtain ⟨a, n⟩ := entry
    by_cases ha : accept a n = true
    · simp only [take?, ha, if_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ha
    · have haf : accept a n = false := by
        simpa only [Bool.not_eq_true] using ha
      simp only [take?, haf, Bool.false_eq_true, if_false] at h
      obtain ⟨found, hfound, heq⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨b, q, tail'⟩ := found
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      exact ih hfound

theorem AppOnly.rest_of_take {mailbox rest : List (Addr × CMsg)}
    {sender : Addr} {m : CMsg} (happ : AppOnly mailbox)
    (htake : take? isRequest mailbox = some (sender, m, rest)) :
    AppOnly rest := by
  induction mailbox generalizing rest with
  | nil => simp [take?] at htake
  | cons entry tail ih =>
    obtain ⟨a, n⟩ := entry
    by_cases ha : isRequest a n = true
    · simp only [take?, ha, if_true, Option.some.injEq, Prod.mk.injEq] at htake
      obtain ⟨rfl, rfl, rfl⟩ := htake
      intro b q hq
      exact happ b q (List.mem_cons_of_mem _ hq)
    · have haf : isRequest a n = false := by
        simpa only [Bool.not_eq_true] using ha
      simp only [take?, haf, Bool.false_eq_true, if_false] at htake
      obtain ⟨found, hfound, heq⟩ := Option.map_eq_some_iff.mp htake
      obtain ⟨b, q, tail'⟩ := found
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      intro c x hx
      simp only [List.mem_cons] at hx
      rcases hx with hx | hx
      · have hp := Prod.mk.inj hx
        rw [hp.2]
        exact happ a n (List.mem_cons_self)
      · exact ih (fun c x hx => happ c x (List.mem_cons_of_mem _ hx))
          hfound c x hx

theorem request_of_take_isRequest {mailbox rest : List (Addr × CMsg)}
    {sender : Addr} {m : CMsg}
    (h : take? isRequest mailbox = some (sender, m, rest)) :
    ∃ id requestNow req, m = .app (.req id requestNow req) := by
  have ha := take?_some_accept h
  cases m with
  | app m =>
    cases m with
    | req id requestNow req => exact ⟨id, requestNow, req, rfl⟩
    | res _ _ => simp [isRequest] at ha
    | notify _ => simp [isRequest] at ha
  | get _ _ | put _ _ _ _ | got _ _ | written _ | conflict _ | failed _ =>
      simp [isRequest] at ha

inductive Control : Running Storage.Config Nat CMsg → Prop where
  | idle {next mailbox} :
      AppOnly mailbox →
      take? isRequest mailbox = none →
      Control ⟨next, mailbox, node⟩
  | loading {call : Call} {tries op next mailbox k} :
      AppOnly mailbox →
      next = op + 1 →
      k = loadK tries (call.retry tries) call.client call.id call.req call.now op →
      take? (answers op) mailbox = none →
      Control ⟨next, mailbox, k⟩
  | writing {cand : Candidate} {op next mailbox k} :
      AppOnly mailbox →
      next = op + 1 →
      k = writeK cand.tries (cand.call.retry cand.tries) cand op →
      take? (answers op) mailbox = none →
      Control ⟨next, mailbox, k⟩

theorem initial_control : Control (⟨0, [], node⟩ : Running Storage.Config Nat CMsg) :=
  .idle (by simp [AppOnly]) rfl

/-- The finite prefix before a node blocks on its store load. -/
theorem advance_startK {cfg : Storage.Config} {mailbox : List (Addr × CMsg)}
    {tries next : Nat} {retry : (k : Nat) → k < tries → NodeP Unit}
    {client : Addr} {id : CallId} {req : Request} {now stepNow : Time}
    (fuel : Nat)
    (hn : take? (answers next) mailbox = none) :
    advance node cfg stepNow (fuel + 5) next mailbox
      (startK tries retry client id req now) =
    [(⟨next + 1, mailbox, loadK tries retry client id req now next⟩,
      [.send cfg.store (.get next req.key)])] := by
  unfold startK fresh
  change advance node cfg stepNow (fuel + 5) next mailbox
    (.ask fun cfg' =>
      .load fun n =>
        .store (n + 1)
          (.emit (.send cfg'.store (.get n req.key))
            (loadK tries retry client id req now n))) = _
  rw [advance_ask, advance_load, advance_store, advance_emit]
  change (advance node cfg stepNow (fuel + 1) (next + 1) mailbox
    (loadK tries retry client id req now next)).map _ = _
  unfold loadK Proc.recv
  change (advance node cfg stepNow (fuel + 1) (next + 1) mailbox
    (.receive (answers next) _)).map _ = _
  rw [advance_receive_none _ _ _ fuel _ _ _ _ hn]
  rfl

theorem advance_idle_request {cfg : Storage.Config} {mailbox : List (Addr × CMsg)}
    (happ : AppOnly mailbox) (hn : take? isRequest mailbox = none)
    (next : Nat) (client : Addr) (id : CallId) (now stepNow : Time) (req : Request) :
    advance node cfg stepNow 64 next
      (mailbox ++ [(client, .app (.req id now req))]) node =
    [(⟨next + 1, mailbox,
      loadK cfg.retries (Call.retry ⟨client, id, req, now⟩ cfg.retries)
        client id req now next⟩,
      [.send cfg.store (.get next req.key)])] := by
  change advance node cfg stepNow 64 next
    (mailbox ++ [(client, .app (.req id now req))])
    (.receive isRequest _) = _
  change advance node cfg stepNow (63 + 1) next
    (mailbox ++ [(client, .app (.req id now req))])
    (.receive isRequest _) = _
  rw [advance.eq_def]
  simp only
  rw [take?_append_match hn rfl]
  simp only [Proc.bind]
  change advance node cfg stepNow (62 + 1) next mailbox
    (.ask fun cfg' => serve client id req now cfg'.retries) = _
  rw [advance_ask]
  rw [serve.eq_1]
  exact advance_startK 57 (answers_none_of_appOnly mailbox next happ)

theorem advance_node_request {cfg : Storage.Config}
    {mailbox rest : List (Addr × CMsg)} {next : Nat}
    {client : Addr} {id : CallId} {requestNow stepNow : Time} {req : Request}
    (fuel : Nat)
    (htake : take? isRequest mailbox =
      some (client, .app (.req id requestNow req), rest))
    (hrest : AppOnly rest) :
    advance node cfg stepNow (fuel + 7) next mailbox node =
    [(⟨next + 1, rest,
      loadK cfg.retries (Call.retry ⟨client, id, req, requestNow⟩ cfg.retries)
        client id req requestNow next⟩,
      [.send cfg.store (.get next req.key)])] := by
  change advance node cfg stepNow ((fuel + 5) + 1 + 1) next mailbox
    (.receive isRequest _) = _
  rw [advance_receive_some (a := client) (m := .app (.req id requestNow req))
    (h := htake)]
  simp only [Proc.bind]
  change advance node cfg stepNow ((fuel + 5) + 1) next rest
    (.ask fun cfg' => serve client id req requestNow cfg'.retries) = _
  rw [advance_ask, serve.eq_1]
  exact advance_startK fuel (answers_none_of_appOnly rest next hrest)

theorem advance_node_none {cfg : Storage.Config}
    {mailbox : List (Addr × CMsg)} {next : Nat} {stepNow : Time}
    (fuel : Nat) (hn : take? isRequest mailbox = none) :
    advance node cfg stepNow (fuel + 1) next mailbox node =
      [(⟨next, mailbox, node⟩, [])] :=
  advance_receive_none _ _ _ fuel _ _ _ _ hn

theorem advance_node_control {cfg : Storage.Config}
    {mailbox : List (Addr × CMsg)} {next : Nat} {stepNow : Time}
    (happ : AppOnly mailbox) (fuel : Nat) :
    ∃ r outs,
      advance node cfg stepNow (fuel + 7) next mailbox node = [(r, outs)] ∧
      Control r := by
  cases htake : take? isRequest mailbox with
  | none =>
    refine ⟨⟨next, mailbox, node⟩, [], ?_, .idle happ htake⟩
    simpa [Nat.add_assoc] using advance_node_none (cfg := cfg)
      (next := next) (stepNow := stepNow) (fuel + 6) htake
  | some found =>
    obtain ⟨client, m, rest⟩ := found
    obtain ⟨id, requestNow, req, rfl⟩ := request_of_take_isRequest htake
    have hrest := AppOnly.rest_of_take happ htake
    let call : Call := ⟨client, id, req, requestNow⟩
    refine ⟨⟨next + 1, rest,
      loadK cfg.retries (call.retry cfg.retries)
        client id req requestNow next⟩,
      [.send cfg.store (.get next req.key)], ?_, ?_⟩
    · simpa [call] using advance_node_request (cfg := cfg) fuel htake hrest
    · exact Control.loading (call := call) (tries := cfg.retries)
        hrest rfl rfl (answers_none_of_appOnly rest next hrest)

theorem idle_request_run {cfg : Storage.Config} {mailbox : List (Addr × CMsg)}
    (happ : AppOnly mailbox) (hn : take? isRequest mailbox = none)
    (next : Nat) (client : Addr) (id : CallId) (now stepNow : Time) (req : Request) :
    (toStep node 64 client (.app (.req id now req)) stepNow cfg
      (⟨next, mailbox, node⟩ : Running Storage.Config Nat CMsg)).val =
    [((), ⟨next + 1, mailbox,
      loadK cfg.retries (Call.retry ⟨client, id, req, now⟩ cfg.retries)
        client id req now next⟩,
      [.send cfg.store (.get next req.key)])] := by
  simp [toStep, advance_idle_request happ hn, someOr]

theorem idle_nonrequest_run {cfg : Storage.Config} {mailbox : List (Addr × CMsg)}
    (hn : take? isRequest mailbox = none) (next : Nat) (sender : Addr)
    (m : Msg) (now : Time) (hm : isRequest sender (.app m) = false) :
    (toStep node 64 sender (.app m) now cfg
      (⟨next, mailbox, node⟩ : Running Storage.Config Nat CMsg)).val =
    [((), ⟨next, mailbox ++ [(sender, .app m)], node⟩, [])] := by
  have hnone : take? isRequest (mailbox ++ [(sender, .app m)]) = none :=
    take?_append_miss hn hm
  have ha : advance node cfg now 64 next
      (mailbox ++ [(sender, .app m)]) node =
      [(⟨next, mailbox ++ [(sender, .app m)], node⟩, [])] := by
    change advance node cfg now (63 + 1) next
      (mailbox ++ [(sender, .app m)]) (.receive isRequest _) = _
    exact advance_receive_none _ _ _ 63 _ _ _ _ hnone
  simp [toStep, ha, someOr]

theorem loading_app_run {cfg : Storage.Config} {mailbox : List (Addr × CMsg)}
    {call : Call} {tries op next : Nat}
    (hn : take? (answers op) mailbox = none) (sender : Addr) (m : Msg)
    (now : Time) :
    (toStep node 64 sender (.app m) now cfg
      (⟨next, mailbox,
        loadK tries (call.retry tries) call.client call.id call.req call.now op⟩ :
        Running Storage.Config Nat CMsg)).val =
    [((), ⟨next, mailbox ++ [(sender, .app m)],
      loadK tries (call.retry tries) call.client call.id call.req call.now op⟩, [])] := by
  have hnone : take? (answers op) (mailbox ++ [(sender, .app m)]) = none :=
    take?_append_miss hn rfl
  have ha : advance node cfg now 64 next (mailbox ++ [(sender, .app m)])
      (loadK tries (call.retry tries) call.client call.id call.req call.now op) =
      [(⟨next, mailbox ++ [(sender, .app m)],
        loadK tries (call.retry tries) call.client call.id call.req call.now op⟩, [])] := by
    unfold loadK Proc.recv
    change advance node cfg now (63 + 1) next
      (mailbox ++ [(sender, .app m)]) (.receive (answers op) _) = _
    exact advance_receive_none _ _ _ 63 _ _ _ _ hnone
  simp [toStep, ha, someOr]

theorem writing_app_run {cfg : Storage.Config} {mailbox : List (Addr × CMsg)}
    {cand : Candidate} {op next : Nat}
    (hn : take? (answers op) mailbox = none) (sender : Addr) (m : Msg)
    (now : Time) :
    (toStep node 64 sender (.app m) now cfg
      (⟨next, mailbox,
        writeK cand.tries (cand.call.retry cand.tries) cand op⟩ :
        Running Storage.Config Nat CMsg)).val =
    [((), ⟨next, mailbox ++ [(sender, .app m)],
      writeK cand.tries (cand.call.retry cand.tries) cand op⟩, [])] := by
  have hnone : take? (answers op) (mailbox ++ [(sender, .app m)]) = none :=
    take?_append_miss hn rfl
  have ha : advance node cfg now 64 next (mailbox ++ [(sender, .app m)])
      (writeK cand.tries (cand.call.retry cand.tries) cand op) =
      [(⟨next, mailbox ++ [(sender, .app m)],
        writeK cand.tries (cand.call.retry cand.tries) cand op⟩, [])] := by
    unfold writeK Proc.recv
    change advance node cfg now (63 + 1) next
      (mailbox ++ [(sender, .app m)]) (.receive (answers op) _) = _
    exact advance_receive_none _ _ _ 63 _ _ _ _ hnone
  simp [toStep, ha, someOr]

theorem control_app_nonrequest {cfg : Storage.Config}
    {r : Running Storage.Config Nat CMsg} (hc : Control r)
    (sender : Addr) (m : Msg) (now : Time)
    (hm : isRequest sender (.app m) = false) :
    ∃ r',
      (toStep node 64 sender (.app m) now cfg r).val = [((), r', [])] ∧
      Control r' := by
  cases hc with
  | idle happ hn =>
    refine ⟨_, idle_nonrequest_run hn _ sender m now hm, ?_⟩
    exact .idle (happ.append_app sender m) (take?_append_miss hn hm)
  | loading happ hnext hk hn =>
    subst hk
    refine ⟨_, loading_app_run hn sender m now, ?_⟩
    exact .loading (happ.append_app sender m) hnext rfl
      (take?_append_miss hn rfl)
  | writing happ hnext hk hn =>
    subst hk
    refine ⟨_, writing_app_run hn sender m now, ?_⟩
    exact .writing (happ.append_app sender m) hnext rfl
      (take?_append_miss hn rfl)

theorem control_request_run {cfg : Storage.Config}
    {r : Running Storage.Config Nat CMsg} (hc : Control r)
    (client : Addr) (id : CallId) (requestNow stepNow : Time) (req : Request) :
    ∃ r' outs,
      (toStep node 64 client (.app (.req id requestNow req)) stepNow cfg r).val =
        [((), r', outs)] ∧
      Control r' := by
  cases hc with
  | idle happ hn =>
    let call : Call := ⟨client, id, req, requestNow⟩
    refine ⟨⟨_, _, loadK cfg.retries (call.retry cfg.retries)
      client id req requestNow _⟩,
      [.send cfg.store (.get _ req.key)],
      idle_request_run happ hn _ client id requestNow stepNow req, ?_⟩
    exact Control.loading (call := call) (tries := cfg.retries)
      (by simpa [call] using happ) rfl (by simp [call])
      (answers_none_of_appOnly _ _ happ)
  | loading happ hnext hk hn =>
    subst hk
    refine ⟨_, [], loading_app_run hn client (.req id requestNow req) stepNow, ?_⟩
    exact .loading (happ.append_app client (.req id requestNow req)) hnext rfl
      (take?_append_miss hn rfl)
  | writing happ hnext hk hn =>
    subst hk
    refine ⟨_, [], writing_app_run hn client (.req id requestNow req) stepNow, ?_⟩
    exact .writing (happ.append_app client (.req id requestNow req)) hnext rfl
      (take?_append_miss hn rfl)

theorem writing_written_run {cfg : Storage.Config}
    {mailbox : List (Addr × CMsg)} {cand : Candidate} {op next : Nat}
    (happ : AppOnly mailbox) (hn : take? (answers op) mailbox = none)
    (sender : Addr) (stepNow : Time) :
    ∃ r rest,
      (toStep node 64 sender (.written op) stepNow cfg
        (⟨next, mailbox,
          writeK cand.tries (cand.call.retry cand.tries) cand op⟩ :
          Running Storage.Config Nat CMsg)).val =
        [((), r,
          .send cand.client (.app (.res cand.id cand.res)) ::
            (sends cand.outs).map (fun (a, m) => .send a (.app m)) ++ rest)] ∧
      Control r := by
  obtain ⟨r, rest, hr, hc⟩ :=
    advance_node_control (cfg := cfg) (next := next) (stepNow := stepNow) happ 53
  refine ⟨r, rest, ?_, hc⟩
  have htake : take? (answers op) (mailbox ++ [(sender, .written op)]) =
      some (sender, .written op, mailbox) :=
    take?_append_match hn (by simp [answers])
  unfold toStep writeK Proc.recv answer sendAll Proc.send Proc.emitAllNow
  change (someOr ((advance node cfg stepNow (63 + 1) next
    (mailbox ++ [(sender, .written op)]) (.receive (answers op) _)).map _)
    _).val = _
  rw [advance_receive_some (a := sender) (m := .written op) (h := htake)]
  simp only [Proc.bind]
  change (someOr ((advance node cfg stepNow (62 + 1) next mailbox
    (.emit (.send cand.client (.app (.res cand.id cand.res)))
      (.emitMany ((sends cand.outs).map fun (a, m) => .send a (.app m))
        (.pure ())))).map _) _).val = _
  rw [advance_emit, advance_emitMany]
  rw [show advance node cfg stepNow 61 next mailbox (.pure ()) =
    advance node cfg stepNow 60 next mailbox node from rfl]
  rw [show 60 = 53 + 7 by omega]
  rw [hr]
  rfl

theorem writing_failed_run {cfg : Storage.Config}
    {mailbox : List (Addr × CMsg)} {cand : Candidate} {op next : Nat}
    (happ : AppOnly mailbox) (hn : take? (answers op) mailbox = none)
    (sender : Addr) (stepNow : Time) :
    ∃ r rest,
      (toStep node 64 sender (.failed op) stepNow cfg
        (⟨next, mailbox,
          writeK cand.tries (cand.call.retry cand.tries) cand op⟩ :
          Running Storage.Config Nat CMsg)).val =
        [((), r,
          .send cand.client (.app (.res cand.id ⟨503, none⟩)) :: rest)] ∧
      Control r := by
  obtain ⟨r, rest, hr, hc⟩ :=
    advance_node_control (cfg := cfg) (next := next) (stepNow := stepNow) happ 54
  refine ⟨r, rest, ?_, hc⟩
  have htake : take? (answers op) (mailbox ++ [(sender, .failed op)]) =
      some (sender, .failed op, mailbox) :=
    take?_append_match hn (by simp [answers])
  unfold toStep writeK Proc.recv answer Proc.send
  change (someOr ((advance node cfg stepNow (63 + 1) next
    (mailbox ++ [(sender, .failed op)]) (.receive (answers op) _)).map _)
    _).val = _
  rw [advance_receive_some (a := sender) (m := .failed op) (h := htake)]
  simp only [Proc.bind]
  change (someOr ((advance node cfg stepNow (62 + 1) next mailbox
    (.emit (.send cand.client (.app (.res cand.id ⟨503, none⟩)))
      (.pure ()))).map _) _).val = _
  rw [advance_emit]
  rw [show advance node cfg stepNow 62 next mailbox (.pure ()) =
    advance node cfg stepNow 61 next mailbox node from rfl]
  rw [show 61 = 54 + 7 by omega]
  rw [hr]
  rfl

theorem writing_conflict_retry_run {cfg : Storage.Config}
    {mailbox : List (Addr × CMsg)} {cand : Candidate} {op next k : Nat}
    (happ : AppOnly mailbox) (hn : take? (answers op) mailbox = none)
    (htries : cand.tries = k + 1) (sender : Addr) (stepNow : Time) :
    (toStep node 64 sender (.conflict op) stepNow cfg
      (⟨next, mailbox,
        writeK cand.tries (cand.call.retry cand.tries) cand op⟩ :
        Running Storage.Config Nat CMsg)).val =
    [((), ⟨next + 1, mailbox,
      loadK k (cand.call.retry k) cand.client cand.id cand.req cand.now next⟩,
      [.send cfg.store (.get next cand.req.key)])] := by
  have htake : take? (answers op) (mailbox ++ [(sender, .conflict op)]) =
      some (sender, .conflict op, mailbox) :=
    take?_append_match hn (by simp [answers])
  unfold toStep writeK Proc.recv
  change (someOr ((advance node cfg stepNow (63 + 1) next
    (mailbox ++ [(sender, .conflict op)]) (.receive (answers op) _)).map _)
    _).val = _
  rw [advance_receive_some (a := sender) (m := .conflict op) (h := htake)]
  simp only [Proc.bind]
  rw [htries]
  simp only [Call.retry, Candidate.call]
  rw [serve.eq_1]
  have ha := advance_startK (cfg := cfg) (mailbox := mailbox)
    (tries := k)
    (retry := fun k' _ => serve cand.client cand.id cand.req cand.now k')
    (client := cand.client)
    (id := cand.id) (req := cand.req) (now := cand.now) (stepNow := stepNow)
    (next := next) 58 (answers_none_of_appOnly mailbox next happ)
  rw [show 63 = 58 + 5 by omega, ha]
  rfl

theorem writing_conflict_exhausted_run {cfg : Storage.Config}
    {mailbox : List (Addr × CMsg)} {cand : Candidate} {op next : Nat}
    (happ : AppOnly mailbox) (hn : take? (answers op) mailbox = none)
    (htries : cand.tries = 0) (sender : Addr) (stepNow : Time) :
    ∃ r rest,
      (toStep node 64 sender (.conflict op) stepNow cfg
        (⟨next, mailbox,
          writeK cand.tries (cand.call.retry cand.tries) cand op⟩ :
          Running Storage.Config Nat CMsg)).val =
        [((), r,
          .send cand.client (.app (.res cand.id ⟨503, none⟩)) :: rest)] ∧
      Control r := by
  obtain ⟨r, rest, hr, hc⟩ :=
    advance_node_control (cfg := cfg) (next := next) (stepNow := stepNow) happ 54
  refine ⟨r, rest, ?_, hc⟩
  have htake : take? (answers op) (mailbox ++ [(sender, .conflict op)]) =
      some (sender, .conflict op, mailbox) :=
    take?_append_match hn (by simp [answers])
  unfold toStep writeK Proc.recv answer Proc.send
  change (someOr ((advance node cfg stepNow (63 + 1) next
    (mailbox ++ [(sender, .conflict op)]) (.receive (answers op) _)).map _)
    _).val = _
  rw [advance_receive_some (a := sender) (m := .conflict op) (h := htake)]
  simp only [Proc.bind]
  rw [htries]
  change (someOr ((advance node cfg stepNow (62 + 1) next mailbox
    (.emit (.send cand.client (.app (.res cand.id ⟨503, none⟩)))
      (.pure ()))).map _) _).val = _
  rw [advance_emit]
  rw [show advance node cfg stepNow 62 next mailbox (.pure ()) =
    advance node cfg stepNow 61 next mailbox node from rfl]
  rw [show 61 = 54 + 7 by omega, hr]
  rfl

set_option maxHeartbeats 1000000 in
theorem loading_got_unchanged_run {cfg : Storage.Config}
    {mailbox : List (Addr × CMsg)} {call : Call} {tries op next : Nat}
    {doc : Option (Promise × Version)} {res : Response}
    {after : Experiment.State} {outs : List (Out Msg)}
    (happ : AppOnly mailbox) (hn : take? (answers op) mailbox = none)
    (hpick :
      pick ((Experiment.dispatch call.req call.now).run
        { cfg.app with unreliable := true }
        { promises := doc.toList.map (·.1) }) 0 = (res, after, outs))
    (hunchanged : after = { promises := doc.toList.map (·.1) })
    (sender : Addr) (stepNow : Time) :
    ∃ r rest,
      (toStep node 64 sender (.got op doc) stepNow cfg
        (⟨next, mailbox,
          loadK tries (call.retry tries)
            call.client call.id call.req call.now op⟩ :
          Running Storage.Config Nat CMsg)).val =
        [((), r, notes outs ++
          .send call.client (.app (.res call.id res)) ::
            (sends outs).map (fun (a, m) => .send a (.app m)) ++ rest)] ∧
      Control r := by
  subst after
  obtain ⟨r, rest, hr, hc⟩ :=
    advance_node_control (cfg := cfg) (next := next) (stepNow := stepNow) happ 51
  refine ⟨r, rest, ?_, hc⟩
  have htake : take? (answers op) (mailbox ++ [(sender, .got op doc)]) =
      some (sender, .got op doc, mailbox) :=
    take?_append_match hn (by simp [answers])
  unfold toStep loadK Proc.recv
  change (someOr ((advance node cfg stepNow (63 + 1) next
    (mailbox ++ [(sender, .got op doc)]) (.receive (answers op) _)).map _)
    _).val = _
  rw [advance_receive_some (a := sender) (m := .got op doc) (h := htake)]
  simp only [Proc.bind]
  change (someOr ((advance node cfg stepNow (62 + 1) next mailbox
    (.ask fun cfg' => decideK tries (call.retry tries) call.client call.id
      call.req call.now cfg' doc { promises := doc.toList.map (·.1) }
      (pick ((Experiment.dispatch call.req call.now).run
        { cfg'.app with unreliable := true }
        { promises := doc.toList.map (·.1) }) 0))).map _) _).val = _
  rw [advance_ask, hpick]
  unfold decideK note answer sendAll Proc.send Proc.emitAllNow
  simp only [beq_self_eq_true, if_true]
  change (someOr ((advance node cfg stepNow (61 + 1) next mailbox
    (.emitMany (notes outs)
      (.emit (.send call.client (.app (.res call.id res)))
        (.emitMany ((sends outs).map fun (a, m) => .send a (.app m))
          (.pure ()))))).map _) _).val = _
  rw [advance_emitMany, advance_emit, advance_emitMany]
  rw [show advance node cfg stepNow 59 next mailbox (.pure ()) =
    advance node cfg stepNow 58 next mailbox node from rfl]
  rw [show 58 = 51 + 7 by omega, hr]
  simp [List.append_assoc, someOr]

set_option maxHeartbeats 1000000 in
theorem loading_got_changed_run {cfg : Storage.Config}
    {mailbox : List (Addr × CMsg)} {call : Call} {tries op next : Nat}
    {doc : Option (Promise × Version)} {res : Response}
    {after : Experiment.State} {outs : List (Out Msg)} {promise : Promise}
    (happ : AppOnly mailbox) (hn : take? (answers op) mailbox = none)
    (hpick :
      pick ((Experiment.dispatch call.req call.now).run
        { cfg.app with unreliable := true }
        { promises := doc.toList.map (·.1) }) 0 = (res, after, outs))
    (hchanged : (after == { promises := doc.toList.map (·.1) }) = false)
    (hpromise : after.promises.find? (·.id == call.req.key) = some promise)
    (sender : Addr) (stepNow : Time) :
    let cand : Candidate :=
      ⟨call.client, call.id, call.req, call.now, tries, doc,
        res, after, outs, promise⟩
    (toStep node 64 sender (.got op doc) stepNow cfg
      (⟨next, mailbox,
        loadK tries (call.retry tries)
          call.client call.id call.req call.now op⟩ :
        Running Storage.Config Nat CMsg)).val =
      [((), ⟨next + 1, mailbox,
        writeK tries (call.retry tries) cand next⟩,
        notes outs ++
          [.send cfg.store (.put next call.req.key promise (doc.map (·.2)))])] := by
  dsimp
  have htake : take? (answers op) (mailbox ++ [(sender, .got op doc)]) =
      some (sender, .got op doc, mailbox) :=
    take?_append_match hn (by simp [answers])
  have hw : advance node cfg stepNow 58 (next + 1) mailbox
      (writeK tries (call.retry tries)
        ⟨call.client, call.id, call.req, call.now, tries, doc,
          res, after, outs, promise⟩ next) =
      [(⟨next + 1, mailbox,
        writeK tries (call.retry tries)
          ⟨call.client, call.id, call.req, call.now, tries, doc,
            res, after, outs, promise⟩ next⟩, [])] := by
    unfold writeK Proc.recv
    change advance node cfg stepNow (57 + 1) (next + 1) mailbox
      (.receive (answers next) _) = _
    exact advance_receive_none _ _ _ 57 _ _ _ _
      (answers_none_of_appOnly mailbox next happ)
  unfold toStep loadK Proc.recv
  change (someOr ((advance node cfg stepNow (63 + 1) next
    (mailbox ++ [(sender, .got op doc)]) (.receive (answers op) _)).map _)
    _).val = _
  rw [advance_receive_some (a := sender) (m := .got op doc) (h := htake)]
  simp only [Proc.bind]
  change (someOr ((advance node cfg stepNow (62 + 1) next mailbox
    (.ask fun cfg' => decideK tries (call.retry tries) call.client call.id
      call.req call.now cfg' doc { promises := doc.toList.map (·.1) }
      (pick ((Experiment.dispatch call.req call.now).run
        { cfg'.app with unreliable := true }
        { promises := doc.toList.map (·.1) }) 0))).map _) _).val = _
  rw [advance_ask, hpick]
  unfold decideK note fresh Proc.emitAllNow Proc.send
  simp only [hchanged, Bool.false_eq_true, if_false, hpromise]
  change (someOr ((advance node cfg stepNow (61 + 1) next mailbox
    (.emitMany (notes outs)
      (.load fun n => .store (n + 1)
        (.emit (.send cfg.store
          (.put n call.req.key promise (doc.map (·.2))))
          (writeK tries (call.retry tries)
            ⟨call.client, call.id, call.req, call.now, tries, doc,
              res, after, outs, promise⟩ n))))).map _) _).val = _
  rw [advance_emitMany, advance_load, advance_store, advance_emit]
  rw [hw]
  simp [someOr]

def storeLookup (s : Store) (key : Ident) : Option (Promise × Version) :=
  (s.docs.find? (·.1 == key)).map fun (_, p, v) => (p, v)

def storePromiseAt (s : Store) (key : Ident) : Option Promise :=
  (storeLookup s key).map (·.1)

def StoreRep (store : Store) (state : Experiment.State) : Prop :=
  ∀ key, storePromiseAt store key = Experiment.promiseAt state key

def storeCommit (store : Store) (key : Ident) (p : Promise) : Store :=
  let version := (storeLookup store key).map (·.2) |>.getD 0
  { docs := (key, p, version + 1) :: store.docs.filter (·.1 != key) }

theorem find?_filter_store_other (docs : List (Ident × Promise × Version))
    {keep drop : Ident} (h : keep ≠ drop) :
    (docs.filter (·.1 != drop)).find? (·.1 == keep) = docs.find? (·.1 == keep) := by
  induction docs with
  | nil => rfl
  | cons entry rest ih =>
    simp only [List.filter_cons, List.find?_cons]
    by_cases hd : entry.1 = drop
    · have hk : entry.1 ≠ keep := by
        intro he
        exact h (he.symm.trans hd)
      rw [show (entry.1 != drop) = false from bne_eq_false_iff_eq.mpr hd]
      rw [show (entry.1 == keep) = false from beq_eq_false_iff_ne.mpr hk]
      simp only [Bool.false_eq_true, if_false]
      exact ih
    · rw [show (entry.1 != drop) = true from bne_iff_ne.mpr hd]
      change (entry :: rest.filter (·.1 != drop)).find? (·.1 == keep) =
        (entry :: rest).find? (·.1 == keep)
      by_cases hk : entry.1 = keep
      · rw [List.find?_cons, List.find?_cons,
          show (entry.1 == keep) = true from beq_iff_eq.mpr hk]
      · rw [List.find?_cons, List.find?_cons,
          show (entry.1 == keep) = false from beq_eq_false_iff_ne.mpr hk]
        exact ih

theorem storePromiseAt_commit (store : Store) (key : Ident) (p : Promise) (other : Ident) :
    storePromiseAt (storeCommit store key p) other =
      if other = key then some p else storePromiseAt store other := by
  by_cases h : other = key
  · subst other
    simp [storePromiseAt, storeLookup, storeCommit]
  · simp only [storePromiseAt, storeLookup, storeCommit, List.find?_cons]
    rw [show (key == other) = false from beq_eq_false_iff_ne.mpr (Ne.symm h)]
    rw [if_neg h]
    simp only
    rw [find?_filter_store_other _ h]

theorem storeLookup_commit (store : Store) (key : Ident) (p : Promise) (other : Ident) :
    storeLookup (storeCommit store key p) other =
      if other = key then
        some (p, ((storeLookup store key).map (·.2) |>.getD 0) + 1)
      else storeLookup store other := by
  by_cases h : other = key
  · subst other
    simp [storeLookup, storeCommit]
  · simp only [storeLookup, storeCommit, List.find?_cons]
    rw [show (key == other) = false from beq_eq_false_iff_ne.mpr (Ne.symm h)]
    rw [if_neg h]
    simp only
    rw [find?_filter_store_other _ h]

/-- A loaded document remains a sound CAS snapshot while the store advances:
if its version still matches, its promise still matches too. -/
def Snapshot (store : Store) (key : Ident) :
    Option (Promise × Version) → Prop
  | none => True
  | some (promise, version) =>
      ∃ currentPromise currentVersion,
        storeLookup store key = some (currentPromise, currentVersion) ∧
        version ≤ currentVersion ∧
        (version = currentVersion → promise = currentPromise)

theorem Snapshot.of_lookup {store : Store} {key : Ident}
    {doc : Option (Promise × Version)}
    (h : storeLookup store key = doc) : Snapshot store key doc := by
  cases doc with
  | none => trivial
  | some value =>
    obtain ⟨promise, version⟩ := value
    exact ⟨promise, version, h, Nat.le_refl _, fun _ => rfl⟩

theorem Snapshot.commit {store : Store} {loadedKey writtenKey : Ident}
    {doc : Option (Promise × Version)} {written : Promise}
    (h : Snapshot store loadedKey doc) :
    Snapshot (storeCommit store writtenKey written) loadedKey doc := by
  cases doc with
  | none => trivial
  | some value =>
    obtain ⟨promise, version⟩ := value
    simp only [Snapshot] at h ⊢
    obtain ⟨currentPromise, currentVersion, hlookup, hle, hpromise⟩ := h
    by_cases hk : loadedKey = writtenKey
    · subst writtenKey
      rw [storeLookup_commit, if_pos rfl]
      refine ⟨written, currentVersion + 1, ?_, Nat.le_trans hle
        (Nat.le_succ currentVersion), ?_⟩
      · simp [hlookup]
      · intro heq
        exact (Nat.ne_of_lt (Nat.lt_succ_of_le hle) heq).elim
    · refine ⟨currentPromise, currentVersion, ?_, hle, hpromise⟩
      rw [storeLookup_commit, if_neg hk]
      exact hlookup

theorem Snapshot.eq_of_versions {store : Store} {key : Ident}
    {doc : Option (Promise × Version)}
    (hs : Snapshot store key doc)
    (hv : doc.map (·.2) = (storeLookup store key).map (·.2)) :
    storeLookup store key = doc := by
  cases doc with
  | none =>
    cases hcur : storeLookup store key with
    | none => rfl
    | some current =>
      simp [hcur] at hv
  | some loaded =>
    obtain ⟨promise, version⟩ := loaded
    obtain ⟨currentPromise, currentVersion, hlookup, hle, hp⟩ := hs
    simp only [Option.map_some] at hv
    rw [hlookup] at hv
    simp only [Option.map_some, Option.some.injEq] at hv
    subst currentVersion
    rw [hlookup, hp rfl]

def KeyLocal (key : Ident) (state : Experiment.State) : Prop :=
  state.promises = [] ∨ ∃ promise, state.promises = [promise] ∧ promise.id = key

def PreservesKey (key : Ident) (h : Experiment.Handler α) : Prop :=
  ∀ cfg state result, KeyLocal key state → result ∈ (h cfg state).val →
    KeyLocal key result.2.1

namespace PreservesKey

theorem pure (key : Ident) (value : α) :
    PreservesKey key (Pure.pure value : Experiment.Handler α) := by
  intro cfg state result hlocal hout
  change result ∈ [(value, state, [])] at hout
  simp only [List.mem_singleton] at hout
  subst result
  exact hlocal

theorem bind {key : Ident} {first : Experiment.Handler α}
    {next : α → Experiment.Handler β}
    (hfirst : PreservesKey key first)
    (hnext : ∀ value, PreservesKey key (next value)) :
    PreservesKey key (first >>= next) := by
  intro cfg state result hlocal hout
  simp only [Bind.bind, Some.bind, Some.map, List.mem_flatMap, List.mem_map] at hout
  obtain ⟨⟨value, middle, firstOut⟩, hm, ⟨answer, final, nextOut⟩,
    hn, rfl⟩ := hout
  exact hnext value cfg middle (answer, final, nextOut)
    (hfirst cfg state (value, middle, firstOut) hlocal hm) hn

theorem bind_on {key : Ident} {first : Experiment.Handler α}
    {next : α → Experiment.Handler β} {P : α → Prop}
    (hfirst : PreservesKey key first)
    (hP : Experiment.Returns first P)
    (hnext : ∀ value, P value → PreservesKey key (next value)) :
    PreservesKey key (first >>= next) := by
  intro cfg state result hlocal hout
  simp only [Bind.bind, Some.bind, Some.map, List.mem_flatMap, List.mem_map] at hout
  obtain ⟨⟨value, middle, firstOut⟩, hm, ⟨answer, final, nextOut⟩,
    hn, rfl⟩ := hout
  exact hnext value (hP cfg state (value, middle, firstOut) hm)
    cfg middle (answer, final, nextOut)
    (hfirst cfg state (value, middle, firstOut) hlocal hm) hn

theorem read (key : Ident) :
    PreservesKey key (read : Experiment.Handler Experiment.Config) := by
  intro cfg state result hlocal hout
  change result ∈ [(cfg, state, [])] at hout
  simp only [List.mem_singleton] at hout
  subst result
  exact hlocal

theorem readDefaultTimeout (key : Ident) :
    PreservesKey key Experiment.readDefaultTimeout := by
  intro cfg state result hlocal hout
  change result ∈ [(cfg.defaultTimeout, state, [])] at hout
  simp only [List.mem_singleton] at hout
  subst result
  exact hlocal

theorem emit (key : Ident) (out : Out Msg) :
    PreservesKey key (Experiment.emit out : Experiment.Handler Unit) := by
  intro cfg state result hlocal hout
  change result ∈ [((), state, [out])] at hout
  simp only [List.mem_singleton] at hout
  subst result
  exact hlocal

theorem choose (key : Ident) (values : Some α) :
    PreservesKey key (Experiment.choose values : Experiment.Handler α) := by
  intro cfg state result hlocal hout
  change result ∈ values.val.map (fun value => (value, state, [])) at hout
  obtain ⟨value, _, rfl⟩ := List.mem_map.mp hout
  exact hlocal

theorem lookup (key : Ident) :
    PreservesKey key (Experiment.lookup key) := by
  intro cfg state result hlocal hout
  change result ∈ [(Experiment.promiseAt state key, state, [])] at hout
  simp only [List.mem_singleton] at hout
  subst result
  exact hlocal

theorem save {key : Ident} {promise : Promise} (hid : promise.id = key) :
    PreservesKey key (Experiment.save promise) := by
  intro cfg state result hlocal hout
  change result ∈
    [((), ({ promises := promise ::
      (state.promises.filter fun p => p.id != promise.id) } : Experiment.State), [])] at hout
  simp only [List.mem_singleton] at hout
  subst result
  rcases hlocal with hempty | ⟨old, hold, holdId⟩
  · right
    refine ⟨promise, ?_, hid⟩
    simp [hempty]
  · right
    refine ⟨promise, ?_, hid⟩
    simp [hold, holdId, hid]

theorem notifyAll (key : Ident) (promise : Record) :
    ∀ addresses, PreservesKey key (Experiment.notifyAll promise addresses) := by
  intro addresses
  induction addresses with
  | nil => exact pure key ()
  | cons address rest ih =>
    exact bind (emit key (.send address (.notify promise))) fun _ => ih

theorem settle {key : Ident} {promise : Promise} (hid : promise.id = key)
    (state : PromiseState) (value : String) :
    PreservesKey key (Experiment.settle promise state value) := by
  unfold Experiment.settle
  refine bind (emit key (.always _ _)) fun _ => ?_
  refine bind (emit key (.always _ _)) fun _ => ?_
  refine bind (save (promise := { promise with state, value, listeners := [] }) hid)
    fun _ => ?_
  refine bind (notifyAll key _ _) fun _ => pure key _

theorem load (key : Ident) (now : Time) :
    PreservesKey key (Experiment.load key now) := by
  unfold Experiment.load
  refine bind_on (lookup key) (Experiment.lookup_returns key) ?_
  intro doc hdoc
  cases doc with
  | none => exact pure key none
  | some promise =>
    change PreservesKey key
      (if promise.state == .pending && decide (promise.timeoutAt ≤ now) then
        do let settled ← Experiment.settle promise .rejectedTimedout ""
           return some settled
       else Pure.pure (some promise))
    split
    · exact bind (settle hdoc _ _) fun _ => pure key _
    · exact pure key _

theorem promiseGet (key : Ident) (now : Time) :
    PreservesKey key (Experiment.promiseGet key now) := by
  unfold Experiment.promiseGet
  refine bind (load key now) ?_
  intro doc
  cases doc <;> exact pure key _

theorem promiseCreate (key : Ident) (timeoutAt : Option Time) (now : Time) :
    PreservesKey key (Experiment.promiseCreate key timeoutAt now) := by
  unfold Experiment.promiseCreate
  refine bind_on (load key now) (Experiment.load_returns key now) ?_
  intro doc hdoc
  cases doc with
  | some promise =>
    exact bind (emit key (.sometimes _ _)) fun _ => pure key _
  | none =>
    refine bind (readDefaultTimeout key) fun defaultTimeout => ?_
    let deadline := timeoutAt.getD (now + defaultTimeout)
    let promise : Promise :=
      { id := key, timeoutAt := deadline,
        state := if deadline ≤ now then .rejectedTimedout else .pending }
    exact bind (save (promise := promise) rfl) fun _ => pure key _

theorem promiseSettle (key : Ident) (state : PromiseState)
    (value : String) (now : Time) :
    PreservesKey key (Experiment.promiseSettle key state value now) := by
  unfold Experiment.promiseSettle
  split
  · exact pure key _
  · refine bind (pure key ()) fun _ => ?_
    refine bind_on (load key now) (Experiment.load_returns key now) ?_
    intro doc hdoc
    cases doc with
    | none => exact pure key _
    | some promise =>
      change PreservesKey key
        (if promise.state == .pending then
          do let settled ← Experiment.settle promise state value
             return Experiment.ok settled
         else do
          Experiment.sometimes "settle arrives after the timeout"
            (promise.state == .rejectedTimedout)
          return Experiment.ok promise)
      split
      · exact bind (settle hdoc state value) fun _ => pure key _
      · exact bind (emit key (.sometimes _ _)) fun _ => pure key _

theorem promiseListen (key : Ident) (address : Addr) (now : Time) :
    PreservesKey key (Experiment.promiseListen key address now) := by
  unfold Experiment.promiseListen
  refine bind_on (load key now) (Experiment.load_returns key now) ?_
  intro doc hdoc
  cases doc with
  | none => exact pure key _
  | some promise =>
    change PreservesKey key
      (if promise.state == .pending && !promise.listeners.contains address then
        let updated := { promise with listeners := promise.listeners ++ [address] }
        do Experiment.save updated; return Experiment.ok updated
       else Pure.pure (Experiment.ok promise))
    split
    · exact bind (save (promise := { promise with
        listeners := promise.listeners ++ [address] }) hdoc) fun _ => pure key _
    · exact pure key _

theorem dispatch (request : Request) (now : Time) :
    PreservesKey request.key (Experiment.dispatch request now) := by
  cases request with
  | get key => exact promiseGet key now
  | create key timeoutAt => exact promiseCreate key timeoutAt now
  | settle key state value => exact promiseSettle key state value now
  | listen key address => exact promiseListen key address now

end PreservesKey

def OnlyNotifies (outs : List (Out Msg)) : Prop :=
  ∀ address message, (address, message) ∈ sends outs →
    ∃ promise, message = .notify promise

def EmitsOnlyNotifies (handler : Experiment.Handler α) : Prop :=
  ∀ cfg state result, result ∈ (handler cfg state).val →
    OnlyNotifies result.2.2

namespace EmitsOnlyNotifies

theorem pure (value : α) :
    EmitsOnlyNotifies (Pure.pure value : Experiment.Handler α) := by
  intro cfg state result hout
  change result ∈ [(value, state, [])] at hout
  simp only [List.mem_singleton] at hout
  subst result
  simp [OnlyNotifies, sends]

theorem bind {first : Experiment.Handler α}
    {next : α → Experiment.Handler β}
    (hfirst : EmitsOnlyNotifies first)
    (hnext : ∀ value, EmitsOnlyNotifies (next value)) :
    EmitsOnlyNotifies (first >>= next) := by
  intro cfg state result hout
  simp only [Bind.bind, Some.bind, Some.map, List.mem_flatMap,
    List.mem_map] at hout
  obtain ⟨⟨value, middle, firstOut⟩, hm,
    ⟨answer, final, nextOut⟩, hn, rfl⟩ := hout
  intro address message hsend
  simp only [sends, List.filterMap_append, List.mem_append] at hsend
  rcases hsend with hsend | hsend
  · exact hfirst cfg state (value, middle, firstOut) hm address message hsend
  · exact hnext value cfg middle (answer, final, nextOut) hn
      address message hsend

theorem read :
    EmitsOnlyNotifies (read : Experiment.Handler Experiment.Config) := by
  intro cfg state result hout
  change result ∈ [(cfg, state, [])] at hout
  simp only [List.mem_singleton] at hout
  subst result
  simp [OnlyNotifies, sends]

theorem readDefaultTimeout :
    EmitsOnlyNotifies Experiment.readDefaultTimeout := by
  intro cfg state result hout
  change result ∈ [(cfg.defaultTimeout, state, [])] at hout
  simp only [List.mem_singleton] at hout
  subst result
  simp [OnlyNotifies, sends]

theorem choose (values : Some α) :
    EmitsOnlyNotifies (Experiment.choose values : Experiment.Handler α) := by
  intro cfg state result hout
  change result ∈ values.val.map (fun value => (value, state, [])) at hout
  obtain ⟨value, _, rfl⟩ := List.mem_map.mp hout
  simp [OnlyNotifies, sends]

theorem emitAssertion (out : Out Msg)
    (h : ∀ address message, out ≠ .send address message) :
    EmitsOnlyNotifies (Experiment.emit out : Experiment.Handler Unit) := by
  intro cfg state result hout
  change result ∈ [((), state, [out])] at hout
  simp only [List.mem_singleton] at hout
  subst result
  intro address message hsend
  simp [sends] at hsend

theorem always (name : String) (ok : Bool) :
    EmitsOnlyNotifies (Experiment.always name ok) := by
  apply emitAssertion
  simp

theorem sometimes (name : String) (hit : Bool) :
    EmitsOnlyNotifies (Experiment.sometimes name hit) := by
  apply emitAssertion
  simp

theorem sendNotify (address : Addr) (promise : Record) :
    EmitsOnlyNotifies (Experiment.send address (.notify promise)) := by
  intro cfg state result hout
  change result ∈ [((), state, [.send address (.notify promise)])] at hout
  simp only [List.mem_singleton] at hout
  subst result
  intro destination message hsend
  simp [sends] at hsend
  obtain ⟨rfl, rfl⟩ := hsend
  exact ⟨promise, rfl⟩

theorem save (promise : Promise) :
    EmitsOnlyNotifies (Experiment.save promise) := by
  intro cfg state result hout
  change result ∈
    [((), ({ promises := promise ::
      state.promises.filter (·.id != promise.id) } : Experiment.State), [])] at hout
  simp only [List.mem_singleton] at hout
  subst result
  simp [OnlyNotifies, sends]

theorem notifyAll (promise : Record) :
    ∀ addresses, EmitsOnlyNotifies (Experiment.notifyAll promise addresses) := by
  intro addresses
  induction addresses with
  | nil => exact pure ()
  | cons address rest ih =>
    exact bind (sendNotify address promise) (fun _ => ih)

theorem settle (promise : Promise) (state : PromiseState) (value : String) :
    EmitsOnlyNotifies (Experiment.settle promise state value) := by
  unfold Experiment.settle
  exact bind (always _ _) (fun _ =>
    bind (always _ _) (fun _ =>
      bind (save _) (fun _ =>
        bind (notifyAll _ _) (fun _ => pure _))))

theorem lookup (key : Ident) :
    EmitsOnlyNotifies (Experiment.lookup key) := by
  intro cfg state result hout
  change result ∈ [(Experiment.promiseAt state key, state, [])] at hout
  simp only [List.mem_singleton] at hout
  subst result
  simp [OnlyNotifies, sends]

theorem load (key : Ident) (now : Time) :
    EmitsOnlyNotifies (Experiment.load key now) := by
  unfold Experiment.load
  refine bind (lookup key) fun doc => ?_
  cases doc with
  | none => exact pure none
  | some promise =>
    change EmitsOnlyNotifies
      (if promise.state == .pending && decide (promise.timeoutAt ≤ now) then
        do let settled ← Experiment.settle promise .rejectedTimedout ""
           return some settled
       else Pure.pure (some promise))
    split
    · exact bind (settle promise .rejectedTimedout "") (fun value => pure (some value))
    · exact pure (some promise)

theorem promiseGet (key : Ident) (now : Time) :
    EmitsOnlyNotifies (Experiment.promiseGet key now) := by
  unfold Experiment.promiseGet
  refine bind (load key now) ?_
  intro doc
  cases doc <;> exact pure _

theorem promiseCreate (key : Ident) (timeoutAt : Option Time) (now : Time) :
    EmitsOnlyNotifies (Experiment.promiseCreate key timeoutAt now) := by
  unfold Experiment.promiseCreate
  refine bind (load key now) ?_
  intro doc
  cases doc with
  | some promise =>
    exact bind (sometimes _ _) (fun _ => pure _)
  | none =>
    exact bind readDefaultTimeout (fun defaultTimeout =>
      bind (save {
        id := key
        timeoutAt := timeoutAt.getD (now + defaultTimeout)
        state := if timeoutAt.getD (now + defaultTimeout) ≤ now then
          .rejectedTimedout else .pending
      }) (fun _ => pure _))

theorem promiseSettle (key : Ident) (state : PromiseState)
    (value : String) (now : Time) :
    EmitsOnlyNotifies (Experiment.promiseSettle key state value now) := by
  unfold Experiment.promiseSettle
  split
  · exact pure _
  · refine bind (pure ()) fun _ => ?_
    refine bind (load key now) ?_
    intro doc
    cases doc with
    | none => exact pure _
    | some promise =>
      change EmitsOnlyNotifies
        (if promise.state == .pending then
          do let settled ← Experiment.settle promise state value
             return Experiment.ok settled
         else do
          Experiment.sometimes "settle arrives after the timeout"
            (promise.state == .rejectedTimedout)
          return Experiment.ok promise)
      split
      · exact bind (settle promise state value) (fun settled => pure _)
      · exact bind (sometimes _ _) (fun _ => pure _)

theorem promiseListen (key : Ident) (address : Addr) (now : Time) :
    EmitsOnlyNotifies (Experiment.promiseListen key address now) := by
  unfold Experiment.promiseListen
  refine bind (load key now) ?_
  intro doc
  cases doc with
  | none => exact pure _
  | some promise =>
    change EmitsOnlyNotifies
      (if promise.state == .pending && !promise.listeners.contains address then
        let updated := { promise with
          listeners := promise.listeners ++ [address] }
        do Experiment.save updated; return Experiment.ok updated
       else Pure.pure (Experiment.ok promise))
    split
    · exact bind (save { promise with
        listeners := promise.listeners ++ [address] }) (fun _ => pure _)
    · exact pure _

theorem dispatch (request : Request) (now : Time) :
    EmitsOnlyNotifies (Experiment.dispatch request now) := by
  cases request with
  | get key => exact promiseGet key now
  | create key timeoutAt => exact promiseCreate key timeoutAt now
  | settle key state value => exact promiseSettle key state value now
  | listen key address => exact promiseListen key address now

end EmitsOnlyNotifies

def DocAtKey (key : Ident) : Option (Promise × Version) → Prop
  | none => True
  | some (promise, _) => promise.id = key

theorem keyLocal_of_doc {key : Ident} {doc : Option (Promise × Version)}
    (hdoc : DocAtKey key doc) :
    KeyLocal key { promises := doc.toList.map (·.1) } := by
  cases doc with
  | none => exact .inl rfl
  | some value =>
    obtain ⟨promise, version⟩ := value
    exact .inr ⟨promise, rfl, hdoc⟩

theorem docAtKey_of_rep_lookup {store : Store} {global : Experiment.State}
    {key : Ident} {doc : Option (Promise × Version)}
    (hrep : StoreRep store global) (hlookup : storeLookup store key = doc) :
    DocAtKey key doc := by
  cases doc with
  | none => trivial
  | some value =>
    obtain ⟨promise, version⟩ := value
    have hat : Experiment.promiseAt global key = some promise := by
      rw [← hrep key]
      simp [storePromiseAt, hlookup]
    change global.promises.find? (·.id == key) = some promise at hat
    have hf : (promise.id == key) = true :=
      List.find?_some (p := fun x : Promise => x.id == key)
        (a := promise) hat
    exact beq_iff_eq.mp hf

theorem dispatch_changed_singleton {cfg : Storage.Config} {call : Call}
    {doc : Option (Promise × Version)} {res : Response}
    {after : Experiment.State} {outs : List (Out Msg)} {promise : Promise}
    (hdoc : DocAtKey call.req.key doc)
    (hpick :
      pick ((Experiment.dispatch call.req call.now).run
        { cfg.app with unreliable := true }
        { promises := doc.toList.map (·.1) }) 0 = (res, after, outs))
    (hpromise : after.promises.find? (·.id == call.req.key) = some promise) :
    after.promises = [promise] := by
  have hmem : (res, after, outs) ∈
      ((Experiment.dispatch call.req call.now).run
        { cfg.app with unreliable := true }
        { promises := doc.toList.map (·.1) }).val := by
    rw [← hpick]
    exact pick_mem _ _
  have hlocal := PreservesKey.dispatch call.req call.now
    { cfg.app with unreliable := true }
    { promises := doc.toList.map (·.1) } (res, after, outs)
    (keyLocal_of_doc hdoc) hmem
  rcases hlocal with hempty | ⟨found, hsingle, hid⟩
  · rw [hempty] at hpromise
    simp at hpromise
  · rw [hsingle] at hpromise
    simp only [List.find?_cons, hid, beq_self_eq_true,
      Option.some.injEq] at hpromise
    subst found
    exact hsingle

def Candidate.Valid (cfg : Storage.Config) (cand : Candidate) : Prop :=
  let before : Experiment.State := { promises := cand.doc.toList.map (·.1) }
  (cand.res, cand.after, cand.outs) =
      pick ((Experiment.dispatch cand.req cand.now).run
        { cfg.app with unreliable := true } before) 0 ∧
  cand.after.promises.find? (·.id == cand.req.key) = some cand.promise ∧
  cand.after.promises = [cand.promise]

theorem changed_candidate_valid {cfg : Storage.Config} {call : Call}
    {tries : Nat} {doc : Option (Promise × Version)}
    {res : Response} {after : Experiment.State} {outs : List (Out Msg)}
    {promise : Promise}
    (hpick :
      pick ((Experiment.dispatch call.req call.now).run
        { cfg.app with unreliable := true }
        { promises := doc.toList.map (·.1) }) 0 = (res, after, outs))
    (hdoc : DocAtKey call.req.key doc)
    (hpromise : after.promises.find? (·.id == call.req.key) = some promise)
    :
    Candidate.Valid cfg
      ⟨call.client, call.id, call.req, call.now, tries, doc,
        res, after, outs, promise⟩ :=
  ⟨hpick.symm, hpromise, dispatch_changed_singleton hdoc hpick hpromise⟩

theorem Candidate.onlyNotifies {cfg : Storage.Config} {candidate : Candidate}
    (h : candidate.Valid cfg) : OnlyNotifies candidate.outs := by
  apply EmitsOnlyNotifies.dispatch candidate.req candidate.now
    { cfg.app with unreliable := true }
    { promises := candidate.doc.toList.map (·.1) }
    (candidate.res, candidate.after, candidate.outs)
  rw [h.1]
  exact pick_mem _ _

abbrev AbstractMessage := Experiment.Proc × Experiment.Proc × Msg
abbrev ConcreteMessage := Network.Who × Network.Who × CMsg

def Call.token (call : Call) : AbstractMessage :=
  (.client call.client, .server, .req call.id call.now call.req)

def responseToken (client : Addr) (id : CallId) (response : Response) :
    AbstractMessage :=
  (.server, .client client, .res id response)

def outputTokens (outs : List (Out Msg)) : List AbstractMessage :=
  (sends outs).map fun (client, message) => (.server, .client client, message)

theorem emits_outputs_response (outs : List (Out Msg)) (client : Addr)
    (id : CallId) (response : Response) (event : Experiment.Event Msg) :
    Experiment.emits .server event
      (outs ++ [.send client (.res id response)]) =
      outputTokens outs ++ [responseToken client id response] := by
  simp [Experiment.emits, outputTokens, responseToken, sends,
    List.map_append]

inductive WriteStage where
  | pending
  | served
  | lost
  | shed

def Candidate.stageTokens (candidate : Candidate) : WriteStage → List AbstractMessage
  | .pending => [candidate.call.token]
  | .served =>
      outputTokens candidate.outs ++
        [responseToken candidate.client candidate.id candidate.res]
  | .lost =>
      outputTokens candidate.outs ++
        [responseToken candidate.client candidate.id ⟨503, none⟩]
  | .shed => [responseToken candidate.client candidate.id ⟨503, none⟩]

def mailboxTokens (mailbox : List (Addr × CMsg)) : List AbstractMessage :=
  mailbox.filterMap fun
    | (client, .app (.req id now request)) =>
        some (.client client, .server, .req id now request)
    | _ => none

def appToken : ConcreteMessage → Option AbstractMessage
  | (_, .client client, .app message) =>
      some (.server, .client client, message)
  | (.client client, .proc _, .app message) =>
      some (.client client, .server, message)
  | (.proc sender, .proc _, .app (.req id now request)) =>
      some (.client sender, .server, .req id now request)
  | (.proc _, .proc client, .app message) =>
      some (.server, .client client, message)
  | _ => none

def appTokens (net : List ConcreteMessage) : List AbstractMessage :=
  net.filterMap appToken

theorem appTokens_append (left right : List ConcreteMessage) :
    appTokens (left ++ right) = appTokens left ++ appTokens right :=
  List.filterMap_append

def routedMessages (states : List (Addr × Local)) (source : Addr)
    (messages : List (Addr × CMsg)) : List ConcreteMessage :=
  messages.map fun (destination, message) =>
    (.proc source,
      (⟨[], states, 0⟩ : Network.Conf system).route destination, message)

def routedOuts (states : List (Addr × Local)) (source : Addr)
    (outs : List (Out CMsg)) : List ConcreteMessage :=
  routedMessages states source (sends outs)

theorem routedMessages_append (states : List (Addr × Local)) (source : Addr)
    (left right : List (Addr × CMsg)) :
    routedMessages states source (left ++ right) =
      routedMessages states source left ++ routedMessages states source right := by
  simp [routedMessages]

theorem routedOuts_append (states : List (Addr × Local)) (source : Addr)
    (left right : List (Out CMsg)) :
    routedOuts states source (left ++ right) =
      routedOuts states source left ++ routedOuts states source right := by
  simp [routedOuts, routedMessages, sends]

theorem appTokens_routedNotifies
    (states : List (Addr × Local)) (source : Addr)
    (messages : List (Addr × Msg))
    (h : ∀ address message, (address, message) ∈ messages →
      ∃ promise, message = .notify promise) :
    appTokens
      (routedMessages states source
        (messages.map fun (address, message) => (address, .app message))) =
      messages.map fun (address, message) =>
        ((.server, .client address, message) : AbstractMessage) := by
  induction messages with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨address, message⟩ := entry
    obtain ⟨promise, rfl⟩ := h address message (List.mem_cons_self)
    have hrest : ∀ address message, (address, message) ∈ rest →
        ∃ promise, message = .notify promise :=
      fun address message hm => h address message (List.mem_cons_of_mem _ hm)
    simp only [List.map_cons]
    rw [show
      routedMessages states source
          ((address, CMsg.app (.notify promise)) ::
            rest.map fun entry => (entry.1, CMsg.app entry.2)) =
        (.proc source,
          (⟨[], states, 0⟩ : Network.Conf system).route address,
          .app (.notify promise)) ::
          routedMessages states source
            (rest.map fun entry => (entry.1, CMsg.app entry.2)) from rfl]
    by_cases hp :
        (⟨[], states, 0⟩ : Network.Conf system).isProc address = true
    · rw [show
        (⟨[], states, 0⟩ : Network.Conf system).route address =
          .proc address by simp [Network.Conf.route, hp]]
      change
        ((.server, .client address, .notify promise) : AbstractMessage) ::
            appTokens
              (routedMessages states source
                (rest.map fun entry => (entry.1, .app entry.2))) =
          ((.server, .client address, .notify promise) : AbstractMessage) ::
            rest.map (fun entry =>
              ((.server, .client entry.1, entry.2) : AbstractMessage))
      rw [ih hrest]
    · have hpf :
          (⟨[], states, 0⟩ : Network.Conf system).isProc address = false := by
        simpa only [Bool.not_eq_true] using hp
      rw [show
        (⟨[], states, 0⟩ : Network.Conf system).route address =
          .client address by simp [Network.Conf.route, hpf]]
      change
        ((.server, .client address, .notify promise) : AbstractMessage) ::
            appTokens
              (routedMessages states source
                (rest.map fun entry => (entry.1, .app entry.2))) =
          ((.server, .client address, .notify promise) : AbstractMessage) ::
            rest.map (fun entry =>
              ((.server, .client entry.1, entry.2) : AbstractMessage))
      rw [ih hrest]

theorem appTokens_routedResponse
    (states : List (Addr × Local)) (source client : Addr)
    (id : CallId) (response : Response) :
    appTokens
      (routedOuts states source
        [.send client (.app (.res id response))]) =
      [responseToken client id response] := by
  change
    (appToken (.proc source,
      (⟨[], states, 0⟩ : Network.Conf system).route client,
      .app (.res id response))).toList =
      [responseToken client id response]
  unfold Network.Conf.route
  split <;> rfl

theorem appTokens_routedOutputs
    (states : List (Addr × Local)) (source : Addr)
    (outs : List (Out Msg)) (h : OnlyNotifies outs) :
    appTokens
      (routedOuts states source
        ((sends outs).map fun (address, message) =>
          .send address (.app message))) =
      outputTokens outs := by
  have hsends (messages : List (Addr × Msg)) :
      sends (messages.map fun (address, message) =>
        Out.send address (CMsg.app message)) =
        messages.map fun (address, message) => (address, CMsg.app message) := by
    induction messages with
    | nil => rfl
    | cons entry rest ih =>
      obtain ⟨address, message⟩ := entry
      change
        (address, CMsg.app message) ::
            sends (rest.map fun entry =>
              Out.send entry.1 (CMsg.app entry.2)) =
          (address, CMsg.app message) ::
            rest.map fun entry => (entry.1, CMsg.app entry.2)
      rw [ih]
  unfold routedOuts outputTokens
  rw [hsends]
  rw [appTokens_routedNotifies]
  intro address message hm
  exact h address message hm

theorem mailboxTokens_append_nonrequest {mailbox : List (Addr × CMsg)}
    {sender : Addr} {message : Msg}
    (hm : isRequest sender (.app message) = false) :
    mailboxTokens (mailbox ++ [(sender, .app message)]) =
      mailboxTokens mailbox := by
  cases message <;> simp_all [mailboxTokens, isRequest]

theorem mailboxTokens_append_request (mailbox : List (Addr × CMsg))
    (sender : Addr) (id : CallId) (now : Time) (request : Request) :
    mailboxTokens (mailbox ++ [(sender, .app (.req id now request))]) =
      mailboxTokens mailbox ++
        [Call.token ⟨sender, id, request, now⟩] := by
  simp [mailboxTokens, Call.token]

theorem mailboxTokens_take_request_perm
    {mailbox rest : List (Addr × CMsg)} {client : Addr}
    {id : CallId} {requestNow : Time} {request : Request}
    (happ : AppOnly mailbox)
    (htake : take? isRequest mailbox =
      some (client, .app (.req id requestNow request), rest)) :
    (mailboxTokens rest ++
      [Call.token ⟨client, id, request, requestNow⟩]).Perm
      (mailboxTokens mailbox) := by
  induction mailbox generalizing rest with
  | nil => simp [take?] at htake
  | cons entry tail ih =>
    obtain ⟨sender, message⟩ := entry
    by_cases ha : isRequest sender message = true
    · simp only [take?, ha, if_true, Option.some.injEq,
        Prod.mk.injEq] at htake
      obtain ⟨rfl, rfl, rfl⟩ := htake
      simp [mailboxTokens, Call.token, List.perm_append_comm]
    · have haf : isRequest sender message = false := by
        simpa only [Bool.not_eq_true] using ha
      simp only [take?, haf, Bool.false_eq_true, if_false] at htake
      obtain ⟨found, hfound, heq⟩ := Option.map_eq_some_iff.mp htake
      obtain ⟨selected, selectedMessage, tailRest⟩ := found
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      have happTail : AppOnly tail :=
        fun a m hm => happ a m (List.mem_cons_of_mem _ hm)
      have hp := ih happTail hfound
      obtain ⟨app, rfl⟩ := happ sender message (List.mem_cons_self)
      cases app with
      | req callId now req => simp [isRequest] at haf
      | res callId response =>
        simpa [mailboxTokens] using hp
      | notify promise =>
        simpa [mailboxTokens] using hp

theorem perm_insert_before_suffix (before after : List α) (value : α) :
    (before ++ [value] ++ after).Perm
      ((before ++ after) ++ [value]) := by
  simpa [List.append_assoc] using
    (List.Perm.append_left before
      (List.perm_append_comm : ([value] ++ after).Perm (after ++ [value])))

def protocolMessages (net : List ConcreteMessage) : List ConcreteMessage :=
  net.filter fun (_, _, message) =>
    match message with
    | .app _ => false
    | _ => true

theorem protocolMessages_append (left right : List ConcreteMessage) :
    protocolMessages (left ++ right) =
      protocolMessages left ++ protocolMessages right := by
  simp [protocolMessages]

theorem protocolMessages_routedApps
    (states : List (Addr × Local)) (source : Addr)
    (messages : List (Addr × Msg)) :
    protocolMessages
      (routedMessages states source
        (messages.map fun (address, message) => (address, .app message))) = [] := by
  induction messages with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨address, message⟩ := entry
    simp only [List.map_cons]
    change protocolMessages
      ((.proc source,
        (⟨[], states, 0⟩ : Network.Conf system).route address,
        .app message) ::
        routedMessages states source
          (rest.map fun entry => (entry.1, .app entry.2))) = []
    simpa [protocolMessages] using ih

theorem protocolMessages_routedResponse
    (states : List (Addr × Local)) (source client : Addr)
    (id : CallId) (response : Response) :
    protocolMessages
      (routedOuts states source
        [.send client (.app (.res id response))]) = [] := by
  simp [routedOuts, routedMessages, sends, protocolMessages]

theorem protocolMessages_routedOutputs
    (states : List (Addr × Local)) (source : Addr)
    (outs : List (Out Msg)) :
    protocolMessages
      (routedOuts states source
        ((sends outs).map fun (address, message) =>
          .send address (.app message))) = [] := by
  have hsends (messages : List (Addr × Msg)) :
      sends (messages.map fun (address, message) =>
        Out.send address (CMsg.app message)) =
        messages.map fun (address, message) => (address, CMsg.app message) := by
    induction messages with
    | nil => rfl
    | cons entry rest ih =>
      obtain ⟨address, message⟩ := entry
      change
        (address, CMsg.app message) ::
            sends (rest.map fun entry =>
              Out.send entry.1 (CMsg.app entry.2)) =
          (address, CMsg.app message) ::
            rest.map fun entry => (entry.1, CMsg.app entry.2)
      rw [ih]
  unfold routedOuts
  rw [hsends]
  exact protocolMessages_routedApps states source _

def optionList : Option α → List α
  | none => []
  | some value => [value]

def Covers (required actual : List AbstractMessage) : Prop :=
  ∃ extra, actual.Perm (required ++ extra)

theorem perm_append_cons_head (before after : List α) (value : α) :
    (before ++ value :: after).Perm (value :: before ++ after) := by
  simpa [List.append_assoc] using
    (List.Perm.append_right after
      (List.perm_append_comm :
        (before ++ [value]).Perm ([value] ++ before)))

theorem Perm.cancel_exposed {before after rest : List α} {value : α}
    (h : (before ++ value :: after).Perm (value :: rest)) :
    (before ++ after).Perm rest := by
  apply List.Perm.cons_inv
  exact (perm_append_cons_head before after value).symm.trans h

namespace Covers

theorem refl (required : List AbstractMessage) : Covers required required :=
  ⟨[], by simp⟩

theorem of_perm {required required' actual : List AbstractMessage}
    (h : required.Perm required') (hc : Covers required actual) :
    Covers required' actual := by
  obtain ⟨extra, hp⟩ := hc
  exact ⟨extra, hp.trans (h.append_right extra)⟩

theorem actual_perm {required actual actual' : List AbstractMessage}
    (h : actual.Perm actual') (hc : Covers required actual) :
    Covers required actual' := by
  obtain ⟨extra, hp⟩ := hc
  exact ⟨extra, h.symm.trans hp⟩

theorem weaken {required extra actual : List AbstractMessage}
    (hc : Covers (required ++ extra) actual) :
    Covers required actual := by
  obtain ⟨rest, hp⟩ := hc
  exact ⟨extra ++ rest, by simpa [List.append_assoc] using hp⟩

theorem append_both {required actual added : List AbstractMessage}
    (hc : Covers required actual) :
    Covers (required ++ added) (actual ++ added) := by
  obtain ⟨extra, hp⟩ := hc
  refine ⟨extra, (hp.append_right added).trans ?_⟩
  simpa [List.append_assoc] using
    (List.Perm.append_left required
      (List.perm_append_comm :
        (extra ++ added).Perm (added ++ extra)))

theorem append_actual {required actual added : List AbstractMessage}
    (hc : Covers required actual) :
    Covers required (actual ++ added) := by
  obtain ⟨extra, hp⟩ := hc
  exact ⟨extra ++ added, by simpa [List.append_assoc] using hp.append_right added⟩

theorem insert_both {left right actual added : List AbstractMessage}
    (hc : Covers (left ++ right) actual) :
    Covers (left ++ added ++ right) (actual ++ added) := by
  apply of_perm _ (append_both (added := added) hc)
  simpa [List.append_assoc] using
    (List.Perm.append_left left
      (List.perm_append_comm : (right ++ added).Perm (added ++ right)))

theorem drop_middle {before after actual : List AbstractMessage}
    {value : AbstractMessage}
    (hc : Covers (before ++ value :: after) actual) :
    Covers (before ++ after) actual := by
  apply weaken (extra := [value])
  apply of_perm _ hc
  simpa [List.append_assoc, List.cons_append] using
    (List.Perm.append_left before
      (List.perm_append_comm : ([value] ++ after).Perm (after ++ [value])))

theorem consume {before after actual : List AbstractMessage}
    {value : AbstractMessage}
    (hc : Covers (before ++ value :: after) actual) :
    ∃ (pre post : List AbstractMessage),
      (actual = pre ++ (value :: post)) ∧
      Covers (before ++ after) (pre ++ post) := by
  obtain ⟨extra, hp⟩ := hc
  have hmem : value ∈ actual := by
    apply (hp.mem_iff).2
    simp
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hmem
  refine ⟨pre, post, rfl, ?_⟩
  refine ⟨extra, ?_⟩
  have hp' : (pre ++ value :: post).Perm
      (before ++ value :: (after ++ extra)) := by
    simpa [List.append_assoc] using hp
  have hall : (value :: pre ++ post).Perm
      (value :: before ++ (after ++ extra)) :=
    (perm_append_cons_head pre post value).symm.trans
      (hp'.trans (perm_append_cons_head before (after ++ extra) value))
  simpa [List.append_assoc] using List.Perm.cons_inv hall

end Covers

inductive NodeRep (cfg : Storage.Config) (store : Store) (address : Addr) :
    Running Storage.Config Nat CMsg →
    Option ConcreteMessage → List AbstractMessage → Prop where
  | idle {next mailbox} :
      AppOnly mailbox →
      take? isRequest mailbox = none →
      NodeRep cfg store address ⟨next, mailbox, node⟩ none
        (mailboxTokens mailbox)
  | loadingGet {call : Call} {tries op next mailbox} :
      AppOnly mailbox →
      next = op + 1 →
      take? (answers op) mailbox = none →
      NodeRep cfg store address
        ⟨next, mailbox,
          loadK tries (call.retry tries)
            call.client call.id call.req call.now op⟩
        (some (.proc address, .proc cfg.store, .get op call.req.key))
        (mailboxTokens mailbox ++ [call.token])
  | loadingGot {call : Call} {tries op next mailbox doc} :
      AppOnly mailbox →
      next = op + 1 →
      take? (answers op) mailbox = none →
      (∃ res after outs,
        pick ((Experiment.dispatch call.req call.now).run
          { cfg.app with unreliable := true }
          { promises := doc.toList.map (·.1) }) 0 = (res, after, outs) ∧
        after ≠ { promises := doc.toList.map (·.1) }) →
      Snapshot store call.req.key doc →
      DocAtKey call.req.key doc →
      NodeRep cfg store address
        ⟨next, mailbox,
          loadK tries (call.retry tries)
            call.client call.id call.req call.now op⟩
        (some (.proc cfg.store, .proc address, .got op doc))
        (mailboxTokens mailbox ++ [call.token])
  | loadingDone {call : Call} {tries op next mailbox doc}
      {res : Response} {after : Experiment.State} {outs : List (Out Msg)} :
      AppOnly mailbox →
      next = op + 1 →
      take? (answers op) mailbox = none →
      pick ((Experiment.dispatch call.req call.now).run
        { cfg.app with unreliable := true }
        { promises := doc.toList.map (·.1) }) 0 = (res, after, outs) →
      after = { promises := doc.toList.map (·.1) } →
      Snapshot store call.req.key doc →
      DocAtKey call.req.key doc →
      NodeRep cfg store address
        ⟨next, mailbox,
          loadK tries (call.retry tries)
            call.client call.id call.req call.now op⟩
        (some (.proc cfg.store, .proc address, .got op doc))
        (mailboxTokens mailbox ++ outputTokens outs ++
          [responseToken call.client call.id res])
  | writingPut {candidate : Candidate} {op next mailbox} :
      AppOnly mailbox →
      next = op + 1 →
      take? (answers op) mailbox = none →
      candidate.Valid cfg →
      Snapshot store candidate.req.key candidate.doc →
      NodeRep cfg store address
        ⟨next, mailbox,
          writeK candidate.tries (candidate.call.retry candidate.tries)
            candidate op⟩
        (some (.proc address, .proc cfg.store,
          .put op candidate.req.key candidate.promise (candidate.doc.map (·.2))))
        (mailboxTokens mailbox ++ candidate.stageTokens .pending)
  | writingConflict {candidate : Candidate} {op next mailbox} :
      AppOnly mailbox →
      next = op + 1 →
      take? (answers op) mailbox = none →
      candidate.Valid cfg →
      Snapshot store candidate.req.key candidate.doc →
      NodeRep cfg store address
        ⟨next, mailbox,
          writeK candidate.tries (candidate.call.retry candidate.tries)
            candidate op⟩
        (some (.proc cfg.store, .proc address, .conflict op))
        (mailboxTokens mailbox ++ candidate.stageTokens .pending)
  | writingServed {candidate : Candidate} {op next mailbox} :
      AppOnly mailbox →
      next = op + 1 →
      take? (answers op) mailbox = none →
      candidate.Valid cfg →
      NodeRep cfg store address
        ⟨next, mailbox,
          writeK candidate.tries (candidate.call.retry candidate.tries)
            candidate op⟩
        (some (.proc cfg.store, .proc address, .written op))
        (mailboxTokens mailbox ++ candidate.stageTokens .served)
  | writingLost {candidate : Candidate} {op next mailbox} :
      AppOnly mailbox →
      next = op + 1 →
      take? (answers op) mailbox = none →
      candidate.Valid cfg →
      NodeRep cfg store address
        ⟨next, mailbox,
          writeK candidate.tries (candidate.call.retry candidate.tries)
            candidate op⟩
        (some (.proc cfg.store, .proc address, .failed op))
        (mailboxTokens mailbox ++ candidate.stageTokens .lost)
  | writingShed {candidate : Candidate} {op next mailbox} :
      AppOnly mailbox →
      next = op + 1 →
      take? (answers op) mailbox = none →
      candidate.Valid cfg →
      Snapshot store candidate.req.key candidate.doc →
      NodeRep cfg store address
        ⟨next, mailbox,
          writeK candidate.tries (candidate.call.retry candidate.tries)
            candidate op⟩
        (some (.proc cfg.store, .proc address, .failed op))
        (mailboxTokens mailbox ++ candidate.stageTokens .shed)

inductive RestartRep (cfg : Storage.Config) (store : Store) (address : Addr) :
    Running Storage.Config Nat CMsg → List (Out CMsg) →
      Option ConcreteMessage → List AbstractMessage → Prop where
  | idle {next mailbox} :
      AppOnly mailbox →
      take? isRequest mailbox = none →
      RestartRep cfg store address ⟨next, mailbox, node⟩ [] none
        (mailboxTokens mailbox)
  | loading {call : Call} {op next mailbox} :
      AppOnly mailbox →
      next = op + 1 →
      take? (answers op) mailbox = none →
      RestartRep cfg store address
        ⟨next, mailbox,
          loadK cfg.retries (call.retry cfg.retries)
            call.client call.id call.req call.now op⟩
        [.send cfg.store (.get op call.req.key)]
        (some (.proc address, .proc cfg.store, .get op call.req.key))
        (mailboxTokens mailbox ++ [call.token])

theorem RestartRep.nodeRep {cfg : Storage.Config} {store : Store}
    {address : Addr} {running : Running Storage.Config Nat CMsg}
    {outs : List (Out CMsg)} {wire : Option ConcreteMessage}
    {tokens : List AbstractMessage}
    (h : RestartRep cfg store address running outs wire tokens) :
    NodeRep cfg store address running wire tokens := by
  cases h with
  | idle happ hn => exact .idle happ hn
  | loading happ hnext hn => exact .loadingGet happ hnext hn

theorem RestartRep.routedResponse {cfg : Storage.Config} {store : Store}
    {address : Addr} {running : Running Storage.Config Nat CMsg}
    {rest : List (Out CMsg)} {wire : Option ConcreteMessage}
    {tokens : List AbstractMessage} {states : List (Addr × Local)}
    {client : Addr} {id : CallId} {response : Response}
    (hroute :
      (⟨[], states, 0⟩ : Network.Conf system).route cfg.store =
        .proc cfg.store)
    (h : RestartRep cfg store address running rest wire tokens) :
    protocolMessages
        (routedOuts states address
          (.send client (.app (.res id response)) :: rest)) =
        optionList wire ∧
      appTokens
        (routedOuts states address
          (.send client (.app (.res id response)) :: rest)) =
        [responseToken client id response] := by
  have hsplit :
      (.send client (.app (.res id response)) :: rest) =
        [.send client (.app (.res id response))] ++ rest := rfl
  rw [hsplit, routedOuts_append, protocolMessages_append, appTokens_append,
    protocolMessages_routedResponse, appTokens_routedResponse]
  cases h with
  | idle happ hnone =>
    simp [routedOuts, routedMessages, sends, protocolMessages,
      appTokens, optionList]
  | @loading call op next mailbox happ hnext hnone =>
    simp [routedOuts, routedMessages, sends, protocolMessages,
      appTokens, appToken, optionList, hroute]

theorem advance_node_restart {cfg : Storage.Config} {store : Store}
    {address : Addr} {mailbox : List (Addr × CMsg)} {next : Nat}
    {stepNow : Time} (happ : AppOnly mailbox) (fuel : Nat) :
    ∃ running outs wire tokens,
      advance node cfg stepNow (fuel + 7) next mailbox node =
        [(running, outs)] ∧
      RestartRep cfg store address running outs wire tokens ∧
      tokens.Perm (mailboxTokens mailbox) := by
  cases htake : take? isRequest mailbox with
  | none =>
    refine ⟨⟨next, mailbox, node⟩, [], none, mailboxTokens mailbox,
      ?_, .idle happ htake, List.Perm.refl _⟩
    simpa [Nat.add_assoc] using advance_node_none (cfg := cfg)
      (next := next) (stepNow := stepNow) (fuel + 6) htake
  | some found =>
    obtain ⟨client, message, rest⟩ := found
    obtain ⟨id, requestNow, request, rfl⟩ :=
      request_of_take_isRequest htake
    have hrest := AppOnly.rest_of_take happ htake
    let call : Call := ⟨client, id, request, requestNow⟩
    refine ⟨⟨next + 1, rest,
      loadK cfg.retries (call.retry cfg.retries)
        client id request requestNow next⟩,
      [.send cfg.store (.get next request.key)],
      some (.proc address, .proc cfg.store, .get next request.key),
      mailboxTokens rest ++ [call.token], ?_, ?_, ?_⟩
    · simpa [call] using advance_node_request (cfg := cfg) fuel htake hrest
    · exact .loading hrest rfl
        (answers_none_of_appOnly rest next hrest)
    · simpa [call] using mailboxTokens_take_request_perm happ htake

theorem writing_written_restart {cfg : Storage.Config} {store : Store}
    {address : Addr} {mailbox : List (Addr × CMsg)}
    {candidate : Candidate} {op next : Nat}
    (happ : AppOnly mailbox) (hn : take? (answers op) mailbox = none)
    (sender : Addr) (stepNow : Time) :
    ∃ running rest wire tokens,
      (toStep node 64 sender (.written op) stepNow cfg
        (⟨next, mailbox,
          writeK candidate.tries (candidate.call.retry candidate.tries)
            candidate op⟩ : Running Storage.Config Nat CMsg)).val =
        [((), running,
          .send candidate.client (.app (.res candidate.id candidate.res)) ::
            (sends candidate.outs).map (fun (a, m) => .send a (.app m)) ++
              rest)] ∧
      RestartRep cfg store address running rest wire tokens ∧
      tokens.Perm (mailboxTokens mailbox) := by
  obtain ⟨running, rest, wire, tokens, hr, hrep, htokens⟩ :=
    advance_node_restart (cfg := cfg) (store := store)
      (address := address) (next := next) (stepNow := stepNow) happ 53
  refine ⟨running, rest, wire, tokens, ?_, hrep, htokens⟩
  have htake : take? (answers op) (mailbox ++ [(sender, .written op)]) =
      some (sender, .written op, mailbox) :=
    take?_append_match hn (by simp [answers])
  unfold toStep writeK Proc.recv answer sendAll Proc.send Proc.emitAllNow
  change (someOr ((advance node cfg stepNow (63 + 1) next
    (mailbox ++ [(sender, .written op)]) (.receive (answers op) _)).map _)
    _).val = _
  rw [advance_receive_some (a := sender) (m := .written op) (h := htake)]
  simp only [Proc.bind]
  change (someOr ((advance node cfg stepNow (62 + 1) next mailbox
    (.emit (.send candidate.client (.app (.res candidate.id candidate.res)))
      (.emitMany ((sends candidate.outs).map fun (a, m) => .send a (.app m))
        (.pure ())))).map _) _).val = _
  rw [advance_emit, advance_emitMany]
  rw [show advance node cfg stepNow 61 next mailbox (.pure ()) =
    advance node cfg stepNow 60 next mailbox node from rfl]
  rw [show 60 = 53 + 7 by omega, hr]
  rfl

theorem writing_failed_restart {cfg : Storage.Config} {store : Store}
    {address : Addr} {mailbox : List (Addr × CMsg)}
    {candidate : Candidate} {op next : Nat}
    (happ : AppOnly mailbox) (hn : take? (answers op) mailbox = none)
    (sender : Addr) (stepNow : Time) :
    ∃ running rest wire tokens,
      (toStep node 64 sender (.failed op) stepNow cfg
        (⟨next, mailbox,
          writeK candidate.tries (candidate.call.retry candidate.tries)
            candidate op⟩ : Running Storage.Config Nat CMsg)).val =
        [((), running,
          .send candidate.client (.app (.res candidate.id ⟨503, none⟩)) ::
            rest)] ∧
      RestartRep cfg store address running rest wire tokens ∧
      tokens.Perm (mailboxTokens mailbox) := by
  obtain ⟨running, rest, wire, tokens, hr, hrep, htokens⟩ :=
    advance_node_restart (cfg := cfg) (store := store)
      (address := address) (next := next) (stepNow := stepNow) happ 54
  refine ⟨running, rest, wire, tokens, ?_, hrep, htokens⟩
  have htake : take? (answers op) (mailbox ++ [(sender, .failed op)]) =
      some (sender, .failed op, mailbox) :=
    take?_append_match hn (by simp [answers])
  unfold toStep writeK Proc.recv answer Proc.send
  change (someOr ((advance node cfg stepNow (63 + 1) next
    (mailbox ++ [(sender, .failed op)]) (.receive (answers op) _)).map _)
    _).val = _
  rw [advance_receive_some (a := sender) (m := .failed op) (h := htake)]
  simp only [Proc.bind]
  change (someOr ((advance node cfg stepNow (62 + 1) next mailbox
    (.emit (.send candidate.client (.app (.res candidate.id ⟨503, none⟩)))
      (.pure ()))).map _) _).val = _
  rw [advance_emit]
  rw [show advance node cfg stepNow 62 next mailbox (.pure ()) =
    advance node cfg stepNow 61 next mailbox node from rfl]
  rw [show 61 = 54 + 7 by omega, hr]
  rfl


set_option maxHeartbeats 1000000 in
theorem loading_got_unchanged_restart {cfg : Storage.Config}
    {store : Store} {address : Addr}
    {mailbox : List (Addr × CMsg)} {call : Call} {tries op next : Nat}
    {doc : Option (Promise × Version)} {res : Response}
    {after : Experiment.State} {outs : List (Out Msg)}
    (happ : AppOnly mailbox) (hn : take? (answers op) mailbox = none)
    (hpick :
      pick ((Experiment.dispatch call.req call.now).run
        { cfg.app with unreliable := true }
        { promises := doc.toList.map (·.1) }) 0 = (res, after, outs))
    (hunchanged : after = { promises := doc.toList.map (·.1) })
    (sender : Addr) (stepNow : Time) :
    ∃ r rest wire tokens,
      (toStep node 64 sender (.got op doc) stepNow cfg
        (⟨next, mailbox,
          loadK tries (call.retry tries)
            call.client call.id call.req call.now op⟩ :
          Running Storage.Config Nat CMsg)).val =
        [((), r, notes outs ++
          .send call.client (.app (.res call.id res)) ::
            (sends outs).map (fun (a, m) => .send a (.app m)) ++ rest)] ∧
      RestartRep cfg store address r rest wire tokens ∧
      tokens.Perm (mailboxTokens mailbox) := by
  subst after
  obtain ⟨r, rest, wire, tokens, hr, hc, htokens⟩ :=
    advance_node_restart (cfg := cfg) (store := store) (address := address)
      (next := next) (stepNow := stepNow) happ 51
  refine ⟨r, rest, wire, tokens, ?_, hc, htokens⟩
  have htake : take? (answers op) (mailbox ++ [(sender, .got op doc)]) =
      some (sender, .got op doc, mailbox) :=
    take?_append_match hn (by simp [answers])
  unfold toStep loadK Proc.recv
  change (someOr ((advance node cfg stepNow (63 + 1) next
    (mailbox ++ [(sender, .got op doc)]) (.receive (answers op) _)).map _)
    _).val = _
  rw [advance_receive_some (a := sender) (m := .got op doc) (h := htake)]
  simp only [Proc.bind]
  change (someOr ((advance node cfg stepNow (62 + 1) next mailbox
    (.ask fun cfg' => decideK tries (call.retry tries) call.client call.id
      call.req call.now cfg' doc { promises := doc.toList.map (·.1) }
      (pick ((Experiment.dispatch call.req call.now).run
        { cfg'.app with unreliable := true }
        { promises := doc.toList.map (·.1) }) 0))).map _) _).val = _
  rw [advance_ask, hpick]
  unfold decideK note answer sendAll Proc.send Proc.emitAllNow
  simp only [beq_self_eq_true, if_true]
  change (someOr ((advance node cfg stepNow (61 + 1) next mailbox
    (.emitMany (notes outs)
      (.emit (.send call.client (.app (.res call.id res)))
        (.emitMany ((sends outs).map fun (a, m) => .send a (.app m))
          (.pure ()))))).map _) _).val = _
  rw [advance_emitMany, advance_emit, advance_emitMany]
  rw [show advance node cfg stepNow 59 next mailbox (.pure ()) =
    advance node cfg stepNow 58 next mailbox node from rfl]
  rw [show 58 = 51 + 7 by omega, hr]
  simp [List.append_assoc, someOr]

theorem writing_conflict_exhausted_restart {cfg : Storage.Config}
    {store : Store} {address : Addr}
    {mailbox : List (Addr × CMsg)} {candidate : Candidate}
    {op next : Nat}
    (happ : AppOnly mailbox) (hn : take? (answers op) mailbox = none)
    (htries : candidate.tries = 0) (sender : Addr) (stepNow : Time) :
    ∃ running rest wire tokens,
      (toStep node 64 sender (.conflict op) stepNow cfg
        (⟨next, mailbox,
          writeK candidate.tries (candidate.call.retry candidate.tries)
            candidate op⟩ : Running Storage.Config Nat CMsg)).val =
        [((), running,
          .send candidate.client (.app (.res candidate.id ⟨503, none⟩)) ::
            rest)] ∧
      RestartRep cfg store address running rest wire tokens ∧
      tokens.Perm (mailboxTokens mailbox) := by
  obtain ⟨running, rest, wire, tokens, hr, hrep, htokens⟩ :=
    advance_node_restart (cfg := cfg) (store := store)
      (address := address) (next := next) (stepNow := stepNow) happ 54
  refine ⟨running, rest, wire, tokens, ?_, hrep, htokens⟩
  have htake :
      take? (answers op) (mailbox ++ [(sender, .conflict op)]) =
        some (sender, .conflict op, mailbox) :=
    take?_append_match hn (by simp [answers])
  unfold toStep writeK Proc.recv answer Proc.send
  change (someOr ((advance node cfg stepNow (63 + 1) next
    (mailbox ++ [(sender, .conflict op)]) (.receive (answers op) _)).map _)
    _).val = _
  rw [advance_receive_some (a := sender) (m := .conflict op) (h := htake)]
  simp only [Proc.bind]
  rw [htries]
  change (someOr ((advance node cfg stepNow (62 + 1) next mailbox
    (.emit (.send candidate.client (.app (.res candidate.id ⟨503, none⟩)))
      (.pure ()))).map _) _).val = _
  rw [advance_emit]
  rw [show advance node cfg stepNow 62 next mailbox (.pure ()) =
    advance node cfg stepNow 61 next mailbox node from rfl]
  rw [show 61 = 54 + 7 by omega, hr]
  rfl

theorem writing_conflict_retry_rep {cfg : Storage.Config}
    {store : Store} {address : Addr}
    {mailbox : List (Addr × CMsg)} {candidate : Candidate}
    {op next k : Nat}
    (happ : AppOnly mailbox) (hn : take? (answers op) mailbox = none)
    (htries : candidate.tries = k + 1) (sender : Addr) (stepNow : Time) :
    let running : Running Storage.Config Nat CMsg :=
      ⟨next + 1, mailbox,
        loadK k (candidate.call.retry k)
          candidate.client candidate.id candidate.req candidate.now next⟩
    let wire : ConcreteMessage :=
      (.proc address, .proc cfg.store, .get next candidate.req.key)
    (toStep node 64 sender (.conflict op) stepNow cfg
      (⟨next, mailbox,
        writeK candidate.tries (candidate.call.retry candidate.tries)
          candidate op⟩ : Running Storage.Config Nat CMsg)).val =
      [((), running, [.send cfg.store (.get next candidate.req.key)])] ∧
    NodeRep cfg store address running (some wire)
      (mailboxTokens mailbox ++ [candidate.call.token]) := by
  dsimp
  constructor
  · exact writing_conflict_retry_run happ hn htries sender stepNow
  · exact .loadingGet happ rfl
      (answers_none_of_appOnly mailbox next happ)

set_option maxHeartbeats 1000000 in
theorem loading_got_changed_rep {cfg : Storage.Config}
    {store : Store} {address : Addr}
    {mailbox : List (Addr × CMsg)} {call : Call}
    {tries op next : Nat} {doc : Option (Promise × Version)}
    {res : Response} {after : Experiment.State} {outs : List (Out Msg)}
    {promise : Promise}
    (happ : AppOnly mailbox) (hn : take? (answers op) mailbox = none)
    (hpick :
      pick ((Experiment.dispatch call.req call.now).run
        { cfg.app with unreliable := true }
        { promises := doc.toList.map (·.1) }) 0 = (res, after, outs))
    (hchanged : (after == { promises := doc.toList.map (·.1) }) = false)
    (hpromise :
      after.promises.find? (·.id == call.req.key) = some promise)
    (hsnapshot : Snapshot store call.req.key doc)
    (hdoc : DocAtKey call.req.key doc)
    (sender : Addr) (stepNow : Time) :
    let candidate : Candidate :=
      ⟨call.client, call.id, call.req, call.now, tries, doc,
        res, after, outs, promise⟩
    let running : Running Storage.Config Nat CMsg :=
      ⟨next + 1, mailbox,
        writeK tries (call.retry tries) candidate next⟩
    let wire : ConcreteMessage :=
      (.proc address, .proc cfg.store,
        .put next call.req.key promise (doc.map (·.2)))
    (toStep node 64 sender (.got op doc) stepNow cfg
      (⟨next, mailbox,
        loadK tries (call.retry tries)
          call.client call.id call.req call.now op⟩ :
        Running Storage.Config Nat CMsg)).val =
      [((), running, notes outs ++
        [.send cfg.store (.put next call.req.key promise (doc.map (·.2)))])] ∧
    NodeRep cfg store address running (some wire)
      (mailboxTokens mailbox ++ candidate.stageTokens .pending) := by
  dsimp
  constructor
  · exact loading_got_changed_run happ hn hpick hchanged hpromise sender stepNow
  · exact .writingPut happ rfl
      (answers_none_of_appOnly mailbox next happ)
      (changed_candidate_valid hpick hdoc hpromise) hsnapshot

theorem pick_eq_of_val_singleton {α : Type} (values : Some α)
    (value : α) (index : Nat) (h : values.val = [value]) :
    pick values index = value :=
  List.mem_singleton.mp (h ▸ pick_mem values index)

theorem node_service_step_singleton {cfg : Storage.Config}
    {running running' : Running Storage.Config Nat CMsg}
    {sender : Addr} {message : CMsg} {now : Time}
    {outs : List (Out CMsg)}
    (h :
      (toStep node 64 sender message now cfg running).val =
        [((), running', outs)]) :
    (system.step cfg (.node running) now (.msg sender message)).val =
      [(.node running', outs)] := by
  have hsome :
      toStep node 64 sender message now cfg running =
        Some.one ((), running', outs) :=
    Subtype.ext h
  simp [system, Experiment.Service.step, receive, H.run, hsome,
    Experiment.Some.map]
  exact ⟨(), rfl⟩

theorem store_service_step_singleton {cfg : Storage.Config}
    {store store' : Store} {sender : Addr} {message : CMsg} {now : Time}
    {outs : List (Out CMsg)}
    (h : ((storeReceive sender message).run cfg store).val =
      [((), store', outs)]) :
    (system.step cfg (Local.store store) now (.msg sender message)).val =
      [(Local.store store', outs)] := by
  have hsome :
      (storeReceive sender message).run cfg store =
        Some.one ((), store', outs) :=
    Subtype.ext h
  change ((((storeReceive sender message).run cfg store).map
    (fun (result, nextStore, nextOuts) =>
      (result, Local.store nextStore, nextOuts))).map
    (fun (_, nextState, nextOuts) => (nextState, nextOuts))).val =
    [(Local.store store', outs)]
  rw [hsome]
  rfl

theorem pick_map {α β : Type} (values : Some α) (f : α → β) (choice : Nat) :
    pick (values.map f) choice = f (pick values choice) := by
  simp [pick, Some.map]

theorem store_service_step_pick {cfg : Storage.Config}
    {store store' : Store} {sender : Addr} {message : CMsg} {now : Time}
    {outs : List (Out CMsg)} {choice : Nat}
    (h : pick ((storeReceive sender message).run cfg store) choice =
      ((), store', outs)) :
    pick (system.step cfg (Local.store store) now (.msg sender message)) choice =
      (Local.store store', outs) := by
  change pick ((((storeReceive sender message).run cfg store).map
    (fun (result, nextStore, nextOuts) =>
      (result, Local.store nextStore, nextOuts))).map
    (fun (_, nextState, nextOuts) => (nextState, nextOuts))) choice =
    (Local.store store', outs)
  rw [pick_map, pick_map, h]

def NormalRel (cfg : Storage.Config)
    (concrete : Network.Conf system) (abstract : Experiment.Conf promises) : Prop :=
  ∃ node1 node2 store wire1 wire2 nodeTokens1 nodeTokens2,
    concrete.states =
      [("n1", .node node1), ("n2", .node node2), ("s3", .store store)] ∧
    NodeRep cfg store "n1" node1 wire1 nodeTokens1 ∧
    NodeRep cfg store "n2" node2 wire2 nodeTokens2 ∧
    (protocolMessages concrete.net).Perm
      (optionList wire1 ++ optionList wire2) ∧
    Covers (appTokens concrete.net ++ nodeTokens1 ++ nodeTokens2) abstract.net ∧
    StoreRep store abstract.state ∧
    abstract.now ≤ concrete.now

theorem NodeRep.commit {cfg : Storage.Config} {store : Store} {address : Addr}
    {running : Running Storage.Config Nat CMsg} {wire : Option ConcreteMessage}
    {tokens : List AbstractMessage} {key : Ident} {promise : Promise}
    (h : NodeRep cfg store address running wire tokens) :
    NodeRep cfg (storeCommit store key promise) address running wire tokens := by
  cases h with
  | idle happ hn => exact .idle happ hn
  | loadingGet happ hnext hn => exact .loadingGet happ hnext hn
  | loadingGot happ hnext hn hchanged hs hd =>
    exact .loadingGot happ hnext hn hchanged hs.commit hd
  | loadingDone happ hnext hn hpick hunchanged hs hd =>
    exact .loadingDone happ hnext hn hpick hunchanged hs.commit hd
  | writingPut happ hnext hn hvalid hs =>
    exact .writingPut happ hnext hn hvalid hs.commit
  | writingConflict happ hnext hn hvalid hs =>
    exact .writingConflict happ hnext hn hvalid hs.commit
  | writingServed happ hnext hn hvalid =>
    exact .writingServed happ hnext hn hvalid
  | writingLost happ hnext hn hvalid =>
    exact .writingLost happ hnext hn hvalid
  | writingShed happ hnext hn hvalid hs =>
    exact .writingShed happ hnext hn hvalid hs.commit

theorem NodeRep.receive_app_nonrequest {cfg : Storage.Config} {store : Store}
    {address sender : Addr} {running : Running Storage.Config Nat CMsg}
    {wire : Option ConcreteMessage} {tokens : List AbstractMessage}
    (h : NodeRep cfg store address running wire tokens)
    (message : Msg) (now : Time)
    (hm : isRequest sender (.app message) = false) :
    ∃ running',
      (toStep node 64 sender (.app message) now cfg running).val =
        [((), running', [])] ∧
      NodeRep cfg store address running' wire tokens := by
  cases h with
  | idle happ hn =>
    refine ⟨_, idle_nonrequest_run hn _ sender message now hm, ?_⟩
    simpa only [mailboxTokens_append_nonrequest hm] using
      (NodeRep.idle (happ.append_app sender message)
        (take?_append_miss hn hm))
  | loadingGet happ hnext hn =>
    refine ⟨_, loading_app_run hn sender message now, ?_⟩
    simpa only [mailboxTokens_append_nonrequest hm] using
      (NodeRep.loadingGet (happ.append_app sender message) hnext
        (take?_append_miss hn rfl))
  | loadingGot happ hnext hn hchanged hs hd =>
    refine ⟨_, loading_app_run hn sender message now, ?_⟩
    simpa only [mailboxTokens_append_nonrequest hm] using
      (NodeRep.loadingGot (happ.append_app sender message) hnext
        (take?_append_miss hn rfl) hchanged hs hd)
  | loadingDone happ hnext hn hpick hunchanged hs hd =>
    refine ⟨_, loading_app_run hn sender message now, ?_⟩
    simpa only [mailboxTokens_append_nonrequest hm] using
      (NodeRep.loadingDone (happ.append_app sender message) hnext
        (take?_append_miss hn rfl) hpick hunchanged hs hd)
  | writingPut happ hnext hn hv hs =>
    refine ⟨_, writing_app_run hn sender message now, ?_⟩
    simpa only [mailboxTokens_append_nonrequest hm] using
      (NodeRep.writingPut (happ.append_app sender message) hnext
        (take?_append_miss hn rfl) hv hs)
  | writingConflict happ hnext hn hv hs =>
    refine ⟨_, writing_app_run hn sender message now, ?_⟩
    simpa only [mailboxTokens_append_nonrequest hm] using
      (NodeRep.writingConflict (happ.append_app sender message) hnext
        (take?_append_miss hn rfl) hv hs)
  | writingServed happ hnext hn hv =>
    refine ⟨_, writing_app_run hn sender message now, ?_⟩
    simpa only [mailboxTokens_append_nonrequest hm] using
      (NodeRep.writingServed (happ.append_app sender message) hnext
        (take?_append_miss hn rfl) hv)
  | writingLost happ hnext hn hv =>
    refine ⟨_, writing_app_run hn sender message now, ?_⟩
    simpa only [mailboxTokens_append_nonrequest hm] using
      (NodeRep.writingLost (happ.append_app sender message) hnext
        (take?_append_miss hn rfl) hv)
  | writingShed happ hnext hn hv hs =>
    refine ⟨_, writing_app_run hn sender message now, ?_⟩
    simpa only [mailboxTokens_append_nonrequest hm] using
      (NodeRep.writingShed (happ.append_app sender message) hnext
        (take?_append_miss hn rfl) hv hs)

theorem NodeRep.receive_app_request_busy {cfg : Storage.Config} {store : Store}
    {address sender : Addr} {running : Running Storage.Config Nat CMsg}
    {wire : Option ConcreteMessage} {tokens : List AbstractMessage}
    (h : NodeRep cfg store address running wire tokens)
    (id : CallId) (requestNow now : Time) (request : Request)
    (hbusy : wire ≠ none) :
    ∃ running' tokens',
      (toStep node 64 sender (.app (.req id requestNow request)) now cfg
        running).val = [((), running', [])] ∧
      NodeRep cfg store address running' wire tokens' ∧
      tokens'.Perm
        (tokens ++ [Call.token ⟨sender, id, request, requestNow⟩]) := by
  let queued : Call := ⟨sender, id, request, requestNow⟩
  cases h with
  | idle happ hn => exact (hbusy rfl).elim
  | @loadingGet call tries op next mailbox happ hnext hn =>
    let tokens' := mailboxTokens
      (mailbox ++ [(sender, .app (.req id requestNow request))]) ++
        [call.token]
    refine ⟨_, tokens', loading_app_run hn sender (.req id requestNow request) now,
      ?_, ?_⟩
    · simpa [tokens', mailboxTokens_append_request, queued] using
        (NodeRep.loadingGet
          (cfg := cfg) (store := store) (address := address)
          (call := call) (tries := tries)
          (happ.append_app sender (.req id requestNow request)) hnext
          (take?_append_miss hn rfl))
    · simpa [tokens', mailboxTokens_append_request, queued,
        List.append_assoc] using
        perm_insert_before_suffix (mailboxTokens mailbox) [call.token] queued.token
  | @loadingGot call tries op next mailbox doc happ hnext hn hchanged hs hd =>
    let tokens' := mailboxTokens
      (mailbox ++ [(sender, .app (.req id requestNow request))]) ++
        [call.token]
    refine ⟨_, tokens', loading_app_run hn sender (.req id requestNow request) now,
      ?_, ?_⟩
    · simpa [tokens', mailboxTokens_append_request, queued] using
        (NodeRep.loadingGot
          (cfg := cfg) (store := store) (address := address)
          (call := call) (tries := tries) (doc := doc)
          (happ.append_app sender (.req id requestNow request)) hnext
          (take?_append_miss hn rfl) hchanged hs hd)
    · simpa [tokens', mailboxTokens_append_request, queued,
        List.append_assoc] using
        perm_insert_before_suffix (mailboxTokens mailbox) [call.token] queued.token
  | @loadingDone call tries op next mailbox doc res after outs
      happ hnext hn hpick hunchanged hs hd =>
    let stage :=
      outputTokens outs ++ [responseToken call.client call.id res]
    let tokens' := mailboxTokens
      (mailbox ++ [(sender, .app (.req id requestNow request))]) ++ stage
    refine ⟨_, tokens', loading_app_run hn sender (.req id requestNow request) now,
      ?_, ?_⟩
    · simpa [tokens', stage, mailboxTokens_append_request, queued] using
        (NodeRep.loadingDone
          (cfg := cfg) (store := store) (address := address)
          (call := call) (tries := tries) (doc := doc)
          (happ.append_app sender (.req id requestNow request)) hnext
          (take?_append_miss hn rfl) hpick hunchanged hs hd)
    · simpa [tokens', stage, mailboxTokens_append_request, queued,
        List.append_assoc] using
        perm_insert_before_suffix (mailboxTokens mailbox) stage queued.token
  | @writingPut candidate op next mailbox happ hnext hn hv hs =>
    let tokens' := mailboxTokens
      (mailbox ++ [(sender, .app (.req id requestNow request))]) ++
        candidate.stageTokens .pending
    refine ⟨_, tokens', writing_app_run hn sender (.req id requestNow request) now,
      ?_, ?_⟩
    · simpa [tokens', mailboxTokens_append_request, queued] using
        (NodeRep.writingPut
          (cfg := cfg) (store := store) (address := address)
          (candidate := candidate)
          (happ.append_app sender (.req id requestNow request)) hnext
          (take?_append_miss hn rfl) hv hs)
    · simpa [tokens', mailboxTokens_append_request, queued,
        List.append_assoc] using
        perm_insert_before_suffix (mailboxTokens mailbox)
          (candidate.stageTokens .pending) queued.token
  | @writingConflict candidate op next mailbox happ hnext hn hv hs =>
    let tokens' := mailboxTokens
      (mailbox ++ [(sender, .app (.req id requestNow request))]) ++
        candidate.stageTokens .pending
    refine ⟨_, tokens', writing_app_run hn sender (.req id requestNow request) now,
      ?_, ?_⟩
    · simpa [tokens', mailboxTokens_append_request, queued] using
        (NodeRep.writingConflict
          (cfg := cfg) (store := store) (address := address)
          (candidate := candidate)
          (happ.append_app sender (.req id requestNow request)) hnext
          (take?_append_miss hn rfl) hv hs)
    · simpa [tokens', mailboxTokens_append_request, queued,
        List.append_assoc] using
        perm_insert_before_suffix (mailboxTokens mailbox)
          (candidate.stageTokens .pending) queued.token
  | @writingServed candidate op next mailbox happ hnext hn hv =>
    let tokens' := mailboxTokens
      (mailbox ++ [(sender, .app (.req id requestNow request))]) ++
        candidate.stageTokens .served
    refine ⟨_, tokens', writing_app_run hn sender (.req id requestNow request) now,
      ?_, ?_⟩
    · simpa [tokens', mailboxTokens_append_request, queued] using
        (NodeRep.writingServed
          (cfg := cfg) (store := store) (address := address)
          (candidate := candidate)
          (happ.append_app sender (.req id requestNow request)) hnext
          (take?_append_miss hn rfl) hv)
    · simpa [tokens', mailboxTokens_append_request, queued,
        List.append_assoc] using
        perm_insert_before_suffix (mailboxTokens mailbox)
          (candidate.stageTokens .served) queued.token
  | @writingLost candidate op next mailbox happ hnext hn hv =>
    let tokens' := mailboxTokens
      (mailbox ++ [(sender, .app (.req id requestNow request))]) ++
        candidate.stageTokens .lost
    refine ⟨_, tokens', writing_app_run hn sender (.req id requestNow request) now,
      ?_, ?_⟩
    · simpa [tokens', mailboxTokens_append_request, queued] using
        (NodeRep.writingLost
          (cfg := cfg) (store := store) (address := address)
          (candidate := candidate)
          (happ.append_app sender (.req id requestNow request)) hnext
          (take?_append_miss hn rfl) hv)
    · simpa [tokens', mailboxTokens_append_request, queued,
        List.append_assoc] using
        perm_insert_before_suffix (mailboxTokens mailbox)
          (candidate.stageTokens .lost) queued.token
  | @writingShed candidate op next mailbox happ hnext hn hv hs =>
    let tokens' := mailboxTokens
      (mailbox ++ [(sender, .app (.req id requestNow request))]) ++
        candidate.stageTokens .shed
    refine ⟨_, tokens', writing_app_run hn sender (.req id requestNow request) now,
      ?_, ?_⟩
    · simpa [tokens', mailboxTokens_append_request, queued] using
        (NodeRep.writingShed
          (cfg := cfg) (store := store) (address := address)
          (candidate := candidate)
          (happ.append_app sender (.req id requestNow request)) hnext
          (take?_append_miss hn rfl) hv hs)
    · simpa [tokens', mailboxTokens_append_request, queued,
        List.append_assoc] using
        perm_insert_before_suffix (mailboxTokens mailbox)
          (candidate.stageTokens .shed) queued.token

theorem NodeRep.wire_is_protocol {cfg : Storage.Config} {store : Store}
    {address : Addr} {running : Running Storage.Config Nat CMsg}
    {wire : Option ConcreteMessage} {tokens : List AbstractMessage}
    (h : NodeRep cfg store address running wire tokens)
    {message : ConcreteMessage} (hw : wire = some message) :
    ∃ source dest m, message = (.proc source, .proc dest, m) := by
  cases h <;> simp_all <;> subst message <;> exact ⟨_, _, _, rfl⟩

theorem protocol_message_is_between_procs {cfg : Storage.Config} {store : Store}
    {node1 node2 : Running Storage.Config Nat CMsg}
    {wire1 wire2 : Option ConcreteMessage}
    {tokens1 tokens2 : List AbstractMessage} {net : List ConcreteMessage}
    (hn1 : NodeRep cfg store "n1" node1 wire1 tokens1)
    (hn2 : NodeRep cfg store "n2" node2 wire2 tokens2)
    (hp : (protocolMessages net).Perm
      (optionList wire1 ++ optionList wire2))
    {message : ConcreteMessage} (hm : message ∈ protocolMessages net) :
    ∃ source dest m, message = (.proc source, .proc dest, m) := by
  have hout := (hp.mem_iff).1 hm
  simp only [List.mem_append] at hout
  rcases hout with hout | hout
  · have hw : wire1 = some message := by
      cases wire1 <;> simp [optionList] at hout ⊢
      exact hout.symm
    exact hn1.wire_is_protocol hw
  · have hw : wire2 = some message := by
      cases wire2 <;> simp [optionList] at hout ⊢
      exact hout.symm
    exact hn2.wire_is_protocol hw

theorem initial_store_rep :
    StoreRep ({} : Store) ({} : Experiment.State) := by
  intro key
  simp [storePromiseAt, storeLookup, Experiment.promiseAt]

theorem initial_normalRel (cfg : Storage.Config) :
    NormalRel cfg (Network.initial world) (Experiment.initial {}) := by
  refine ⟨⟨0, [], node⟩, ⟨0, [], node⟩, {}, none, none, [], [],
    rfl, ?_, ?_, ?_, ?_, initial_store_rep, Nat.le_refl 0⟩
  · exact .idle (by simp [AppOnly]) rfl
  · exact .idle (by simp [AppOnly]) rfl
  · change [].Perm []
    exact .nil
  · change Covers [] []
    exact ⟨[], List.Perm.refl []⟩

theorem normalRel_node1_conflict_retry {cfg : Storage.Config}
    {net : List ConcreteMessage} {now t : Time}
    {candidate : Candidate} {op next k : Nat}
    {mailbox : List (Addr × CMsg)}
    {node2 : Running Storage.Config Nat CMsg} {store : Store}
    {wire2 : Option ConcreteMessage} {tokens2 : List AbstractMessage}
    {a : Experiment.Conf promises}
    (hstoreAddr : cfg.store = "s3")
    (happ : AppOnly mailbox) (hnext : next = op + 1)
    (hnone : take? (answers op) mailbox = none)
    (hvalid : candidate.Valid cfg)
    (hsnapshot : Snapshot store candidate.req.key candidate.doc)
    (htries : candidate.tries = k + 1)
    (hn2 : NodeRep cfg store "n2" node2 wire2 tokens2)
    (hprotocol : (protocolMessages net).Perm
      ([((.proc "s3", .proc "n1", .conflict op) : ConcreteMessage)] ++
        optionList wire2))
    (hcover : Covers
      (appTokens net ++
        (mailboxTokens mailbox ++ candidate.stageTokens .pending) ++
        tokens2) a.net)
    (hstore : StoreRep store a.state) (htime : a.now ≤ now)
    (hstepTime : now ≤ t) (source : Network.Who)
    (pre post : List ConcreteMessage)
    (hnet : net = pre ++
      ((.proc "s3", .proc "n1", .conflict op) : ConcreteMessage) :: post) :
    let running : Running Storage.Config Nat CMsg :=
      ⟨next + 1, mailbox,
        loadK k (candidate.call.retry k)
          candidate.client candidate.id candidate.req candidate.now next⟩
    let wire : ConcreteMessage :=
      (.proc "n1", .proc "s3", .get next candidate.req.key)
    (toStep node 64 source.addr (.conflict op) t cfg
      (⟨next, mailbox,
        writeK candidate.tries (candidate.call.retry candidate.tries)
          candidate op⟩ : Running Storage.Config Nat CMsg)).val =
      [((), running, [.send "s3" (.get next candidate.req.key)])] ∧
    NormalRel cfg
      ⟨pre ++ post ++ [wire],
        [("n1", .node running), ("n2", .node node2), ("s3", .store store)],
        t⟩ a := by
  dsimp
  constructor
  · simpa [hstoreAddr] using
      (writing_conflict_retry_run (cfg := cfg) (cand := candidate)
        (next := next) happ hnone htries source.addr t)
  · let wire : ConcreteMessage :=
      (.proc "n1", .proc "s3", .get next candidate.req.key)
    refine ⟨_, node2, store, some wire, wire2,
      mailboxTokens mailbox ++ [candidate.call.token], tokens2,
      rfl, ?_, hn2, ?_, ?_, hstore, Nat.le_trans htime hstepTime⟩
    · simpa [wire, hstoreAddr, Candidate.call] using
        (NodeRep.loadingGet
          (cfg := cfg) (store := store) (address := "n1")
          (call := candidate.call) (tries := k)
          happ rfl (answers_none_of_appOnly mailbox next happ))
    · rw [hnet] at hprotocol
      have hbase :
          (protocolMessages pre ++ protocolMessages post).Perm
            (optionList wire2) := by
        apply Perm.cancel_exposed
        simpa [protocolMessages, List.append_assoc] using hprotocol
      have hp := hbase.append_right [wire]
      have hswap :
          (optionList wire2 ++ [wire]).Perm
            ([wire] ++ optionList wire2) := List.perm_append_comm
      simpa [wire, protocolMessages, optionList, List.append_assoc] using
        hp.trans hswap
    · rw [hnet] at hcover
      simpa [wire, appTokens, appToken, Candidate.stageTokens,
        List.append_assoc] using hcover

theorem normalRel_node2_conflict_retry {cfg : Storage.Config}
    {net : List ConcreteMessage} {now t : Time}
    {candidate : Candidate} {op next k : Nat}
    {mailbox : List (Addr × CMsg)}
    {node1 : Running Storage.Config Nat CMsg} {store : Store}
    {wire1 : Option ConcreteMessage} {tokens1 : List AbstractMessage}
    {a : Experiment.Conf promises}
    (hstoreAddr : cfg.store = "s3")
    (hn1 : NodeRep cfg store "n1" node1 wire1 tokens1)
    (happ : AppOnly mailbox) (hnext : next = op + 1)
    (hnone : take? (answers op) mailbox = none)
    (hvalid : candidate.Valid cfg)
    (hsnapshot : Snapshot store candidate.req.key candidate.doc)
    (htries : candidate.tries = k + 1)
    (hprotocol : (protocolMessages net).Perm
      (optionList wire1 ++
        [((.proc "s3", .proc "n2", .conflict op) : ConcreteMessage)]))
    (hcover : Covers
      (appTokens net ++ tokens1 ++
        (mailboxTokens mailbox ++ candidate.stageTokens .pending)) a.net)
    (hstore : StoreRep store a.state) (htime : a.now ≤ now)
    (hstepTime : now ≤ t) (source : Network.Who)
    (pre post : List ConcreteMessage)
    (hnet : net = pre ++
      ((.proc "s3", .proc "n2", .conflict op) : ConcreteMessage) :: post) :
    let running : Running Storage.Config Nat CMsg :=
      ⟨next + 1, mailbox,
        loadK k (candidate.call.retry k)
          candidate.client candidate.id candidate.req candidate.now next⟩
    let wire : ConcreteMessage :=
      (.proc "n2", .proc "s3", .get next candidate.req.key)
    (toStep node 64 source.addr (.conflict op) t cfg
      (⟨next, mailbox,
        writeK candidate.tries (candidate.call.retry candidate.tries)
          candidate op⟩ : Running Storage.Config Nat CMsg)).val =
      [((), running, [.send "s3" (.get next candidate.req.key)])] ∧
    NormalRel cfg
      ⟨pre ++ post ++ [wire],
        [("n1", .node node1), ("n2", .node running), ("s3", .store store)],
        t⟩ a := by
  dsimp
  constructor
  · simpa [hstoreAddr] using
      (writing_conflict_retry_run (cfg := cfg) (cand := candidate)
        (next := next) happ hnone htries source.addr t)
  · let wire : ConcreteMessage :=
      (.proc "n2", .proc "s3", .get next candidate.req.key)
    refine ⟨node1, _, store, wire1, some wire,
      tokens1, mailboxTokens mailbox ++ [candidate.call.token],
      rfl, hn1, ?_, ?_, ?_, hstore, Nat.le_trans htime hstepTime⟩
    · simpa [wire, hstoreAddr, Candidate.call] using
        (NodeRep.loadingGet
          (cfg := cfg) (store := store) (address := "n2")
          (call := candidate.call) (tries := k)
          happ rfl (answers_none_of_appOnly mailbox next happ))
    · rw [hnet] at hprotocol
      have hbase :
          (protocolMessages pre ++ protocolMessages post).Perm
            (optionList wire1) := by
        have hp := hprotocol.trans List.perm_append_comm
        apply Perm.cancel_exposed
        simpa [protocolMessages, List.append_assoc] using hp
      simpa [wire, protocolMessages, optionList, List.append_assoc] using
        hbase.append_right [wire]
    · rw [hnet] at hcover
      simpa [wire, appTokens, appToken, Candidate.stageTokens,
        List.append_assoc] using hcover

set_option maxHeartbeats 1000000 in
theorem normalRel_node1_got_changed {cfg : Storage.Config}
    {net : List ConcreteMessage} {now t : Time}
    {call : Call} {tries op next : Nat}
    {mailbox : List (Addr × CMsg)}
    {doc : Option (Promise × Version)}
    {res : Response} {after : Experiment.State} {outs : List (Out Msg)}
    {promise : Promise}
    {node2 : Running Storage.Config Nat CMsg} {store : Store}
    {wire2 : Option ConcreteMessage} {tokens2 : List AbstractMessage}
    {a : Experiment.Conf promises}
    (hstoreAddr : cfg.store = "s3")
    (happ : AppOnly mailbox) (hnext : next = op + 1)
    (hnone : take? (answers op) mailbox = none)
    (hpick :
      pick ((Experiment.dispatch call.req call.now).run
        { cfg.app with unreliable := true }
        { promises := doc.toList.map (·.1) }) 0 = (res, after, outs))
    (hchanged : (after == { promises := doc.toList.map (·.1) }) = false)
    (hpromise :
      after.promises.find? (·.id == call.req.key) = some promise)
    (hsnapshot : Snapshot store call.req.key doc)
    (hdoc : DocAtKey call.req.key doc)
    (hn2 : NodeRep cfg store "n2" node2 wire2 tokens2)
    (hprotocol : (protocolMessages net).Perm
      ([((.proc "s3", .proc "n1", .got op doc) : ConcreteMessage)] ++
        optionList wire2))
    (hcover : Covers
      (appTokens net ++ (mailboxTokens mailbox ++ [call.token]) ++
        tokens2) a.net)
    (hstore : StoreRep store a.state) (htime : a.now ≤ now)
    (hstepTime : now ≤ t) (source : Network.Who)
    (pre post : List ConcreteMessage)
    (hnet : net = pre ++
      ((.proc "s3", .proc "n1", .got op doc) : ConcreteMessage) :: post) :
    let candidate : Candidate :=
      ⟨call.client, call.id, call.req, call.now, tries, doc,
        res, after, outs, promise⟩
    let running : Running Storage.Config Nat CMsg :=
      ⟨next + 1, mailbox,
        writeK tries (call.retry tries) candidate next⟩
    let wire : ConcreteMessage :=
      (.proc "n1", .proc "s3",
        .put next call.req.key promise (doc.map (·.2)))
    (toStep node 64 source.addr (.got op doc) t cfg
      (⟨next, mailbox,
        loadK tries (call.retry tries)
          call.client call.id call.req call.now op⟩ :
        Running Storage.Config Nat CMsg)).val =
      [((), running, notes outs ++
        [.send "s3" (.put next call.req.key promise (doc.map (·.2)))])] ∧
    NormalRel cfg
      ⟨pre ++ post ++ [wire],
        [("n1", .node running), ("n2", .node node2), ("s3", .store store)],
        t⟩ a := by
  dsimp
  constructor
  · simpa [hstoreAddr] using
      (loading_got_changed_run (cfg := cfg) (call := call)
        (tries := tries) (next := next) happ hnone hpick hchanged hpromise
        source.addr t)
  · let candidate : Candidate :=
      ⟨call.client, call.id, call.req, call.now, tries, doc,
        res, after, outs, promise⟩
    let wire : ConcreteMessage :=
      (.proc "n1", .proc "s3",
        .put next call.req.key promise (doc.map (·.2)))
    have hvalid : candidate.Valid cfg := by
      simpa [candidate] using changed_candidate_valid hpick hdoc hpromise
    refine ⟨_, node2, store, some wire, wire2,
      mailboxTokens mailbox ++ candidate.stageTokens .pending, tokens2,
      rfl, ?_, hn2, ?_, ?_, hstore, Nat.le_trans htime hstepTime⟩
    · simpa [candidate, wire, hstoreAddr, Candidate.call, Call.retry] using
        (NodeRep.writingPut
          (cfg := cfg) (store := store) (address := "n1")
          (candidate := candidate) happ rfl
          (answers_none_of_appOnly mailbox next happ) hvalid hsnapshot)
    · rw [hnet] at hprotocol
      have hbase :
          (protocolMessages pre ++ protocolMessages post).Perm
            (optionList wire2) := by
        apply Perm.cancel_exposed
        simpa [protocolMessages, List.append_assoc] using hprotocol
      have hp := hbase.append_right [wire]
      have hswap :
          (optionList wire2 ++ [wire]).Perm
            ([wire] ++ optionList wire2) := List.perm_append_comm
      simpa [wire, protocolMessages, optionList, List.append_assoc] using
        hp.trans hswap
    · rw [hnet] at hcover
      simpa [candidate, wire, appTokens, appToken, Candidate.stageTokens,
        Candidate.call, Call.token, List.append_assoc] using hcover

set_option maxHeartbeats 1000000 in
theorem normalRel_node2_got_changed {cfg : Storage.Config}
    {net : List ConcreteMessage} {now t : Time}
    {call : Call} {tries op next : Nat}
    {mailbox : List (Addr × CMsg)}
    {doc : Option (Promise × Version)}
    {res : Response} {after : Experiment.State} {outs : List (Out Msg)}
    {promise : Promise}
    {node1 : Running Storage.Config Nat CMsg} {store : Store}
    {wire1 : Option ConcreteMessage} {tokens1 : List AbstractMessage}
    {a : Experiment.Conf promises}
    (hstoreAddr : cfg.store = "s3")
    (hn1 : NodeRep cfg store "n1" node1 wire1 tokens1)
    (happ : AppOnly mailbox) (hnext : next = op + 1)
    (hnone : take? (answers op) mailbox = none)
    (hpick :
      pick ((Experiment.dispatch call.req call.now).run
        { cfg.app with unreliable := true }
        { promises := doc.toList.map (·.1) }) 0 = (res, after, outs))
    (hchanged : (after == { promises := doc.toList.map (·.1) }) = false)
    (hpromise :
      after.promises.find? (·.id == call.req.key) = some promise)
    (hsnapshot : Snapshot store call.req.key doc)
    (hdoc : DocAtKey call.req.key doc)
    (hprotocol : (protocolMessages net).Perm
      (optionList wire1 ++
        [((.proc "s3", .proc "n2", .got op doc) : ConcreteMessage)]))
    (hcover : Covers
      (appTokens net ++ tokens1 ++
        (mailboxTokens mailbox ++ [call.token])) a.net)
    (hstore : StoreRep store a.state) (htime : a.now ≤ now)
    (hstepTime : now ≤ t) (source : Network.Who)
    (pre post : List ConcreteMessage)
    (hnet : net = pre ++
      ((.proc "s3", .proc "n2", .got op doc) : ConcreteMessage) :: post) :
    let candidate : Candidate :=
      ⟨call.client, call.id, call.req, call.now, tries, doc,
        res, after, outs, promise⟩
    let running : Running Storage.Config Nat CMsg :=
      ⟨next + 1, mailbox,
        writeK tries (call.retry tries) candidate next⟩
    let wire : ConcreteMessage :=
      (.proc "n2", .proc "s3",
        .put next call.req.key promise (doc.map (·.2)))
    (toStep node 64 source.addr (.got op doc) t cfg
      (⟨next, mailbox,
        loadK tries (call.retry tries)
          call.client call.id call.req call.now op⟩ :
        Running Storage.Config Nat CMsg)).val =
      [((), running, notes outs ++
        [.send "s3" (.put next call.req.key promise (doc.map (·.2)))])] ∧
    NormalRel cfg
      ⟨pre ++ post ++ [wire],
        [("n1", .node node1), ("n2", .node running), ("s3", .store store)],
        t⟩ a := by
  dsimp
  constructor
  · simpa [hstoreAddr] using
      (loading_got_changed_run (cfg := cfg) (call := call)
        (tries := tries) (next := next) happ hnone hpick hchanged hpromise
        source.addr t)
  · let candidate : Candidate :=
      ⟨call.client, call.id, call.req, call.now, tries, doc,
        res, after, outs, promise⟩
    let wire : ConcreteMessage :=
      (.proc "n2", .proc "s3",
        .put next call.req.key promise (doc.map (·.2)))
    have hvalid : candidate.Valid cfg := by
      simpa [candidate] using changed_candidate_valid hpick hdoc hpromise
    refine ⟨node1, _, store, wire1, some wire,
      tokens1, mailboxTokens mailbox ++ candidate.stageTokens .pending,
      rfl, hn1, ?_, ?_, ?_, hstore, Nat.le_trans htime hstepTime⟩
    · simpa [candidate, wire, hstoreAddr, Candidate.call, Call.retry] using
        (NodeRep.writingPut
          (cfg := cfg) (store := store) (address := "n2")
          (candidate := candidate) happ rfl
          (answers_none_of_appOnly mailbox next happ) hvalid hsnapshot)
    · rw [hnet] at hprotocol
      have hbase :
          (protocolMessages pre ++ protocolMessages post).Perm
            (optionList wire1) := by
        have hp := hprotocol.trans List.perm_append_comm
        apply Perm.cancel_exposed
        simpa [protocolMessages, List.append_assoc] using hp
      simpa [wire, protocolMessages, optionList, List.append_assoc] using
        hbase.append_right [wire]
    · rw [hnet] at hcover
      simpa [candidate, wire, appTokens, appToken, Candidate.stageTokens,
        Candidate.call, Call.token, List.append_assoc] using hcover

theorem normalRel_node1_written {cfg : Storage.Config}
    {net : List ConcreteMessage} {now t : Time}
    {candidate : Candidate} {op next : Nat}
    {mailbox : List (Addr × CMsg)}
    {node2 : Running Storage.Config Nat CMsg} {store : Store}
    {wire2 : Option ConcreteMessage} {tokens2 : List AbstractMessage}
    {a : Experiment.Conf promises}
    (hstoreAddr : cfg.store = "s3")
    (happ : AppOnly mailbox) (hnext : next = op + 1)
    (hnone : take? (answers op) mailbox = none)
    (hvalid : candidate.Valid cfg)
    (hn2 : NodeRep cfg store "n2" node2 wire2 tokens2)
    (hprotocol : (protocolMessages net).Perm
      ([((.proc "s3", .proc "n1", .written op) : ConcreteMessage)] ++
        optionList wire2))
    (hcover : Covers
      (appTokens net ++
        (mailboxTokens mailbox ++ candidate.stageTokens .served) ++
        tokens2) a.net)
    (hstore : StoreRep store a.state) (htime : a.now ≤ now)
    (hstepTime : now ≤ t) (source : Network.Who)
    (pre post : List ConcreteMessage)
    (hnet : net = pre ++
      ((.proc "s3", .proc "n1", .written op) : ConcreteMessage) :: post) :
    ∃ running rest wire tokens,
      let states : List (Addr × Local) :=
        [("n1", .node running), ("n2", .node node2), ("s3", .store store)]
      let emitted : List (Out CMsg) :=
        .send candidate.client (.app (.res candidate.id candidate.res)) ::
          (sends candidate.outs).map
            (fun (address, message) => .send address (.app message)) ++ rest
      (toStep node 64 source.addr (.written op) t cfg
        (⟨next, mailbox,
          writeK candidate.tries (candidate.call.retry candidate.tries)
            candidate op⟩ : Running Storage.Config Nat CMsg)).val =
          [((), running, emitted)] ∧
      RestartRep cfg store "n1" running rest wire tokens ∧
      NormalRel cfg
        ⟨pre ++ post ++ routedOuts states "n1" emitted, states, t⟩ a := by
  obtain ⟨running, rest, wire, tokens, hrun, hrestart, htokens⟩ :=
    writing_written_restart (cfg := cfg) (store := store) (address := "n1")
      happ hnone source.addr t
  let states : List (Addr × Local) :=
    [("n1", .node running), ("n2", .node node2), ("s3", .store store)]
  let emittedPrefix : List (Out CMsg) :=
    [.send candidate.client (.app (.res candidate.id candidate.res))] ++
      (sends candidate.outs).map
        (fun (address, message) => .send address (.app message))
  let emitted : List (Out CMsg) := emittedPrefix ++ rest
  have hprefixProtocol :
      protocolMessages (routedOuts states "n1" emittedPrefix) = [] := by
    rw [show emittedPrefix =
      [.send candidate.client (.app (.res candidate.id candidate.res))] ++
        (sends candidate.outs).map
          (fun (address, message) => .send address (.app message)) from rfl]
    rw [routedOuts_append, protocolMessages_append,
      protocolMessages_routedResponse,
      protocolMessages_routedOutputs]
    rfl
  have hprefixApp :
      appTokens (routedOuts states "n1" emittedPrefix) =
        [responseToken candidate.client candidate.id candidate.res] ++
          outputTokens candidate.outs := by
    rw [show emittedPrefix =
      [.send candidate.client (.app (.res candidate.id candidate.res))] ++
        (sends candidate.outs).map
          (fun (address, message) => .send address (.app message)) from rfl]
    rw [routedOuts_append, appTokens_append,
      appTokens_routedResponse,
      appTokens_routedOutputs states "n1" candidate.outs
        (Candidate.onlyNotifies (candidate := candidate) hvalid)]
  have hrouteProtocol :
      protocolMessages (routedOuts states "n1" emitted) =
        optionList wire := by
    rw [show emitted = emittedPrefix ++ rest from rfl, routedOuts_append,
      protocolMessages_append, hprefixProtocol, List.nil_append]
    cases hrestart with
    | idle happ' hnone' => rfl
    | @loading call nextOp next' mailbox' happ' hnext' hnone' =>
      simp [routedOuts, routedMessages, sends, protocolMessages,
        optionList, states, hstoreAddr, Network.Conf.route,
        Network.Conf.isProc]
  have hrouteApp :
      appTokens (routedOuts states "n1" emitted) =
        [responseToken candidate.client candidate.id candidate.res] ++
          outputTokens candidate.outs := by
    rw [show emitted = emittedPrefix ++ rest from rfl, routedOuts_append,
      appTokens_append, hprefixApp]
    cases hrestart <;>
      simp [routedOuts, routedMessages, sends, appTokens, appToken,
        states, hstoreAddr, Network.Conf.route, Network.Conf.isProc]
  refine ⟨running, rest, wire, tokens, ?_, hrestart, ?_⟩
  · simpa [emitted, emittedPrefix, List.append_assoc] using hrun
  · rw [hnet] at hprotocol hcover
    have hbase :
        (protocolMessages pre ++ protocolMessages post).Perm
          (optionList wire2) := by
      apply Perm.cancel_exposed
      simpa [protocolMessages, List.append_assoc] using hprotocol
    have hprotocolFinal :
        (protocolMessages
          (pre ++ post ++ routedOuts states "n1" emitted)).Perm
          (optionList wire ++ optionList wire2) := by
      rw [protocolMessages_append, protocolMessages_append, hrouteProtocol]
      have hp := hbase.append_right (optionList wire)
      have hswap :
          (optionList wire2 ++ optionList wire).Perm
            (optionList wire ++ optionList wire2) :=
        List.perm_append_comm
      simpa [List.append_assoc] using hp.trans hswap
    have hcoverFinal : Covers
        (appTokens (pre ++ post ++ routedOuts states "n1" emitted) ++
          tokens ++ tokens2) a.net := by
      have hlocal :
          (mailboxTokens mailbox ++ candidate.stageTokens .served).Perm
            ([responseToken candidate.client candidate.id candidate.res] ++
              outputTokens candidate.outs ++ tokens) := by
        have hfirst :
            (mailboxTokens mailbox ++ outputTokens candidate.outs ++
                [responseToken candidate.client candidate.id candidate.res]).Perm
              ([responseToken candidate.client candidate.id candidate.res] ++
                mailboxTokens mailbox ++ outputTokens candidate.outs) := by
          simpa [List.append_assoc] using
            (List.perm_append_comm :
              (mailboxTokens mailbox ++ outputTokens candidate.outs ++
                [responseToken candidate.client candidate.id candidate.res]).Perm
              ([responseToken candidate.client candidate.id candidate.res] ++
                mailboxTokens mailbox ++ outputTokens candidate.outs))
        have hmiddle :
            ([responseToken candidate.client candidate.id candidate.res] ++
                mailboxTokens mailbox ++ outputTokens candidate.outs).Perm
              ([responseToken candidate.client candidate.id candidate.res] ++
                tokens ++ outputTokens candidate.outs) :=
          by
            simpa [List.append_assoc] using
              (List.Perm.append_left
                [responseToken candidate.client candidate.id candidate.res]
                (htokens.symm.append_right (outputTokens candidate.outs)))
        have hlast :
            ([responseToken candidate.client candidate.id candidate.res] ++
                tokens ++ outputTokens candidate.outs).Perm
              ([responseToken candidate.client candidate.id candidate.res] ++
                outputTokens candidate.outs ++ tokens) := by
          simpa [List.append_assoc] using
            (List.Perm.append_left
              [responseToken candidate.client candidate.id candidate.res]
              (List.perm_append_comm :
                (tokens ++ outputTokens candidate.outs).Perm
                  (outputTokens candidate.outs ++ tokens)))
        simpa [Candidate.stageTokens, List.append_assoc] using
          hfirst.trans (hmiddle.trans hlast)
      have hold : Covers
          (appTokens pre ++ appTokens post ++
            (mailboxTokens mailbox ++ candidate.stageTokens .served) ++
            tokens2) a.net := by
        simpa [appTokens, appToken, List.append_assoc] using hcover
      rw [appTokens_append, appTokens_append, hrouteApp]
      apply Covers.of_perm _ hold
      simpa [List.append_assoc] using
        (List.Perm.append_right tokens2
          (List.Perm.append_left (appTokens pre ++ appTokens post) hlocal))
    refine ⟨running, node2, store, wire, wire2, tokens, tokens2,
      rfl, hrestart.nodeRep, hn2, ?_, ?_, hstore,
      Nat.le_trans htime hstepTime⟩
    · simpa [states, emitted, emittedPrefix, List.append_assoc] using
        hprotocolFinal
    · simpa [states, emitted, emittedPrefix, List.append_assoc] using
        hcoverFinal

theorem normalRel_node2_written {cfg : Storage.Config}
    {net : List ConcreteMessage} {now t : Time}
    {candidate : Candidate} {op next : Nat}
    {mailbox : List (Addr × CMsg)}
    {node1 : Running Storage.Config Nat CMsg} {store : Store}
    {wire1 : Option ConcreteMessage} {tokens1 : List AbstractMessage}
    {a : Experiment.Conf promises}
    (hstoreAddr : cfg.store = "s3")
    (hn1 : NodeRep cfg store "n1" node1 wire1 tokens1)
    (happ : AppOnly mailbox) (hnext : next = op + 1)
    (hnone : take? (answers op) mailbox = none)
    (hvalid : candidate.Valid cfg)
    (hprotocol : (protocolMessages net).Perm
      (optionList wire1 ++
        [((.proc "s3", .proc "n2", .written op) : ConcreteMessage)]))
    (hcover : Covers
      (appTokens net ++ tokens1 ++
        (mailboxTokens mailbox ++ candidate.stageTokens .served)) a.net)
    (hstore : StoreRep store a.state) (htime : a.now ≤ now)
    (hstepTime : now ≤ t) (source : Network.Who)
    (pre post : List ConcreteMessage)
    (hnet : net = pre ++
      ((.proc "s3", .proc "n2", .written op) : ConcreteMessage) :: post) :
    ∃ running rest wire tokens,
      let states : List (Addr × Local) :=
        [("n1", .node node1), ("n2", .node running), ("s3", .store store)]
      let emitted : List (Out CMsg) :=
        .send candidate.client (.app (.res candidate.id candidate.res)) ::
          (sends candidate.outs).map
            (fun (address, message) => .send address (.app message)) ++ rest
      (toStep node 64 source.addr (.written op) t cfg
        (⟨next, mailbox,
          writeK candidate.tries (candidate.call.retry candidate.tries)
            candidate op⟩ : Running Storage.Config Nat CMsg)).val =
          [((), running, emitted)] ∧
      RestartRep cfg store "n2" running rest wire tokens ∧
      NormalRel cfg
        ⟨pre ++ post ++ routedOuts states "n2" emitted, states, t⟩ a := by
  obtain ⟨running, rest, wire, tokens, hrun, hrestart, htokens⟩ :=
    writing_written_restart (cfg := cfg) (store := store) (address := "n2")
      happ hnone source.addr t
  let states : List (Addr × Local) :=
    [("n1", .node node1), ("n2", .node running), ("s3", .store store)]
  let emittedPrefix : List (Out CMsg) :=
    [.send candidate.client (.app (.res candidate.id candidate.res))] ++
      (sends candidate.outs).map
        (fun (address, message) => .send address (.app message))
  let emitted : List (Out CMsg) := emittedPrefix ++ rest
  have hprefixProtocol :
      protocolMessages (routedOuts states "n2" emittedPrefix) = [] := by
    rw [show emittedPrefix =
      [.send candidate.client (.app (.res candidate.id candidate.res))] ++
        (sends candidate.outs).map
          (fun (address, message) => .send address (.app message)) from rfl]
    rw [routedOuts_append, protocolMessages_append,
      protocolMessages_routedResponse, protocolMessages_routedOutputs]
    rfl
  have hprefixApp :
      appTokens (routedOuts states "n2" emittedPrefix) =
        [responseToken candidate.client candidate.id candidate.res] ++
          outputTokens candidate.outs := by
    rw [show emittedPrefix =
      [.send candidate.client (.app (.res candidate.id candidate.res))] ++
        (sends candidate.outs).map
          (fun (address, message) => .send address (.app message)) from rfl]
    rw [routedOuts_append, appTokens_append, appTokens_routedResponse,
      appTokens_routedOutputs states "n2" candidate.outs
        (Candidate.onlyNotifies (candidate := candidate) hvalid)]
  have hrouteProtocol :
      protocolMessages (routedOuts states "n2" emitted) =
        optionList wire := by
    rw [show emitted = emittedPrefix ++ rest from rfl, routedOuts_append,
      protocolMessages_append, hprefixProtocol, List.nil_append]
    cases hrestart with
    | idle happ' hnone' => rfl
    | @loading call nextOp next' mailbox' happ' hnext' hnone' =>
      simp [routedOuts, routedMessages, sends, protocolMessages,
        optionList, states, hstoreAddr, Network.Conf.route,
        Network.Conf.isProc]
  have hrouteApp :
      appTokens (routedOuts states "n2" emitted) =
        [responseToken candidate.client candidate.id candidate.res] ++
          outputTokens candidate.outs := by
    rw [show emitted = emittedPrefix ++ rest from rfl, routedOuts_append,
      appTokens_append, hprefixApp]
    cases hrestart <;>
      simp [routedOuts, routedMessages, sends, appTokens, appToken,
        states, hstoreAddr, Network.Conf.route, Network.Conf.isProc]
  rw [hnet] at hprotocol hcover
  have hbaseProtocol :
      (protocolMessages pre ++ protocolMessages post).Perm
        (optionList wire1) := by
    have hp := hprotocol.trans List.perm_append_comm
    apply Perm.cancel_exposed
    simpa [protocolMessages, List.append_assoc] using hp
  have hprotocolFinal :
      (protocolMessages
        (pre ++ post ++ routedOuts states "n2" emitted)).Perm
        (optionList wire1 ++ optionList wire) := by
    rw [protocolMessages_append, protocolMessages_append, hrouteProtocol]
    simpa [List.append_assoc] using hbaseProtocol.append_right (optionList wire)
  have hlocal :
      (mailboxTokens mailbox ++ candidate.stageTokens .served).Perm
        ([responseToken candidate.client candidate.id candidate.res] ++
          outputTokens candidate.outs ++ tokens) := by
    have hfirst :
        (mailboxTokens mailbox ++ outputTokens candidate.outs ++
            [responseToken candidate.client candidate.id candidate.res]).Perm
          ([responseToken candidate.client candidate.id candidate.res] ++
            mailboxTokens mailbox ++ outputTokens candidate.outs) := by
      simpa [List.append_assoc] using
        (List.perm_append_comm :
          (mailboxTokens mailbox ++ outputTokens candidate.outs ++
            [responseToken candidate.client candidate.id candidate.res]).Perm
          ([responseToken candidate.client candidate.id candidate.res] ++
            mailboxTokens mailbox ++ outputTokens candidate.outs))
    have hmiddle :
        ([responseToken candidate.client candidate.id candidate.res] ++
            mailboxTokens mailbox ++ outputTokens candidate.outs).Perm
          ([responseToken candidate.client candidate.id candidate.res] ++
            tokens ++ outputTokens candidate.outs) := by
      simpa [List.append_assoc] using
        (List.Perm.append_left
          [responseToken candidate.client candidate.id candidate.res]
          (htokens.symm.append_right (outputTokens candidate.outs)))
    have hlast :
        ([responseToken candidate.client candidate.id candidate.res] ++
            tokens ++ outputTokens candidate.outs).Perm
          ([responseToken candidate.client candidate.id candidate.res] ++
            outputTokens candidate.outs ++ tokens) := by
      simpa [List.append_assoc] using
        (List.Perm.append_left
          [responseToken candidate.client candidate.id candidate.res]
          (List.perm_append_comm :
            (tokens ++ outputTokens candidate.outs).Perm
              (outputTokens candidate.outs ++ tokens)))
    simpa [Candidate.stageTokens, List.append_assoc] using
      hfirst.trans (hmiddle.trans hlast)
  have hold : Covers
      (appTokens pre ++ appTokens post ++ tokens1 ++
        (mailboxTokens mailbox ++ candidate.stageTokens .served)) a.net := by
    simpa [appTokens, appToken, List.append_assoc] using hcover
  have hcoverFinal : Covers
      (appTokens (pre ++ post ++ routedOuts states "n2" emitted) ++
        tokens1 ++ tokens) a.net := by
    rw [appTokens_append, appTokens_append, hrouteApp]
    apply Covers.of_perm _ hold
    have hwith :
        (tokens1 ++
            (mailboxTokens mailbox ++ candidate.stageTokens .served)).Perm
          (tokens1 ++
            ([responseToken candidate.client candidate.id candidate.res] ++
              outputTokens candidate.outs ++ tokens)) :=
      List.Perm.append_left tokens1 hlocal
    have hmove :
        (tokens1 ++
            ([responseToken candidate.client candidate.id candidate.res] ++
              outputTokens candidate.outs ++ tokens)).Perm
          ([responseToken candidate.client candidate.id candidate.res] ++
            outputTokens candidate.outs ++ tokens1 ++ tokens) := by
      simpa [List.append_assoc] using
        (List.Perm.append_right tokens
          (List.perm_append_comm :
            (tokens1 ++
              ([responseToken candidate.client candidate.id candidate.res] ++
                outputTokens candidate.outs)).Perm
              (([responseToken candidate.client candidate.id candidate.res] ++
                outputTokens candidate.outs) ++ tokens1)))
    simpa [List.append_assoc] using
      (List.Perm.append_left (appTokens pre ++ appTokens post)
        (hwith.trans hmove))
  refine ⟨running, rest, wire, tokens, ?_, hrestart, ?_⟩
  · simpa [emitted, emittedPrefix, List.append_assoc] using hrun
  · refine ⟨node1, running, store, wire1, wire, tokens1, tokens,
      rfl, hn1, hrestart.nodeRep, ?_, ?_, hstore,
      Nat.le_trans htime hstepTime⟩
    · simpa [states, emitted, emittedPrefix, List.append_assoc] using
        hprotocolFinal
    · simpa [states, emitted, emittedPrefix, List.append_assoc] using
        hcoverFinal

theorem normalRel_node1_failed {cfg : Storage.Config}
    {net : List ConcreteMessage} {now t : Time}
    {candidate : Candidate} {op next : Nat}
    {mailbox : List (Addr × CMsg)} {stage : WriteStage}
    {node2 : Running Storage.Config Nat CMsg} {store : Store}
    {wire2 : Option ConcreteMessage} {tokens2 : List AbstractMessage}
    {a : Experiment.Conf promises}
    (hstoreAddr : cfg.store = "s3")
    (happ : AppOnly mailbox) (hnext : next = op + 1)
    (hnone : take? (answers op) mailbox = none)
    (hstage : stage = .shed ∨ stage = .lost)
    (hn2 : NodeRep cfg store "n2" node2 wire2 tokens2)
    (hprotocol : (protocolMessages net).Perm
      ([((.proc "s3", .proc "n1", .failed op) : ConcreteMessage)] ++
        optionList wire2))
    (hcover : Covers
      (appTokens net ++
        (mailboxTokens mailbox ++ candidate.stageTokens stage) ++
        tokens2) a.net)
    (hstore : StoreRep store a.state) (htime : a.now ≤ now)
    (hstepTime : now ≤ t) (source : Network.Who)
    (pre post : List ConcreteMessage)
    (hnet : net = pre ++
      ((.proc "s3", .proc "n1", .failed op) : ConcreteMessage) :: post) :
    ∃ running rest wire tokens,
      let states : List (Addr × Local) :=
        [("n1", .node running), ("n2", .node node2), ("s3", .store store)]
      let emitted : List (Out CMsg) :=
        .send candidate.client (.app (.res candidate.id ⟨503, none⟩)) :: rest
      (toStep node 64 source.addr (.failed op) t cfg
        (⟨next, mailbox,
          writeK candidate.tries (candidate.call.retry candidate.tries)
            candidate op⟩ : Running Storage.Config Nat CMsg)).val =
          [((), running, emitted)] ∧
      RestartRep cfg store "n1" running rest wire tokens ∧
      NormalRel cfg
        ⟨pre ++ post ++ routedOuts states "n1" emitted, states, t⟩ a := by
  obtain ⟨running, rest, wire, tokens, hrun, hrestart, htokens⟩ :=
    writing_failed_restart (cfg := cfg) (store := store) (address := "n1")
      happ hnone source.addr t
  let states : List (Addr × Local) :=
    [("n1", .node running), ("n2", .node node2), ("s3", .store store)]
  let emitted : List (Out CMsg) :=
    .send candidate.client (.app (.res candidate.id ⟨503, none⟩)) :: rest
  have hrouteStore :
      (⟨[], states, 0⟩ : Network.Conf system).route cfg.store =
        .proc cfg.store := by
    simp [states, hstoreAddr, Network.Conf.route, Network.Conf.isProc]
  obtain ⟨hrouteProtocol, hrouteApp⟩ :=
    hrestart.routedResponse hrouteStore
      (client := candidate.client) (id := candidate.id)
      (response := ⟨503, none⟩)
  rw [hnet] at hprotocol hcover
  have hbase :
      (protocolMessages pre ++ protocolMessages post).Perm
        (optionList wire2) := by
    apply Perm.cancel_exposed
    simpa [protocolMessages, List.append_assoc] using hprotocol
  have hprotocolFinal :
      (protocolMessages
        (pre ++ post ++ routedOuts states "n1" emitted)).Perm
        (optionList wire ++ optionList wire2) := by
    rw [protocolMessages_append, protocolMessages_append, hrouteProtocol]
    have hp := hbase.append_right (optionList wire)
    have hswap :
        (optionList wire2 ++ optionList wire).Perm
          (optionList wire ++ optionList wire2) :=
      List.perm_append_comm
    simpa [List.append_assoc] using hp.trans hswap
  have hold : Covers
      (appTokens pre ++ appTokens post ++
        (mailboxTokens mailbox ++ candidate.stageTokens stage) ++
        tokens2) a.net := by
    simpa [appTokens, appToken, List.append_assoc] using hcover
  have hcoverFinal : Covers
      (appTokens (pre ++ post ++ routedOuts states "n1" emitted) ++
        tokens ++ tokens2) a.net := by
    rw [appTokens_append, appTokens_append, hrouteApp]
    rcases hstage with rfl | rfl
    · have hlocal :
          (mailboxTokens mailbox ++
              [responseToken candidate.client candidate.id ⟨503, none⟩]).Perm
            ([responseToken candidate.client candidate.id ⟨503, none⟩] ++
              tokens) := by
        exact (List.perm_append_comm.trans
          (List.Perm.append_left
            [responseToken candidate.client candidate.id ⟨503, none⟩]
            htokens.symm))
      apply Covers.of_perm _ hold
      simpa [Candidate.stageTokens, List.append_assoc] using
        (List.Perm.append_right tokens2
          (List.Perm.append_left (appTokens pre ++ appTokens post) hlocal))
    · have hlocal :
          (mailboxTokens mailbox ++ outputTokens candidate.outs ++
              [responseToken candidate.client candidate.id ⟨503, none⟩]).Perm
            ([responseToken candidate.client candidate.id ⟨503, none⟩] ++
              tokens ++ outputTokens candidate.outs) := by
        have hfirst :
            (mailboxTokens mailbox ++ outputTokens candidate.outs ++
                [responseToken candidate.client candidate.id ⟨503, none⟩]).Perm
              ([responseToken candidate.client candidate.id ⟨503, none⟩] ++
                mailboxTokens mailbox ++ outputTokens candidate.outs) := by
          simpa [List.append_assoc] using
            (List.perm_append_comm :
              (mailboxTokens mailbox ++ outputTokens candidate.outs ++
                [responseToken candidate.client candidate.id ⟨503, none⟩]).Perm
              ([responseToken candidate.client candidate.id ⟨503, none⟩] ++
                mailboxTokens mailbox ++ outputTokens candidate.outs))
        have hsecond :
            ([responseToken candidate.client candidate.id ⟨503, none⟩] ++
                mailboxTokens mailbox ++ outputTokens candidate.outs).Perm
              ([responseToken candidate.client candidate.id ⟨503, none⟩] ++
                tokens ++ outputTokens candidate.outs) := by
          simpa [List.append_assoc] using
            (List.Perm.append_left
              [responseToken candidate.client candidate.id ⟨503, none⟩]
              (htokens.symm.append_right (outputTokens candidate.outs)))
        exact hfirst.trans hsecond
      have hglobal :
          (appTokens pre ++ appTokens post ++
              (mailboxTokens mailbox ++ candidate.stageTokens .lost) ++
              tokens2).Perm
            ((appTokens pre ++ appTokens post ++
              [responseToken candidate.client candidate.id ⟨503, none⟩] ++
              tokens ++ tokens2) ++ outputTokens candidate.outs) := by
        have hwith :=
          List.Perm.append_right tokens2
            (List.Perm.append_left (appTokens pre ++ appTokens post) hlocal)
        have hmove :
            (appTokens pre ++ appTokens post ++
                ([responseToken candidate.client candidate.id ⟨503, none⟩] ++
                  tokens ++ outputTokens candidate.outs) ++ tokens2).Perm
              ((appTokens pre ++ appTokens post ++
                [responseToken candidate.client candidate.id ⟨503, none⟩] ++
                tokens ++ tokens2) ++ outputTokens candidate.outs) := by
          simpa [List.append_assoc] using
            (List.Perm.append_left
              (appTokens pre ++ appTokens post ++
                [responseToken candidate.client candidate.id ⟨503, none⟩] ++
                tokens)
              (List.perm_append_comm :
                (outputTokens candidate.outs ++ tokens2).Perm
                  (tokens2 ++ outputTokens candidate.outs)))
        simpa [Candidate.stageTokens, List.append_assoc] using
          hwith.trans hmove
      apply Covers.weaken (extra := outputTokens candidate.outs)
      exact Covers.of_perm hglobal hold
  refine ⟨running, rest, wire, tokens, ?_, hrestart, ?_⟩
  · simpa [emitted] using hrun
  · refine ⟨running, node2, store, wire, wire2, tokens, tokens2,
      rfl, hrestart.nodeRep, hn2, ?_, ?_, hstore,
      Nat.le_trans htime hstepTime⟩
    · simpa [states, emitted, List.append_assoc] using hprotocolFinal
    · simpa [states, emitted, List.append_assoc] using hcoverFinal

theorem normalRel_node2_failed {cfg : Storage.Config}
    {net : List ConcreteMessage} {now t : Time}
    {candidate : Candidate} {op next : Nat}
    {mailbox : List (Addr × CMsg)} {stage : WriteStage}
    {node1 : Running Storage.Config Nat CMsg} {store : Store}
    {wire1 : Option ConcreteMessage} {tokens1 : List AbstractMessage}
    {a : Experiment.Conf promises}
    (hstoreAddr : cfg.store = "s3")
    (hn1 : NodeRep cfg store "n1" node1 wire1 tokens1)
    (happ : AppOnly mailbox) (hnext : next = op + 1)
    (hnone : take? (answers op) mailbox = none)
    (hstage : stage = .shed ∨ stage = .lost)
    (hprotocol : (protocolMessages net).Perm
      (optionList wire1 ++
        [((.proc "s3", .proc "n2", .failed op) : ConcreteMessage)]))
    (hcover : Covers
      (appTokens net ++ tokens1 ++
        (mailboxTokens mailbox ++ candidate.stageTokens stage)) a.net)
    (hstore : StoreRep store a.state) (htime : a.now ≤ now)
    (hstepTime : now ≤ t) (source : Network.Who)
    (pre post : List ConcreteMessage)
    (hnet : net = pre ++
      ((.proc "s3", .proc "n2", .failed op) : ConcreteMessage) :: post) :
    ∃ running rest wire tokens,
      let states : List (Addr × Local) :=
        [("n1", .node node1), ("n2", .node running), ("s3", .store store)]
      let emitted : List (Out CMsg) :=
        .send candidate.client (.app (.res candidate.id ⟨503, none⟩)) :: rest
      (toStep node 64 source.addr (.failed op) t cfg
        (⟨next, mailbox,
          writeK candidate.tries (candidate.call.retry candidate.tries)
            candidate op⟩ : Running Storage.Config Nat CMsg)).val =
          [((), running, emitted)] ∧
      RestartRep cfg store "n2" running rest wire tokens ∧
      NormalRel cfg
        ⟨pre ++ post ++ routedOuts states "n2" emitted, states, t⟩ a := by
  obtain ⟨running, rest, wire, tokens, hrun, hrestart, htokens⟩ :=
    writing_failed_restart (cfg := cfg) (store := store) (address := "n2")
      happ hnone source.addr t
  let states : List (Addr × Local) :=
    [("n1", .node node1), ("n2", .node running), ("s3", .store store)]
  let emitted : List (Out CMsg) :=
    .send candidate.client (.app (.res candidate.id ⟨503, none⟩)) :: rest
  have hrouteStore :
      (⟨[], states, 0⟩ : Network.Conf system).route cfg.store =
        .proc cfg.store := by
    simp [states, hstoreAddr, Network.Conf.route, Network.Conf.isProc]
  obtain ⟨hrouteProtocol, hrouteApp⟩ :=
    hrestart.routedResponse hrouteStore
      (client := candidate.client) (id := candidate.id)
      (response := ⟨503, none⟩)
  rw [hnet] at hprotocol hcover
  have hbaseProtocol :
      (protocolMessages pre ++ protocolMessages post).Perm
        (optionList wire1) := by
    have hp := hprotocol.trans List.perm_append_comm
    apply Perm.cancel_exposed
    simpa [protocolMessages, List.append_assoc] using hp
  have hprotocolFinal :
      (protocolMessages
        (pre ++ post ++ routedOuts states "n2" emitted)).Perm
        (optionList wire1 ++ optionList wire) := by
    rw [protocolMessages_append, protocolMessages_append, hrouteProtocol]
    simpa [List.append_assoc] using
      hbaseProtocol.append_right (optionList wire)
  have hold : Covers
      (appTokens pre ++ appTokens post ++ tokens1 ++
        (mailboxTokens mailbox ++ candidate.stageTokens stage)) a.net := by
    simpa [appTokens, appToken, List.append_assoc] using hcover
  have hcoverFinal : Covers
      (appTokens (pre ++ post ++ routedOuts states "n2" emitted) ++
        tokens1 ++ tokens) a.net := by
    rw [appTokens_append, appTokens_append, hrouteApp]
    rcases hstage with rfl | rfl
    · have hlocal :
          (mailboxTokens mailbox ++
              [responseToken candidate.client candidate.id ⟨503, none⟩]).Perm
            ([responseToken candidate.client candidate.id ⟨503, none⟩] ++
              tokens) :=
        List.perm_append_comm.trans
          (List.Perm.append_left
            [responseToken candidate.client candidate.id ⟨503, none⟩]
            htokens.symm)
      have hwith :
          (tokens1 ++
              (mailboxTokens mailbox ++
                [responseToken candidate.client candidate.id ⟨503, none⟩])).Perm
            (tokens1 ++
              ([responseToken candidate.client candidate.id ⟨503, none⟩] ++
                tokens)) :=
        List.Perm.append_left tokens1 hlocal
      have hmove :
          (tokens1 ++
              ([responseToken candidate.client candidate.id ⟨503, none⟩] ++
                tokens)).Perm
            ([responseToken candidate.client candidate.id ⟨503, none⟩] ++
              tokens1 ++ tokens) := by
        simpa [List.append_assoc] using
          (List.Perm.append_right tokens
            (List.perm_append_comm :
              (tokens1 ++
                [responseToken candidate.client candidate.id ⟨503, none⟩]).Perm
              ([responseToken candidate.client candidate.id ⟨503, none⟩] ++
                tokens1)))
      apply Covers.of_perm _ hold
      simpa [Candidate.stageTokens, List.append_assoc] using
        (List.Perm.append_left (appTokens pre ++ appTokens post)
          (hwith.trans hmove))
    · have hlocal :
          (mailboxTokens mailbox ++ outputTokens candidate.outs ++
              [responseToken candidate.client candidate.id ⟨503, none⟩]).Perm
            ([responseToken candidate.client candidate.id ⟨503, none⟩] ++
              tokens ++ outputTokens candidate.outs) := by
        have hfirst :
            (mailboxTokens mailbox ++ outputTokens candidate.outs ++
                [responseToken candidate.client candidate.id ⟨503, none⟩]).Perm
              ([responseToken candidate.client candidate.id ⟨503, none⟩] ++
                mailboxTokens mailbox ++ outputTokens candidate.outs) := by
          simpa [List.append_assoc] using
            (List.perm_append_comm :
              (mailboxTokens mailbox ++ outputTokens candidate.outs ++
                [responseToken candidate.client candidate.id ⟨503, none⟩]).Perm
              ([responseToken candidate.client candidate.id ⟨503, none⟩] ++
                mailboxTokens mailbox ++ outputTokens candidate.outs))
        have hsecond :
            ([responseToken candidate.client candidate.id ⟨503, none⟩] ++
                mailboxTokens mailbox ++ outputTokens candidate.outs).Perm
              ([responseToken candidate.client candidate.id ⟨503, none⟩] ++
                tokens ++ outputTokens candidate.outs) := by
          simpa [List.append_assoc] using
            (List.Perm.append_left
              [responseToken candidate.client candidate.id ⟨503, none⟩]
              (htokens.symm.append_right (outputTokens candidate.outs)))
        exact hfirst.trans hsecond
      have hwith :
          (tokens1 ++
              (mailboxTokens mailbox ++ candidate.stageTokens .lost)).Perm
            (tokens1 ++
              ([responseToken candidate.client candidate.id ⟨503, none⟩] ++
                tokens ++ outputTokens candidate.outs)) := by
        simpa [Candidate.stageTokens, List.append_assoc] using
          List.Perm.append_left tokens1 hlocal
      have hmove :
          (tokens1 ++
              ([responseToken candidate.client candidate.id ⟨503, none⟩] ++
                tokens ++ outputTokens candidate.outs)).Perm
            (([responseToken candidate.client candidate.id ⟨503, none⟩] ++
              tokens1 ++ tokens) ++ outputTokens candidate.outs) := by
        have hfront :
            (tokens1 ++
                ([responseToken candidate.client candidate.id ⟨503, none⟩] ++
                  tokens)).Perm
              ([responseToken candidate.client candidate.id ⟨503, none⟩] ++
                tokens1 ++ tokens) := by
          simpa [List.append_assoc] using
            (List.Perm.append_right tokens
              (List.perm_append_comm :
                (tokens1 ++
                  [responseToken candidate.client candidate.id ⟨503, none⟩]).Perm
                ([responseToken candidate.client candidate.id ⟨503, none⟩] ++
                  tokens1)))
        simpa [List.append_assoc] using
          hfront.append_right (outputTokens candidate.outs)
      apply Covers.weaken (extra := outputTokens candidate.outs)
      apply Covers.of_perm _ hold
      simpa [List.append_assoc] using
        (List.Perm.append_left (appTokens pre ++ appTokens post)
          (hwith.trans hmove))
  refine ⟨running, rest, wire, tokens, ?_, hrestart, ?_⟩
  · simpa [emitted] using hrun
  · refine ⟨node1, running, store, wire1, wire, tokens1, tokens,
      rfl, hn1, hrestart.nodeRep, ?_, ?_, hstore,
      Nat.le_trans htime hstepTime⟩
    · simpa [states, emitted, List.append_assoc] using hprotocolFinal
    · simpa [states, emitted, List.append_assoc] using hcoverFinal

theorem linearize_candidate_shed_early {cfg : Storage.Config}
    {candidate : Candidate} {store : Store}
    {a : Experiment.Conf promises}
    {pre post : List (Experiment.Proc × Experiment.Proc × Msg)}
    (hrep : StoreRep store a.state)
    (hnet : a.net =
      pre ++ (.client candidate.client, .server,
        Msg.req candidate.id candidate.now candidate.req) :: post) :
    let serviceOut : List (Out Msg) :=
      [.send candidate.client (Msg.res candidate.id ⟨503, none⟩)]
    let next : Experiment.Conf promises :=
      ⟨pre ++ post ++ Experiment.emits .server
        (.receive (.client candidate.client)
          (Msg.req candidate.id candidate.now candidate.req)) serviceOut,
        a.state, a.now⟩
    Experiment.Legal promises { cfg.app with unreliable := true } a
      [((.server, a.now,
        .receive (.client candidate.client)
          (Msg.req candidate.id candidate.now candidate.req)), serviceOut, next)] ∧
    Experiment.observe
      [((.server, a.now,
        .receive (.client candidate.client)
          (Msg.req candidate.id candidate.now candidate.req)), serviceOut, next)] = [] ∧
    StoreRep store next.state := by
  dsimp
  refine ⟨⟨.receive (r := (a.state,
    [.send candidate.client (Msg.res candidate.id ⟨503, none⟩)]))
    (Nat.le_refl _) hnet ?_, trivial⟩, rfl, hrep⟩
  exact request_step_mem
    (request_shed_mem cfg.app a.state candidate.req candidate.now)

theorem normalRel_node1_conflict_exhausted {cfg : Storage.Config}
    {net : List ConcreteMessage} {now t : Time}
    {candidate : Candidate} {op next : Nat}
    {mailbox : List (Addr × CMsg)}
    {node2 : Running Storage.Config Nat CMsg} {store : Store}
    {wire2 : Option ConcreteMessage} {tokens2 : List AbstractMessage}
    {a : Experiment.Conf promises}
    (hstoreAddr : cfg.store = "s3")
    (happ : AppOnly mailbox) (hnext : next = op + 1)
    (hnone : take? (answers op) mailbox = none)
    (htries : candidate.tries = 0)
    (hn2 : NodeRep cfg store "n2" node2 wire2 tokens2)
    (hprotocol : (protocolMessages net).Perm
      ([((.proc "s3", .proc "n1", .conflict op) : ConcreteMessage)] ++
        optionList wire2))
    (hcover : Covers
      (appTokens net ++
        (mailboxTokens mailbox ++ candidate.stageTokens .pending) ++
        tokens2) a.net)
    (hstore : StoreRep store a.state) (htime : a.now ≤ now)
    (hstepTime : now ≤ t) (source : Network.Who)
    (pre post : List ConcreteMessage)
    (hnet : net = pre ++
      ((.proc "s3", .proc "n1", .conflict op) : ConcreteMessage) :: post) :
    ∃ a' running rest wire tokens,
      let states : List (Addr × Local) :=
        [("n1", .node running), ("n2", .node node2), ("s3", .store store)]
      let emitted : List (Out CMsg) :=
        .send candidate.client (.app (.res candidate.id ⟨503, none⟩)) :: rest
      Network.Matches { cfg.app with unreliable := true } clientView a
        (.proc "n1", t, .receive source (CMsg.conflict op)) a' ∧
      (toStep node 64 source.addr (.conflict op) t cfg
        (⟨next, mailbox,
          writeK candidate.tries (candidate.call.retry candidate.tries)
            candidate op⟩ : Running Storage.Config Nat CMsg)).val =
          [((), running, emitted)] ∧
      RestartRep cfg store "n1" running rest wire tokens ∧
      NormalRel cfg
        ⟨pre ++ post ++ routedOuts states "n1" emitted, states, t⟩ a' := by
  rw [hnet] at hcover
  have hc : Covers
      ((appTokens pre ++ appTokens post ++ mailboxTokens mailbox) ++
        candidate.call.token :: tokens2) a.net := by
    simpa [appTokens, appToken, Candidate.stageTokens,
      List.append_assoc] using hcover
  obtain ⟨apre, apost, hanet, hcRest⟩ := Covers.consume hc
  have hlin := linearize_candidate_shed_early
    (cfg := cfg) (candidate := candidate) hstore hanet
  dsimp at hlin
  obtain ⟨hlegal, hobs, hstore'⟩ := hlin
  let response : AbstractMessage :=
    responseToken candidate.client candidate.id ⟨503, none⟩
  let a' : Experiment.Conf promises :=
    ⟨apre ++ apost ++ [response], a.state, a.now⟩
  have haeq : a' =
      ⟨apre ++ apost ++ Experiment.emits .server
        (.receive (.client candidate.client)
          (Msg.req candidate.id candidate.now candidate.req))
        [.send candidate.client (Msg.res candidate.id ⟨503, none⟩)],
        a.state, a.now⟩ := by
    simp [a', response, responseToken, Experiment.emits, sends]
  obtain ⟨running, rest, wire, tokens, hrun, hrestart, htokens⟩ :=
    writing_conflict_exhausted_restart
      (cfg := cfg) (store := store) (address := "n1")
      happ hnone htries source.addr t
  let states : List (Addr × Local) :=
    [("n1", .node running), ("n2", .node node2), ("s3", .store store)]
  let emitted : List (Out CMsg) :=
    .send candidate.client (.app (.res candidate.id ⟨503, none⟩)) :: rest
  have hrouteStore :
      (⟨[], states, 0⟩ : Network.Conf system).route cfg.store =
        .proc cfg.store := by
    simp [states, hstoreAddr, Network.Conf.route, Network.Conf.isProc]
  obtain ⟨hrouteProtocol, hrouteApp⟩ :=
    hrestart.routedResponse hrouteStore
      (client := candidate.client) (id := candidate.id)
      (response := ⟨503, none⟩)
  rw [hnet] at hprotocol
  have hbase :
      (protocolMessages pre ++ protocolMessages post).Perm
        (optionList wire2) := by
    apply Perm.cancel_exposed
    simpa [protocolMessages, List.append_assoc] using hprotocol
  have hprotocolFinal :
      (protocolMessages
        (pre ++ post ++ routedOuts states "n1" emitted)).Perm
        (optionList wire ++ optionList wire2) := by
    rw [protocolMessages_append, protocolMessages_append, hrouteProtocol]
    have hp := hbase.append_right (optionList wire)
    exact (by
      simpa [List.append_assoc] using hp.trans
        (List.perm_append_comm :
          (optionList wire2 ++ optionList wire).Perm
            (optionList wire ++ optionList wire2)))
  have hcAdded := Covers.insert_both
    (left := appTokens pre ++ appTokens post ++ mailboxTokens mailbox)
    (right := tokens2) (added := [response]) hcRest
  have hcoverFinal : Covers
      (appTokens (pre ++ post ++ routedOuts states "n1" emitted) ++
        tokens ++ tokens2) a'.net := by
    rw [appTokens_append, appTokens_append, hrouteApp]
    apply Covers.of_perm _ hcAdded
    have hlocal :
        (mailboxTokens mailbox ++ [response]).Perm
          ([response] ++ tokens) :=
      List.perm_append_comm.trans
        (List.Perm.append_left [response] htokens.symm)
    simpa [a', List.append_assoc] using
      (List.Perm.append_right tokens2
        (List.Perm.append_left (appTokens pre ++ appTokens post) hlocal))
  refine ⟨a', running, rest, wire, tokens, ?_, ?_, hrestart, ?_⟩
  · refine ⟨[((.server, a.now,
      .receive (.client candidate.client)
        (Msg.req candidate.id candidate.now candidate.req)),
      [.send candidate.client (Msg.res candidate.id ⟨503, none⟩)], a')],
      ?_, hobs, rfl⟩
    simpa [haeq] using hlegal
  · simpa [emitted] using hrun
  · refine ⟨running, node2, store, wire, wire2, tokens, tokens2,
      rfl, hrestart.nodeRep, hn2, ?_, ?_, ?_,
      Nat.le_trans htime hstepTime⟩
    · simpa [states, emitted, List.append_assoc] using hprotocolFinal
    · simpa [states, emitted, List.append_assoc] using hcoverFinal
    · simpa [a', haeq] using hstore'

theorem NormalRel.clientRequest {cfg : Storage.Config}
    {c : Network.Conf system} {a : Experiment.Conf promises}
    (hrel : NormalRel cfg c a) (client to : Addr) (t : Time) (m : Msg) :
    NormalRel cfg
      ⟨c.net ++ [(.client client, .proc to, .app m)], c.states, t⟩
      ⟨a.net ++ [(.client client, .server, m)], a.state, t⟩ := by
  obtain ⟨node1, node2, store, wire1, wire2, tokens1, tokens2,
    hstates, hn1, hn2, hprotocol, hcover, hstore, htime⟩ := hrel
  refine ⟨node1, node2, store, wire1, wire2, tokens1, tokens2,
    hstates, hn1, hn2, ?_, ?_, hstore, Nat.le_refl t⟩
  · simpa [protocolMessages] using hprotocol
  · simpa [appTokens, appToken, List.append_assoc] using
      (Covers.insert_both
        (left := appTokens c.net) (right := tokens1 ++ tokens2)
        (added := [((.client client, .server, m) : AbstractMessage)])
        (by simpa [List.append_assoc] using hcover))

theorem NormalRel.clientReceive {cfg : Storage.Config}
    {c : Network.Conf system} {a : Experiment.Conf promises}
    (hrel : NormalRel cfg c a) (sender : Network.Who) (client : Addr)
    (t : Time) (m : Msg)
    (pre post : List ConcreteMessage)
    (hnet : c.net = pre ++
      (sender, .client client, .app m) :: post) :
    ∃ apre apost,
      a.net = apre ++ (.server, .client client, m) :: apost ∧
      NormalRel cfg
        ⟨pre ++ post, c.states, t⟩
        ⟨apre ++ apost, a.state, t⟩ := by
  obtain ⟨node1, node2, store, wire1, wire2, tokens1, tokens2,
    hstates, hn1, hn2, hprotocol, hcover, hstore, htime⟩ := hrel
  rw [hnet] at hprotocol hcover
  have hc : Covers
      (appTokens pre ++
        (.server, .client client, m) ::
          (appTokens post ++ tokens1 ++ tokens2)) a.net := by
    simpa [appTokens, appToken, List.append_assoc] using hcover
  obtain ⟨apre, apost, hanet, hc'⟩ := Covers.consume hc
  refine ⟨apre, apost, hanet, node1, node2, store, wire1, wire2,
    tokens1, tokens2, hstates, hn1, hn2, ?_, ?_, hstore, Nat.le_refl t⟩
  · simpa [protocolMessages, List.append_assoc] using hprotocol
  · simpa [appTokens, List.append_assoc] using hc'

theorem NormalRel.storeApp {cfg : Storage.Config}
    {net : List ConcreteMessage} {now t : Time}
    {node1 node2 : Running Storage.Config Nat CMsg} {store : Store}
    {a : Experiment.Conf promises}
    (hrel : NormalRel cfg
      ⟨net, [("n1", .node node1), ("n2", .node node2), ("s3", .store store)],
        now⟩ a)
    (source : Network.Who) (message : Msg) (hstepTime : now ≤ t)
    (pre post : List ConcreteMessage)
    (hnet : net = pre ++ (source, .proc "s3", .app message) :: post) :
    NormalRel cfg
      ⟨pre ++ post,
        [("n1", .node node1), ("n2", .node node2), ("s3", .store store)], t⟩ a := by
  obtain ⟨represented1, represented2, representedStore,
    wire1, wire2, tokens1, tokens2,
    hstates, hn1, hn2, hprotocol, hcover, hstore, htime⟩ := hrel
  simp only [List.cons.injEq, Prod.mk.injEq, true_and, and_true,
    Local.node.injEq, Local.store.injEq] at hstates
  obtain ⟨rfl, rfl, rfl⟩ := hstates
  refine ⟨node1, node2, store, wire1, wire2, tokens1, tokens2,
    rfl, hn1, hn2, ?_, ?_, hstore, Nat.le_trans htime hstepTime⟩
  · rw [hnet] at hprotocol
    simpa [protocolMessages, List.append_assoc] using hprotocol
  · rw [hnet] at hcover
    cases source with
    | client client =>
      have hc : Covers
          (appTokens pre ++
            (.client client, .server, message) ::
              (appTokens post ++ tokens1 ++ tokens2)) a.net := by
        simpa [appTokens, appToken, List.append_assoc] using hcover
      simpa [appTokens, List.append_assoc] using Covers.drop_middle hc
    | proc sender =>
      cases message with
      | req id requestNow request =>
        have hc : Covers
            (appTokens pre ++
              (.client sender, .server, .req id requestNow request) ::
                (appTokens post ++ tokens1 ++ tokens2)) a.net := by
          simpa [appTokens, appToken, List.append_assoc] using hcover
        simpa [appTokens, List.append_assoc] using Covers.drop_middle hc
      | res id response =>
        have hc : Covers
            (appTokens pre ++
              (.server, .client "s3", .res id response) ::
                (appTokens post ++ tokens1 ++ tokens2)) a.net := by
          simpa [appTokens, appToken, List.append_assoc] using hcover
        simpa [appTokens, List.append_assoc] using Covers.drop_middle hc
      | notify promise =>
        have hc : Covers
            (appTokens pre ++
              (.server, .client "s3", .notify promise) ::
                (appTokens post ++ tokens1 ++ tokens2)) a.net := by
          simpa [appTokens, appToken, List.append_assoc] using hcover
        simpa [appTokens, List.append_assoc] using Covers.drop_middle hc

theorem NormalRel.node1AppNonrequest {cfg : Storage.Config}
    {net : List ConcreteMessage} {now : Time}
    {node1 node2 : Running Storage.Config Nat CMsg} {store : Store}
    {a : Experiment.Conf promises}
    (hrel : NormalRel cfg
      ⟨net, [("n1", .node node1), ("n2", .node node2), ("s3", .store store)],
        now⟩ a)
    (source : Network.Who) (message : Msg) (t : Time)
    (hstepTime : now ≤ t)
    (hm : isRequest source.addr (.app message) = false)
    (pre post : List ConcreteMessage)
    (hnet : net = pre ++ (source, .proc "n1", .app message) :: post) :
    ∃ node1',
      (toStep node 64 source.addr (.app message) t cfg node1).val =
        [((), node1', [])] ∧
      NormalRel cfg
        ⟨pre ++ post,
          [("n1", .node node1'), ("n2", .node node2), ("s3", .store store)],
          t⟩ a := by
  obtain ⟨represented1, represented2, representedStore,
    wire1, wire2, tokens1, tokens2,
    hstates, hn1, hn2, hprotocol, hcover, hstore, htime⟩ := hrel
  simp only [List.cons.injEq, Prod.mk.injEq, true_and, and_true,
    Local.node.injEq, Local.store.injEq] at hstates
  obtain ⟨rfl, rfl, rfl⟩ := hstates
  obtain ⟨nextNode1, hrun, hn1'⟩ :=
    hn1.receive_app_nonrequest message t hm
  refine ⟨nextNode1, hrun, nextNode1, node2, store, wire1, wire2,
    tokens1, tokens2, rfl, hn1', hn2, ?_, ?_, hstore,
    Nat.le_trans htime hstepTime⟩
  · rw [hnet] at hprotocol
    simpa [protocolMessages, List.append_assoc] using hprotocol
  · rw [hnet] at hcover
    cases source with
    | client client =>
      have hc : Covers
          (appTokens pre ++
            (.client client, .server, message) ::
              (appTokens post ++ tokens1 ++ tokens2)) a.net := by
        simpa [appTokens, appToken, List.append_assoc] using hcover
      simpa [appTokens, List.append_assoc] using Covers.drop_middle hc
    | proc sender =>
      cases message with
      | req id now request => simp [isRequest] at hm
      | res id response =>
        have hc : Covers
            (appTokens pre ++
              (.server, .client "n1", .res id response) ::
                (appTokens post ++ tokens1 ++ tokens2)) a.net := by
          simpa [appTokens, appToken, List.append_assoc] using hcover
        simpa [appTokens, List.append_assoc] using Covers.drop_middle hc
      | notify promise =>
        have hc : Covers
            (appTokens pre ++
              (.server, .client "n1", .notify promise) ::
                (appTokens post ++ tokens1 ++ tokens2)) a.net := by
          simpa [appTokens, appToken, List.append_assoc] using hcover
        simpa [appTokens, List.append_assoc] using Covers.drop_middle hc

theorem normalRel_node1_nonrequest {cfg : Storage.Config}
    {net : List ConcreteMessage} {now : Time}
    {node1 node2 : Running Storage.Config Nat CMsg} {store : Store}
    {wire1 wire2 : Option ConcreteMessage}
    {tokens1 tokens2 : List AbstractMessage}
    {a : Experiment.Conf promises}
    (hn1 : NodeRep cfg store "n1" node1 wire1 tokens1)
    (hn2 : NodeRep cfg store "n2" node2 wire2 tokens2)
    (hprotocol : (protocolMessages net).Perm
      (optionList wire1 ++ optionList wire2))
    (hcover : Covers (appTokens net ++ tokens1 ++ tokens2) a.net)
    (hstore : StoreRep store a.state) (htime : a.now ≤ now)
    (source : Network.Who) (message : Msg) (t : Time)
    (hstepTime : now ≤ t)
    (hm : isRequest source.addr (.app message) = false)
    (pre post : List ConcreteMessage)
    (hnet : net = pre ++ (source, .proc "n1", .app message) :: post) :
    ∃ node1',
      (toStep node 64 source.addr (.app message) t cfg node1).val =
        [((), node1', [])] ∧
      NormalRel cfg
        ⟨pre ++ post,
          [("n1", .node node1'), ("n2", .node node2), ("s3", .store store)],
          t⟩ a :=
  NormalRel.node1AppNonrequest
    ⟨node1, node2, store, wire1, wire2, tokens1, tokens2,
      rfl, hn1, hn2, hprotocol, hcover, hstore, htime⟩
    source message t hstepTime hm pre post hnet

theorem normalRel_node1_request_idle {cfg : Storage.Config}
    {net : List ConcreteMessage} {now : Time}
    {next : Nat} {mailbox : List (Addr × CMsg)}
    {node2 : Running Storage.Config Nat CMsg} {store : Store}
    {wire2 : Option ConcreteMessage} {tokens2 : List AbstractMessage}
    {a : Experiment.Conf promises}
    (hstoreAddr : cfg.store = "s3")
    (happ : AppOnly mailbox) (hn : take? isRequest mailbox = none)
    (hn2 : NodeRep cfg store "n2" node2 wire2 tokens2)
    (hprotocol : (protocolMessages net).Perm (optionList wire2))
    (hcover : Covers
      (appTokens net ++ mailboxTokens mailbox ++ tokens2) a.net)
    (hstore : StoreRep store a.state) (htime : a.now ≤ now)
    (source : Network.Who) (id : CallId) (requestNow t : Time)
    (request : Request) (hstepTime : now ≤ t)
    (pre post : List ConcreteMessage)
    (hnet : net =
      pre ++ (source, .proc "n1", .app (.req id requestNow request)) :: post) :
    let nextNode : Running Storage.Config Nat CMsg :=
      ⟨next + 1, mailbox,
        loadK cfg.retries
          (Call.retry ⟨source.addr, id, request, requestNow⟩ cfg.retries)
          source.addr id request requestNow next⟩
    let wire : ConcreteMessage :=
      (.proc "n1", .proc "s3", .get next request.key)
    (toStep node 64 source.addr (.app (.req id requestNow request)) t cfg
      ⟨next, mailbox, node⟩).val =
        [((), nextNode, [.send "s3" (.get next request.key)])] ∧
    NormalRel cfg
      ⟨pre ++ post ++ [wire],
        [("n1", .node nextNode), ("n2", .node node2), ("s3", .store store)],
        t⟩ a := by
  dsimp
  constructor
  · simpa [hstoreAddr] using
      (idle_request_run (cfg := cfg) happ hn next source.addr id
        requestNow t request)
  · let call : Call := ⟨source.addr, id, request, requestNow⟩
    let wire : ConcreteMessage :=
      (.proc "n1", .proc "s3", .get next request.key)
    refine ⟨_, node2, store, some wire, wire2,
      mailboxTokens mailbox ++ [call.token], tokens2,
      rfl, ?_, hn2, ?_, ?_, hstore, Nat.le_trans htime hstepTime⟩
    · simpa [wire, call, hstoreAddr] using
        (NodeRep.loadingGet
          (cfg := cfg) (store := store) (address := "n1")
          (call := call) (tries := cfg.retries) happ rfl
          (answers_none_of_appOnly mailbox next happ))
    · rw [hnet] at hprotocol
      have hp := hprotocol.append_right [wire]
      have hswap :
          (optionList wire2 ++ [wire]).Perm
            ([wire] ++ optionList wire2) := List.perm_append_comm
      simpa [wire, protocolMessages, optionList, List.append_assoc] using
        hp.trans hswap
    · rw [hnet] at hcover
      have hat : appToken
          (source, .proc "n1", .app (.req id requestNow request)) =
          some call.token := by
        cases source <;> rfl
      have hwire' : appToken
          ((.proc "n1", .proc "s3", .get next request.key) :
            ConcreteMessage) = none := rfl
      apply Covers.of_perm _ hcover
      simp only [appTokens, List.filterMap_append, List.filterMap_cons,
        hat, hwire', List.filterMap_nil, List.append_nil]
      simpa only [List.append_assoc, List.cons_append, List.nil_append,
        List.append_nil, appTokens] using
        (List.Perm.append_left (appTokens pre)
          (perm_append_cons_head
            (appTokens post ++ mailboxTokens mailbox)
            tokens2 call.token).symm)

theorem normalRel_node1_request_busy {cfg : Storage.Config}
    {net : List ConcreteMessage} {now : Time}
    {node1 node2 : Running Storage.Config Nat CMsg} {store : Store}
    {wire1 wire2 : Option ConcreteMessage}
    {tokens1 tokens2 : List AbstractMessage}
    {a : Experiment.Conf promises}
    (hn1 : NodeRep cfg store "n1" node1 wire1 tokens1)
    (hn2 : NodeRep cfg store "n2" node2 wire2 tokens2)
    (hbusy : wire1 ≠ none)
    (hprotocol : (protocolMessages net).Perm
      (optionList wire1 ++ optionList wire2))
    (hcover : Covers (appTokens net ++ tokens1 ++ tokens2) a.net)
    (hstore : StoreRep store a.state) (htime : a.now ≤ now)
    (source : Network.Who) (id : CallId) (requestNow t : Time)
    (request : Request) (hstepTime : now ≤ t)
    (pre post : List ConcreteMessage)
    (hnet : net =
      pre ++ (source, .proc "n1", .app (.req id requestNow request)) :: post) :
    ∃ node1',
      (toStep node 64 source.addr (.app (.req id requestNow request)) t cfg
        node1).val = [((), node1', [])] ∧
      NormalRel cfg
        ⟨pre ++ post,
          [("n1", .node node1'), ("n2", .node node2), ("s3", .store store)],
          t⟩ a := by
  obtain ⟨nextNode1, nextTokens1, hrun, hn1', htokens⟩ :=
    hn1.receive_app_request_busy id requestNow t request hbusy
  refine ⟨nextNode1, hrun, nextNode1, node2, store, wire1, wire2,
    nextTokens1, tokens2, rfl, hn1', hn2, ?_, ?_, hstore,
    Nat.le_trans htime hstepTime⟩
  · rw [hnet] at hprotocol
    simpa [protocolMessages, List.append_assoc] using hprotocol
  · rw [hnet] at hcover
    let token : AbstractMessage :=
      Call.token ⟨source.addr, id, request, requestNow⟩
    have happ : appToken
        (source, .proc "n1", .app (.req id requestNow request)) =
        some token := by
      cases source <;> rfl
    have hc : Covers
        (appTokens pre ++ token ::
          (appTokens post ++ tokens1 ++ tokens2)) a.net := by
      simpa [appTokens, happ, List.append_assoc] using hcover
    apply Covers.of_perm _ hc
    have hmove :
        (appTokens pre ++ token ::
          (appTokens post ++ tokens1 ++ tokens2)).Perm
        (appTokens pre ++ appTokens post ++
          (tokens1 ++ [token]) ++ tokens2) := by
      simpa [List.append_assoc, List.cons_append] using
        (List.Perm.append_left (appTokens pre)
          (perm_append_cons_head
            (appTokens post ++ tokens1) tokens2 token).symm)
    exact hmove.trans (by
      simpa [appTokens, List.append_assoc] using
        (List.Perm.append
          (List.Perm.refl (appTokens pre ++ appTokens post))
          (htokens.symm.append_right tokens2)))

theorem normalRel_node2_nonrequest {cfg : Storage.Config}
    {net : List ConcreteMessage} {now : Time}
    {node1 node2 : Running Storage.Config Nat CMsg} {store : Store}
    {wire1 wire2 : Option ConcreteMessage}
    {tokens1 tokens2 : List AbstractMessage}
    {a : Experiment.Conf promises}
    (hn1 : NodeRep cfg store "n1" node1 wire1 tokens1)
    (hn2 : NodeRep cfg store "n2" node2 wire2 tokens2)
    (hprotocol : (protocolMessages net).Perm
      (optionList wire1 ++ optionList wire2))
    (hcover : Covers (appTokens net ++ tokens1 ++ tokens2) a.net)
    (hstore : StoreRep store a.state) (htime : a.now ≤ now)
    (source : Network.Who) (message : Msg) (t : Time)
    (hstepTime : now ≤ t)
    (hm : isRequest source.addr (.app message) = false)
    (pre post : List ConcreteMessage)
    (hnet : net = pre ++ (source, .proc "n2", .app message) :: post) :
    ∃ node2',
      (toStep node 64 source.addr (.app message) t cfg node2).val =
        [((), node2', [])] ∧
      NormalRel cfg
        ⟨pre ++ post,
          [("n1", .node node1), ("n2", .node node2'), ("s3", .store store)],
          t⟩ a := by
  obtain ⟨nextNode2, hrun, hn2'⟩ :=
    hn2.receive_app_nonrequest message t hm
  refine ⟨nextNode2, hrun, node1, nextNode2, store, wire1, wire2,
    tokens1, tokens2, rfl, hn1, hn2', ?_, ?_, hstore,
    Nat.le_trans htime hstepTime⟩
  · rw [hnet] at hprotocol
    simpa [protocolMessages, List.append_assoc] using hprotocol
  · rw [hnet] at hcover
    cases source with
    | client client =>
      have hc : Covers
          (appTokens pre ++
            (.client client, .server, message) ::
              (appTokens post ++ tokens1 ++ tokens2)) a.net := by
        simpa [appTokens, appToken, List.append_assoc] using hcover
      simpa [appTokens, List.append_assoc] using Covers.drop_middle hc
    | proc sender =>
      cases message with
      | req id now request => simp [isRequest] at hm
      | res id response =>
        have hc : Covers
            (appTokens pre ++
              (.server, .client "n2", .res id response) ::
                (appTokens post ++ tokens1 ++ tokens2)) a.net := by
          simpa [appTokens, appToken, List.append_assoc] using hcover
        simpa [appTokens, List.append_assoc] using Covers.drop_middle hc
      | notify promise =>
        have hc : Covers
            (appTokens pre ++
              (.server, .client "n2", .notify promise) ::
                (appTokens post ++ tokens1 ++ tokens2)) a.net := by
          simpa [appTokens, appToken, List.append_assoc] using hcover
        simpa [appTokens, List.append_assoc] using Covers.drop_middle hc

theorem normalRel_node2_request_idle {cfg : Storage.Config}
    {net : List ConcreteMessage} {now : Time}
    {next : Nat} {mailbox : List (Addr × CMsg)}
    {node1 : Running Storage.Config Nat CMsg} {store : Store}
    {wire1 : Option ConcreteMessage} {tokens1 : List AbstractMessage}
    {a : Experiment.Conf promises}
    (hstoreAddr : cfg.store = "s3")
    (hn1 : NodeRep cfg store "n1" node1 wire1 tokens1)
    (happ : AppOnly mailbox) (hn : take? isRequest mailbox = none)
    (hprotocol : (protocolMessages net).Perm (optionList wire1))
    (hcover : Covers
      (appTokens net ++ tokens1 ++ mailboxTokens mailbox) a.net)
    (hstore : StoreRep store a.state) (htime : a.now ≤ now)
    (source : Network.Who) (id : CallId) (requestNow t : Time)
    (request : Request) (hstepTime : now ≤ t)
    (pre post : List ConcreteMessage)
    (hnet : net =
      pre ++ (source, .proc "n2", .app (.req id requestNow request)) :: post) :
    let nextNode : Running Storage.Config Nat CMsg :=
      ⟨next + 1, mailbox,
        loadK cfg.retries
          (Call.retry ⟨source.addr, id, request, requestNow⟩ cfg.retries)
          source.addr id request requestNow next⟩
    let wire : ConcreteMessage :=
      (.proc "n2", .proc "s3", .get next request.key)
    (toStep node 64 source.addr (.app (.req id requestNow request)) t cfg
      ⟨next, mailbox, node⟩).val =
        [((), nextNode, [.send "s3" (.get next request.key)])] ∧
    NormalRel cfg
      ⟨pre ++ post ++ [wire],
        [("n1", .node node1), ("n2", .node nextNode), ("s3", .store store)],
        t⟩ a := by
  dsimp
  constructor
  · simpa [hstoreAddr] using
      (idle_request_run (cfg := cfg) happ hn next source.addr id
        requestNow t request)
  · let call : Call := ⟨source.addr, id, request, requestNow⟩
    let wire : ConcreteMessage :=
      (.proc "n2", .proc "s3", .get next request.key)
    refine ⟨node1, _, store, wire1, some wire,
      tokens1, mailboxTokens mailbox ++ [call.token],
      rfl, hn1, ?_, ?_, ?_, hstore, Nat.le_trans htime hstepTime⟩
    · simpa [wire, call, hstoreAddr] using
        (NodeRep.loadingGet
          (cfg := cfg) (store := store) (address := "n2")
          (call := call) (tries := cfg.retries) happ rfl
          (answers_none_of_appOnly mailbox next happ))
    · rw [hnet] at hprotocol
      simpa [wire, protocolMessages, optionList, List.append_assoc] using
        hprotocol.append_right [wire]
    · rw [hnet] at hcover
      have hat : appToken
          (source, .proc "n2", .app (.req id requestNow request)) =
          some call.token := by
        cases source <;> rfl
      have hwire : appToken
          ((.proc "n2", .proc "s3", .get next request.key) :
            ConcreteMessage) = none := rfl
      apply Covers.of_perm _ hcover
      simp only [appTokens, List.filterMap_append, List.filterMap_cons,
        hat, hwire, List.filterMap_nil, List.append_nil]
      simpa only [List.append_assoc, List.cons_append, List.nil_append,
        List.append_nil, appTokens] using
        (List.Perm.append_left (appTokens pre)
          (perm_append_cons_head
            (appTokens post ++ tokens1 ++ mailboxTokens mailbox)
            [] call.token).symm)

theorem normalRel_node2_request_busy {cfg : Storage.Config}
    {net : List ConcreteMessage} {now : Time}
    {node1 node2 : Running Storage.Config Nat CMsg} {store : Store}
    {wire1 wire2 : Option ConcreteMessage}
    {tokens1 tokens2 : List AbstractMessage}
    {a : Experiment.Conf promises}
    (hn1 : NodeRep cfg store "n1" node1 wire1 tokens1)
    (hn2 : NodeRep cfg store "n2" node2 wire2 tokens2)
    (hbusy : wire2 ≠ none)
    (hprotocol : (protocolMessages net).Perm
      (optionList wire1 ++ optionList wire2))
    (hcover : Covers (appTokens net ++ tokens1 ++ tokens2) a.net)
    (hstore : StoreRep store a.state) (htime : a.now ≤ now)
    (source : Network.Who) (id : CallId) (requestNow t : Time)
    (request : Request) (hstepTime : now ≤ t)
    (pre post : List ConcreteMessage)
    (hnet : net =
      pre ++ (source, .proc "n2", .app (.req id requestNow request)) :: post) :
    ∃ node2',
      (toStep node 64 source.addr (.app (.req id requestNow request)) t cfg
        node2).val = [((), node2', [])] ∧
      NormalRel cfg
        ⟨pre ++ post,
          [("n1", .node node1), ("n2", .node node2'), ("s3", .store store)],
          t⟩ a := by
  obtain ⟨nextNode2, nextTokens2, hrun, hn2', htokens⟩ :=
    hn2.receive_app_request_busy id requestNow t request hbusy
  refine ⟨nextNode2, hrun, node1, nextNode2, store, wire1, wire2,
    tokens1, nextTokens2, rfl, hn1, hn2', ?_, ?_, hstore,
    Nat.le_trans htime hstepTime⟩
  · rw [hnet] at hprotocol
    simpa [protocolMessages, List.append_assoc] using hprotocol
  · rw [hnet] at hcover
    let token : AbstractMessage :=
      Call.token ⟨source.addr, id, request, requestNow⟩
    have happ : appToken
        (source, .proc "n2", .app (.req id requestNow request)) =
        some token := by
      cases source <;> rfl
    have hc : Covers
        (appTokens pre ++ token ::
          (appTokens post ++ tokens1 ++ tokens2)) a.net := by
      simpa [appTokens, happ, List.append_assoc] using hcover
    apply Covers.of_perm _ hc
    have hmove :
        (appTokens pre ++ token ::
          (appTokens post ++ tokens1 ++ tokens2)).Perm
        (appTokens pre ++ appTokens post ++ tokens1 ++
          (tokens2 ++ [token])) := by
      simpa [List.append_assoc, List.cons_append] using
        (List.Perm.append_left (appTokens pre)
          (perm_append_cons_head
            (appTokens post ++ tokens1 ++ tokens2) [] token).symm)
    exact hmove.trans (by
      simpa [appTokens, List.append_assoc] using
        (List.Perm.append
          (List.Perm.refl (appTokens pre ++ appTokens post ++ tokens1))
          htokens.symm))

private theorem handler_get_run {E S W : Type} (e : E) (s : S) :
    (get : H E S W S) e s = Some.one (s, s, []) := by rfl

private theorem handler_read_run {E S W : Type} (e : E) (s : S) :
    (read : H E S W E) e s = Some.one (e, s, []) := by rfl

private theorem handler_modify_run {E S W : Type} (e : E) (s : S)
    (f : S → S) :
    (modify f : H E S W Unit) e s = Some.one ((), f s, []) := by rfl

private theorem handler_pure_run {E S W α : Type} (e : E) (s : S)
    (value : α) :
    (pure value : H E S W α) e s = Some.one (value, s, []) := by rfl

private theorem handler_choose_run {E S W α : Type} (e : E) (s : S)
    (values : Some α) :
    (Experiment.choose values : H E S W α) e s =
      values.map (fun value => (value, s, [])) := by rfl

theorem store_get_run (cfg : Storage.Config) (store : Store)
    (sender : Addr) (op : Nat) (key : Ident) :
    ((storeReceive sender (.get op key)).run cfg store).val =
      [((), store, [.send sender (.got op (storeLookup store key))])] := by
  rfl

theorem normalRel_store_get_node1 {cfg : Storage.Config}
    {net : List ConcreteMessage} {now t : Time}
    {call : Call} {tries op next : Nat} {mailbox : List (Addr × CMsg)}
    {node2 : Running Storage.Config Nat CMsg} {store : Store}
    {wire2 : Option ConcreteMessage} {tokens2 : List AbstractMessage}
    {a : Experiment.Conf promises}
    {res : Response} {after : Experiment.State} {outs : List (Out Msg)}
    (hstoreAddr : cfg.store = "s3")
    (happ : AppOnly mailbox) (hnext : next = op + 1)
    (hnone : take? (answers op) mailbox = none)
    (hpick :
      pick ((Experiment.dispatch call.req call.now).run
        { cfg.app with unreliable := true }
        { promises := (storeLookup store call.req.key).toList.map (·.1) }) 0 =
          (res, after, outs))
    (hchanged :
      after ≠ { promises :=
        (storeLookup store call.req.key).toList.map (·.1) })
    (hn2 : NodeRep cfg store "n2" node2 wire2 tokens2)
    (hprotocol : (protocolMessages net).Perm
      ([((.proc "n1", .proc "s3", .get op call.req.key) :
        ConcreteMessage)] ++ optionList wire2))
    (hcover : Covers
      (appTokens net ++
        (mailboxTokens mailbox ++ [call.token]) ++ tokens2) a.net)
    (hstore : StoreRep store a.state) (htime : a.now ≤ now)
    (hstepTime : now ≤ t)
    (pre post : List ConcreteMessage)
    (hnet : net = pre ++
      ((.proc "n1", .proc "s3", .get op call.req.key) :
        ConcreteMessage) :: post) :
    let doc := storeLookup store call.req.key
    let reply : ConcreteMessage := (.proc "s3", .proc "n1", .got op doc)
    ((storeReceive "n1" (.get op call.req.key)).run cfg store).val =
      [((), store, [.send "n1" (.got op doc)])] ∧
    NormalRel cfg
      ⟨pre ++ post ++ [reply],
        [("n1", .node ⟨next, mailbox,
          loadK tries (call.retry tries) call.client call.id call.req call.now op⟩),
         ("n2", .node node2), ("s3", .store store)], t⟩ a := by
  dsimp
  constructor
  · exact store_get_run cfg store "n1" op call.req.key
  · let reply : ConcreteMessage :=
      (.proc "s3", .proc "n1", .got op (storeLookup store call.req.key))
    refine ⟨_, node2, store, some reply, wire2,
      mailboxTokens mailbox ++ [call.token], tokens2,
      rfl, ?_, hn2, ?_, ?_, hstore, Nat.le_trans htime hstepTime⟩
    · simpa [reply, hstoreAddr] using
        (NodeRep.loadingGot
          (cfg := cfg) (store := store) (address := "n1")
          (call := call) (tries := tries)
          happ hnext hnone ⟨res, after, outs, hpick, hchanged⟩
          (Snapshot.of_lookup rfl)
          (docAtKey_of_rep_lookup hstore rfl))
    · rw [hnet] at hprotocol
      have hbase : (protocolMessages pre ++ protocolMessages post).Perm
          (optionList wire2) := by
        apply Perm.cancel_exposed
        simpa [protocolMessages, List.append_assoc] using hprotocol
      have hp := hbase.append_right [reply]
      have hswap :
          (optionList wire2 ++ [reply]).Perm
            ([reply] ++ optionList wire2) := List.perm_append_comm
      simpa [reply, protocolMessages, optionList, List.append_assoc] using
        hp.trans hswap
    · rw [hnet] at hcover
      simpa [reply, appTokens, appToken, List.append_assoc] using hcover

theorem normalRel_store_get_node2 {cfg : Storage.Config}
    {net : List ConcreteMessage} {now t : Time}
    {call : Call} {tries op next : Nat} {mailbox : List (Addr × CMsg)}
    {node1 : Running Storage.Config Nat CMsg} {store : Store}
    {wire1 : Option ConcreteMessage} {tokens1 : List AbstractMessage}
    {a : Experiment.Conf promises}
    {res : Response} {after : Experiment.State} {outs : List (Out Msg)}
    (hstoreAddr : cfg.store = "s3")
    (hn1 : NodeRep cfg store "n1" node1 wire1 tokens1)
    (happ : AppOnly mailbox) (hnext : next = op + 1)
    (hnone : take? (answers op) mailbox = none)
    (hpick :
      pick ((Experiment.dispatch call.req call.now).run
        { cfg.app with unreliable := true }
        { promises := (storeLookup store call.req.key).toList.map (·.1) }) 0 =
          (res, after, outs))
    (hchanged :
      after ≠ { promises :=
        (storeLookup store call.req.key).toList.map (·.1) })
    (hprotocol : (protocolMessages net).Perm
      (optionList wire1 ++
        [((.proc "n2", .proc "s3", .get op call.req.key) :
          ConcreteMessage)]))
    (hcover : Covers
      (appTokens net ++ tokens1 ++
        (mailboxTokens mailbox ++ [call.token])) a.net)
    (hstore : StoreRep store a.state) (htime : a.now ≤ now)
    (hstepTime : now ≤ t)
    (pre post : List ConcreteMessage)
    (hnet : net = pre ++
      ((.proc "n2", .proc "s3", .get op call.req.key) :
        ConcreteMessage) :: post) :
    let doc := storeLookup store call.req.key
    let reply : ConcreteMessage := (.proc "s3", .proc "n2", .got op doc)
    ((storeReceive "n2" (.get op call.req.key)).run cfg store).val =
      [((), store, [.send "n2" (.got op doc)])] ∧
    NormalRel cfg
      ⟨pre ++ post ++ [reply],
        [("n1", .node node1),
         ("n2", .node ⟨next, mailbox,
          loadK tries (call.retry tries) call.client call.id call.req call.now op⟩),
         ("s3", .store store)], t⟩ a := by
  dsimp
  constructor
  · exact store_get_run cfg store "n2" op call.req.key
  · let reply : ConcreteMessage :=
      (.proc "s3", .proc "n2", .got op (storeLookup store call.req.key))
    refine ⟨node1, _, store, wire1, some reply,
      tokens1, mailboxTokens mailbox ++ [call.token],
      rfl, hn1, ?_, ?_, ?_, hstore, Nat.le_trans htime hstepTime⟩
    · simpa [reply, hstoreAddr] using
        (NodeRep.loadingGot
          (cfg := cfg) (store := store) (address := "n2")
          (call := call) (tries := tries)
          happ hnext hnone ⟨res, after, outs, hpick, hchanged⟩
          (Snapshot.of_lookup rfl)
          (docAtKey_of_rep_lookup hstore rfl))
    · rw [hnet] at hprotocol
      have hbase : (protocolMessages pre ++ protocolMessages post).Perm
          (optionList wire1) := by
        have hp := hprotocol.trans List.perm_append_comm
        apply Perm.cancel_exposed
        simpa [protocolMessages, List.append_assoc] using hp
      simpa [reply, protocolMessages, optionList, List.append_assoc] using
        hbase.append_right [reply]
    · rw [hnet] at hcover
      simpa [reply, appTokens, appToken, List.append_assoc] using hcover

theorem store_put_conflict_run {cfg : Storage.Config} {store : Store}
    {sender : Addr} {op : Nat} {key : Ident} {promise : Promise}
    {ifMatch : Option Version}
    (hconditional : cfg.conditional = true)
    (hmismatch : (ifMatch != (storeLookup store key).map (·.2)) = true) :
    ((storeReceive sender (.put op key promise ifMatch)).run cfg store).val =
      [((), store, [.send sender (.conflict op)])] := by
  rcases cfg with ⟨storeAddr, conditional, flaky, retries, app⟩
  change conditional = true at hconditional
  subst conditional
  unfold storeReceive
  have hmismatchRaw : (ifMatch !=
      (store.docs.find? (·.1 == key)).map (·.2.2)) = true := by
    simpa [storeLookup, Function.comp_def] using hmismatch
  have hneRaw : ifMatch ≠
      (store.docs.find? (·.1 == key)).map (·.2.2) :=
    bne_iff_ne.mp hmismatchRaw
  simp [H.run, Bind.bind, Some.bind, Some.map, Some.one,
    handler_get_run, handler_read_run, handler_pure_run, handler_choose_run,
    handler_modify_run, Experiment.Storage.send, Experiment.emit, hneRaw]

theorem store_put_nonflaky_run {cfg : Storage.Config} {store : Store}
    {sender : Addr} {op : Nat} {key : Ident} {promise : Promise}
    {ifMatch : Option Version}
    (hconditional : cfg.conditional = true)
    (hmatch : ifMatch = (storeLookup store key).map (·.2))
    (hflaky : cfg.flaky = false) :
    ((storeReceive sender (.put op key promise ifMatch)).run cfg store).val =
      [((), storeCommit store key promise, [.send sender (.written op)])] := by
  rcases cfg with ⟨storeAddr, conditional, flaky, retries, app⟩
  change conditional = true at hconditional
  subst conditional
  change flaky = false at hflaky
  subst flaky
  unfold storeReceive
  have hmatchRaw : ifMatch =
      (store.docs.find? (·.1 == key)).map (·.2.2) := by
    simpa [storeLookup, Function.comp_def] using hmatch
  simp [H.run, Bind.bind, Some.bind, Some.map, Some.one,
    handler_get_run, handler_read_run, handler_modify_run, handler_pure_run,
    handler_choose_run, Experiment.Storage.send, Experiment.emit,
    storeCommit, storeLookup, Function.comp_def, hmatchRaw]

theorem store_put_flaky_run {cfg : Storage.Config} {store : Store}
    {sender : Addr} {op : Nat} {key : Ident} {promise : Promise}
    {ifMatch : Option Version}
    (hconditional : cfg.conditional = true)
    (hmatch : ifMatch = (storeLookup store key).map (·.2))
    (hflaky : cfg.flaky = true) :
    ((storeReceive sender (.put op key promise ifMatch)).run cfg store).val =
      [((), storeCommit store key promise, [.send sender (.written op)]),
       ((), storeCommit store key promise, [.send sender (.failed op)]),
       ((), store, [.send sender (.failed op)])] := by
  rcases cfg with ⟨storeAddr, conditional, flaky, retries, app⟩
  change conditional = true at hconditional
  subst conditional
  change flaky = true at hflaky
  subst flaky
  unfold storeReceive
  have hmatchRaw : ifMatch =
      (store.docs.find? (·.1 == key)).map (·.2.2) := by
    simpa [storeLookup, Function.comp_def] using hmatch
  simp [H.run, Bind.bind, Some.bind, Some.map, Some.one,
    handler_get_run, handler_read_run, handler_modify_run, handler_pure_run,
    Experiment.Storage.send, Experiment.emit, Experiment.choose,
    storeCommit, storeLookup, Function.comp_def, hmatchRaw]

inductive StorePutOutcome (store : Store) (sender : Addr) (op : Nat)
    (key : Ident) (promise : Promise) (ifMatch : Option Version) :
    Store → List (Out CMsg) → Prop where
  | conflict :
      StorePutOutcome store sender op key promise ifMatch store
        [.send sender (.conflict op)]
  | written :
      ifMatch = (storeLookup store key).map (·.2) →
      StorePutOutcome store sender op key promise ifMatch
        (storeCommit store key promise) [.send sender (.written op)]
  | landedFailed :
      ifMatch = (storeLookup store key).map (·.2) →
      StorePutOutcome store sender op key promise ifMatch
        (storeCommit store key promise) [.send sender (.failed op)]
  | failed :
      StorePutOutcome store sender op key promise ifMatch store
        [.send sender (.failed op)]

theorem store_put_classify {cfg : Storage.Config} {store after : Store}
    {sender : Addr} {op : Nat} {key : Ident} {promise : Promise}
    {ifMatch : Option Version} {outs : List (Out CMsg)}
    (hconditional : cfg.conditional = true)
    (hout : ((), after, outs) ∈
      ((storeReceive sender (.put op key promise ifMatch)).run cfg store).val) :
    StorePutOutcome store sender op key promise ifMatch after outs := by
  by_cases hmatch : ifMatch = (storeLookup store key).map (·.2)
  · cases hflaky : cfg.flaky with
    | false =>
      rw [store_put_nonflaky_run hconditional hmatch hflaky] at hout
      simp only [List.mem_singleton, Prod.mk.injEq, true_and] at hout
      obtain ⟨rfl, rfl⟩ := hout
      exact .written hmatch
    | true =>
      rw [store_put_flaky_run hconditional hmatch hflaky] at hout
      simp only [List.mem_cons, List.not_mem_nil, or_false,
        Prod.mk.injEq, true_and] at hout
      rcases hout with hout | hout | hout
      · obtain ⟨rfl, rfl⟩ := hout
        exact .written hmatch
      · obtain ⟨rfl, rfl⟩ := hout
        exact .landedFailed hmatch
      · obtain ⟨rfl, rfl⟩ := hout
        exact .failed
  · have hmismatch : (ifMatch != (storeLookup store key).map (·.2)) = true :=
      bne_iff_ne.mpr hmatch
    rw [store_put_conflict_run hconditional hmismatch] at hout
    simp only [List.mem_singleton, Prod.mk.injEq, true_and] at hout
    obtain ⟨rfl, rfl⟩ := hout
    exact .conflict

theorem normalRel_store_conflict_node1 {cfg : Storage.Config}
    {net : List ConcreteMessage} {now t : Time}
    {candidate : Candidate} {op next : Nat} {mailbox : List (Addr × CMsg)}
    {node2 : Running Storage.Config Nat CMsg} {store : Store}
    {wire2 : Option ConcreteMessage} {tokens2 : List AbstractMessage}
    {a : Experiment.Conf promises}
    (hstoreAddr : cfg.store = "s3")
    (happ : AppOnly mailbox) (hnext : next = op + 1)
    (hnone : take? (answers op) mailbox = none)
    (hvalid : candidate.Valid cfg)
    (hsnapshot : Snapshot store candidate.req.key candidate.doc)
    (hn2 : NodeRep cfg store "n2" node2 wire2 tokens2)
    (hprotocol : (protocolMessages net).Perm
      ([((.proc "n1", .proc "s3",
        .put op candidate.req.key candidate.promise
          (candidate.doc.map (·.2))) : ConcreteMessage)] ++
        optionList wire2))
    (hcover : Covers
      (appTokens net ++
        (mailboxTokens mailbox ++ candidate.stageTokens .pending) ++
        tokens2) a.net)
    (hstore : StoreRep store a.state) (htime : a.now ≤ now)
    (hstepTime : now ≤ t) (pre post : List ConcreteMessage)
    (hnet : net = pre ++
      ((.proc "n1", .proc "s3",
        .put op candidate.req.key candidate.promise
          (candidate.doc.map (·.2))) : ConcreteMessage) :: post) :
    let reply : ConcreteMessage := (.proc "s3", .proc "n1", .conflict op)
    NormalRel cfg
      ⟨pre ++ post ++ [reply],
        [("n1", .node ⟨next, mailbox,
          writeK candidate.tries (candidate.call.retry candidate.tries)
            candidate op⟩),
         ("n2", .node node2), ("s3", .store store)], t⟩ a := by
  dsimp
  let reply : ConcreteMessage := (.proc "s3", .proc "n1", .conflict op)
  refine ⟨_, node2, store, some reply, wire2,
    mailboxTokens mailbox ++ candidate.stageTokens .pending, tokens2,
    rfl, ?_, hn2, ?_, ?_, hstore, Nat.le_trans htime hstepTime⟩
  · simpa [reply, hstoreAddr] using
      (NodeRep.writingConflict
        (cfg := cfg) (store := store) (address := "n1")
        (candidate := candidate) happ hnext hnone hvalid hsnapshot)
  · rw [hnet] at hprotocol
    have hbase : (protocolMessages pre ++ protocolMessages post).Perm
        (optionList wire2) := by
      apply Perm.cancel_exposed
      simpa [protocolMessages, List.append_assoc] using hprotocol
    have hp := hbase.append_right [reply]
    have hswap :
        (optionList wire2 ++ [reply]).Perm
          ([reply] ++ optionList wire2) := List.perm_append_comm
    simpa [reply, protocolMessages, optionList, List.append_assoc] using
      hp.trans hswap
  · rw [hnet] at hcover
    simpa [reply, appTokens, appToken, List.append_assoc] using hcover

theorem normalRel_store_conflict_node2 {cfg : Storage.Config}
    {net : List ConcreteMessage} {now t : Time}
    {candidate : Candidate} {op next : Nat} {mailbox : List (Addr × CMsg)}
    {node1 : Running Storage.Config Nat CMsg} {store : Store}
    {wire1 : Option ConcreteMessage} {tokens1 : List AbstractMessage}
    {a : Experiment.Conf promises}
    (hstoreAddr : cfg.store = "s3")
    (hn1 : NodeRep cfg store "n1" node1 wire1 tokens1)
    (happ : AppOnly mailbox) (hnext : next = op + 1)
    (hnone : take? (answers op) mailbox = none)
    (hvalid : candidate.Valid cfg)
    (hsnapshot : Snapshot store candidate.req.key candidate.doc)
    (hprotocol : (protocolMessages net).Perm
      (optionList wire1 ++
        [((.proc "n2", .proc "s3",
          .put op candidate.req.key candidate.promise
            (candidate.doc.map (·.2))) : ConcreteMessage)]))
    (hcover : Covers
      (appTokens net ++ tokens1 ++
        (mailboxTokens mailbox ++ candidate.stageTokens .pending)) a.net)
    (hstore : StoreRep store a.state) (htime : a.now ≤ now)
    (hstepTime : now ≤ t) (pre post : List ConcreteMessage)
    (hnet : net = pre ++
      ((.proc "n2", .proc "s3",
        .put op candidate.req.key candidate.promise
          (candidate.doc.map (·.2))) : ConcreteMessage) :: post) :
    let reply : ConcreteMessage := (.proc "s3", .proc "n2", .conflict op)
    NormalRel cfg
      ⟨pre ++ post ++ [reply],
        [("n1", .node node1),
         ("n2", .node ⟨next, mailbox,
          writeK candidate.tries (candidate.call.retry candidate.tries)
            candidate op⟩),
         ("s3", .store store)], t⟩ a := by
  dsimp
  let reply : ConcreteMessage := (.proc "s3", .proc "n2", .conflict op)
  refine ⟨node1, _, store, wire1, some reply,
    tokens1, mailboxTokens mailbox ++ candidate.stageTokens .pending,
    rfl, hn1, ?_, ?_, ?_, hstore, Nat.le_trans htime hstepTime⟩
  · simpa [reply, hstoreAddr] using
      (NodeRep.writingConflict
        (cfg := cfg) (store := store) (address := "n2")
        (candidate := candidate) happ hnext hnone hvalid hsnapshot)
  · rw [hnet] at hprotocol
    have hbase : (protocolMessages pre ++ protocolMessages post).Perm
        (optionList wire1) := by
      have hp := hprotocol.trans List.perm_append_comm
      apply Perm.cancel_exposed
      simpa [protocolMessages, List.append_assoc] using hp
    simpa [reply, protocolMessages, optionList, List.append_assoc] using
      hbase.append_right [reply]
  · rw [hnet] at hcover
    simpa [reply, appTokens, appToken, List.append_assoc] using hcover

theorem Candidate.local_member {cfg : Storage.Config} {cand : Candidate}
    (h : cand.Valid cfg) :
    (cand.res, cand.after, cand.outs) ∈
      ((Experiment.dispatch cand.req cand.now).run
        { cfg.app with unreliable := true }
        { promises := cand.doc.toList.map (·.1) }).val := by
  rw [h.1]
  exact pick_mem _ _

theorem Candidate.promise_id {cfg : Storage.Config} {cand : Candidate}
    (h : cand.Valid cfg) : cand.promise.id = cand.req.key := by
  have hf := List.find?_some h.2.1
  exact beq_iff_eq.mp hf

theorem storeAt_of_lookup {store : Store} {key : Ident}
    {doc : Option (Promise × Version)} (h : storeLookup store key = doc) :
    storePromiseAt store key = doc.map (·.1) := by
  simp [storePromiseAt, h]

/-- A valid candidate computed from the store's current document is an
abstract handler step on the represented global state. -/
theorem candidate_transport {cfg : Storage.Config} {cand : Candidate}
    {store : Store} {global : Experiment.State}
    (hrep : StoreRep store global)
    (hdoc : storeLookup store cand.req.key = cand.doc)
    (hcand : cand.Valid cfg) :
    ∃ globalAfter,
      (cand.res, globalAfter, cand.outs) ∈
        ((Experiment.dispatch cand.req cand.now).run
          { cfg.app with unreliable := true } global).val ∧
      SameState
        (cand.after.withFrame (global.promises.filter (·.id != cand.req.key)))
        globalAfter := by
  have hglobalDoc : Experiment.promiseAt global cand.req.key =
      cand.doc.map (·.1) := by
    rw [← hrep cand.req.key]
    exact storeAt_of_lookup hdoc
  exact dispatch_transport cand.req cand.now
    { cfg.app with unreliable := true } global cand.after
    (cand.doc.map (·.1)) cand.res cand.outs hglobalDoc
    (by
      have hm := Candidate.local_member hcand
      cases h : cand.doc with
      | none =>
        simp only [h, Option.toList, List.map_nil, Option.map] at hm ⊢
        change (cand.res, cand.after, cand.outs) ∈
          (Experiment.dispatch cand.req cand.now
            { cfg.app with unreliable := true } {}).val at hm
        exact hm
      | some value =>
        simp only [h, Option.toList, List.map_cons, List.map_nil, Option.map] at hm ⊢
        change (cand.res, cand.after, cand.outs) ∈
          (Experiment.dispatch cand.req cand.now
            { cfg.app with unreliable := true } { promises := [value.1] }).val at hm
        exact hm)

/-- Committing the candidate document preserves the extensional store/state
representation established by `candidate_transport`. -/
theorem commit_rep {cfg : Storage.Config} {cand : Candidate}
    {store : Store} {global globalAfter : Experiment.State}
    (hcand : cand.Valid cfg)
    (hrep : StoreRep store global)
    (hstate : SameState
      (cand.after.withFrame (global.promises.filter (·.id != cand.req.key)))
      globalAfter) :
    StoreRep (storeCommit store cand.req.key cand.promise) globalAfter := by
  intro key
  rw [storePromiseAt_commit]
  by_cases hk : key = cand.req.key
  · subst key
    rw [if_pos rfl, ← hstate cand.req.key]
    have hp := Candidate.promise_id hcand
    simp [Experiment.promiseAt, State.withFrame, hcand.2.2, hp]
  · rw [if_neg hk, ← hstate key]
    have hp := Candidate.promise_id hcand
    have hpk : cand.promise.id ≠ key := by
      intro he
      exact hk (he.symm.trans hp)
    simp only [Experiment.promiseAt, State.withFrame, hcand.2.2,
      List.singleton_append, List.find?_cons]
    rw [show (cand.promise.id == key) = false from beq_eq_false_iff_ne.mpr hpk]
    rw [Experiment.find?_filter_other _ hk]
    exact hrep key

/-- A successful conditional commit is one hidden abstract server step. -/
theorem linearize_candidate {cfg : Storage.Config} {cand : Candidate}
    {store : Store} {a : Experiment.Conf promises}
    {pre post : List (Experiment.Proc × Experiment.Proc × Msg)}
    (hcand : cand.Valid cfg)
    (hrep : StoreRep store a.state)
    (hdoc : storeLookup store cand.req.key = cand.doc)
    (hnet : a.net =
      pre ++ (.client cand.client, .server, Msg.req cand.id cand.now cand.req) :: post) :
    ∃ globalAfter serviceOut next,
      serviceOut = cand.outs ++ [.send cand.client (Msg.res cand.id cand.res)] ∧
      Experiment.Legal promises { cfg.app with unreliable := true } a
        [((.server, a.now,
          .receive (.client cand.client) (Msg.req cand.id cand.now cand.req)),
          serviceOut, next)] ∧
      Experiment.observe
        [((.server, a.now,
          .receive (.client cand.client) (Msg.req cand.id cand.now cand.req)),
          serviceOut, next)] = [] ∧
      StoreRep (storeCommit store cand.req.key cand.promise) globalAfter ∧
      next =
        ⟨pre ++ post ++ Experiment.emits .server
          (.receive (.client cand.client)
            (Msg.req cand.id cand.now cand.req)) serviceOut,
          globalAfter, a.now⟩ := by
  obtain ⟨globalAfter, hout, hstate⟩ := candidate_transport hrep hdoc hcand
  let serviceOut := cand.outs ++ [.send cand.client (Msg.res cand.id cand.res)]
  let next : Experiment.Conf promises :=
    ⟨pre ++ post ++ Experiment.emits .server
      (.receive (.client cand.client) (Msg.req cand.id cand.now cand.req)) serviceOut,
      globalAfter, a.now⟩
  refine ⟨globalAfter, serviceOut, next, rfl, ?_, rfl,
    commit_rep hcand hrep hstate, rfl⟩
  dsimp [next]
  refine ⟨.receive (r := (globalAfter, serviceOut)) (Nat.le_refl _) hnet ?_, trivial⟩
  exact request_step_mem (dispatch_as_serve hout)

/-- A write that lands but reports failure is the abstract `lose` outcome:
state and notifications happen, while the client receives 503. -/
theorem linearize_candidate_lost {cfg : Storage.Config} {cand : Candidate}
    {store : Store} {a : Experiment.Conf promises}
    {pre post : List (Experiment.Proc × Experiment.Proc × Msg)}
    (hcand : cand.Valid cfg)
    (hrep : StoreRep store a.state)
    (hdoc : storeLookup store cand.req.key = cand.doc)
    (hnet : a.net =
      pre ++ (.client cand.client, .server, Msg.req cand.id cand.now cand.req) :: post) :
    ∃ globalAfter serviceOut next,
      serviceOut = cand.outs ++ [.send cand.client (Msg.res cand.id ⟨503, none⟩)] ∧
      Experiment.Legal promises { cfg.app with unreliable := true } a
        [((.server, a.now,
          .receive (.client cand.client) (Msg.req cand.id cand.now cand.req)),
          serviceOut, next)] ∧
      Experiment.observe
        [((.server, a.now,
          .receive (.client cand.client) (Msg.req cand.id cand.now cand.req)),
          serviceOut, next)] = [] ∧
      StoreRep (storeCommit store cand.req.key cand.promise) globalAfter ∧
      next =
        ⟨pre ++ post ++ Experiment.emits .server
          (.receive (.client cand.client)
            (Msg.req cand.id cand.now cand.req)) serviceOut,
          globalAfter, a.now⟩ := by
  obtain ⟨globalAfter, hout, hstate⟩ := candidate_transport hrep hdoc hcand
  let failed : Response := ⟨503, none⟩
  let serviceOut := cand.outs ++ [.send cand.client (Msg.res cand.id failed)]
  let next : Experiment.Conf promises :=
    ⟨pre ++ post ++ Experiment.emits .server
      (.receive (.client cand.client) (Msg.req cand.id cand.now cand.req)) serviceOut,
      globalAfter, a.now⟩
  refine ⟨globalAfter, serviceOut, next, rfl, ?_, rfl,
    commit_rep hcand hrep hstate, rfl⟩
  dsimp [next]
  refine ⟨.receive (r := (globalAfter, serviceOut)) (Nat.le_refl _) hnet ?_, trivial⟩
  exact request_step_mem (dispatch_as_lose hout)

theorem linearize_candidate_shed {cfg : Storage.Config} {cand : Candidate}
    {store : Store} {a : Experiment.Conf promises}
    {pre post : List (Experiment.Proc × Experiment.Proc × Msg)}
    (hrep : StoreRep store a.state)
    (hnet : a.net =
      pre ++ (.client cand.client, .server,
        Msg.req cand.id cand.now cand.req) :: post) :
    let serviceOut : List (Out Msg) :=
      [.send cand.client (Msg.res cand.id ⟨503, none⟩)]
    let next : Experiment.Conf promises :=
      ⟨pre ++ post ++ Experiment.emits .server
        (.receive (.client cand.client)
          (Msg.req cand.id cand.now cand.req)) serviceOut,
        a.state, a.now⟩
    Experiment.Legal promises { cfg.app with unreliable := true } a
      [((.server, a.now,
        .receive (.client cand.client)
          (Msg.req cand.id cand.now cand.req)), serviceOut, next)] ∧
    Experiment.observe
      [((.server, a.now,
        .receive (.client cand.client)
          (Msg.req cand.id cand.now cand.req)), serviceOut, next)] = [] ∧
    StoreRep store next.state := by
  dsimp
  refine ⟨⟨.receive (r := (a.state,
    [.send cand.client (Msg.res cand.id ⟨503, none⟩)]))
    (Nat.le_refl _) hnet ?_, trivial⟩, rfl, hrep⟩
  exact request_step_mem
    (request_shed_mem cfg.app a.state cand.req cand.now)

theorem normalRel_store_failed_node1 {cfg : Storage.Config}
    {net : List ConcreteMessage} {now t : Time}
    {candidate : Candidate} {op next : Nat} {mailbox : List (Addr × CMsg)}
    {node2 : Running Storage.Config Nat CMsg} {store : Store}
    {wire2 : Option ConcreteMessage} {tokens2 : List AbstractMessage}
    {a : Experiment.Conf promises}
    (hstoreAddr : cfg.store = "s3")
    (happ : AppOnly mailbox) (hnext : next = op + 1)
    (hnone : take? (answers op) mailbox = none)
    (hvalid : candidate.Valid cfg)
    (hsnapshot : Snapshot store candidate.req.key candidate.doc)
    (hn2 : NodeRep cfg store "n2" node2 wire2 tokens2)
    (hprotocol : (protocolMessages net).Perm
      ([((.proc "n1", .proc "s3",
        .put op candidate.req.key candidate.promise
          (candidate.doc.map (·.2))) : ConcreteMessage)] ++
        optionList wire2))
    (hcover : Covers
      (appTokens net ++
        (mailboxTokens mailbox ++ candidate.stageTokens .pending) ++
        tokens2) a.net)
    (hstore : StoreRep store a.state) (htime : a.now ≤ now)
    (hstepTime : now ≤ t) (pre post : List ConcreteMessage)
    (hnet : net = pre ++
      ((.proc "n1", .proc "s3",
        .put op candidate.req.key candidate.promise
          (candidate.doc.map (·.2))) : ConcreteMessage) :: post) :
    let reply : ConcreteMessage := (.proc "s3", .proc "n1", .failed op)
    ∃ a',
      Network.Matches { cfg.app with unreliable := true } clientView a
        (.proc "s3", t, .receive (.proc "n1")
          (CMsg.put op candidate.req.key candidate.promise
            (candidate.doc.map (·.2)))) a' ∧
      NormalRel cfg
        ⟨pre ++ post ++ [reply],
          [("n1", .node ⟨next, mailbox,
            writeK candidate.tries (candidate.call.retry candidate.tries)
              candidate op⟩),
           ("n2", .node node2), ("s3", .store store)], t⟩ a' := by
  dsimp
  rw [hnet] at hcover
  have hc : Covers
      ((appTokens pre ++ appTokens post ++ mailboxTokens mailbox) ++
        candidate.stageTokens .pending ++ tokens2) a.net := by
    simpa [appTokens, appToken, List.append_assoc] using hcover
  change Covers
      ((appTokens pre ++ appTokens post ++ mailboxTokens mailbox) ++
        [candidate.call.token] ++ tokens2) a.net at hc
  have hcCall : Covers
      ((appTokens pre ++ appTokens post ++ mailboxTokens mailbox) ++
        candidate.call.token :: tokens2) a.net := by
    simpa [List.append_assoc] using hc
  obtain ⟨apre, apost, hanet, hcRest⟩ := Covers.consume hcCall
  have hlin := linearize_candidate_shed
    (cfg := cfg) (cand := candidate) hstore hanet
  dsimp at hlin
  obtain ⟨hlegal, hobs, hstore'⟩ := hlin
  let response : AbstractMessage :=
    responseToken candidate.client candidate.id ⟨503, none⟩
  let a' : Experiment.Conf promises :=
    ⟨apre ++ apost ++ [response], a.state, a.now⟩
  have haeq : a' =
      ⟨apre ++ apost ++ Experiment.emits .server
        (.receive (.client candidate.client)
          (Msg.req candidate.id candidate.now candidate.req))
        [.send candidate.client
          (Msg.res candidate.id ⟨503, none⟩)], a.state, a.now⟩ := by
    simp [a', response, responseToken, Experiment.emits, sends]
  refine ⟨a', ?_, ?_⟩
  · refine ⟨[((.server, a.now,
      .receive (.client candidate.client)
        (Msg.req candidate.id candidate.now candidate.req)),
      [.send candidate.client (Msg.res candidate.id ⟨503, none⟩)], a')],
      ?_, hobs, rfl⟩
    simpa [haeq] using hlegal
  · let reply : ConcreteMessage := (.proc "s3", .proc "n1", .failed op)
    refine ⟨_, node2, store, some reply, wire2,
      mailboxTokens mailbox ++ candidate.stageTokens .shed, tokens2,
      rfl, ?_, hn2, ?_, ?_, ?_, Nat.le_trans htime hstepTime⟩
    · simpa [reply, hstoreAddr] using
        (NodeRep.writingShed
          (cfg := cfg) (store := store) (address := "n1")
          (candidate := candidate) happ hnext hnone hvalid hsnapshot)
    · rw [hnet] at hprotocol
      have hbase : (protocolMessages pre ++ protocolMessages post).Perm
          (optionList wire2) := by
        apply Perm.cancel_exposed
        simpa [protocolMessages, List.append_assoc] using hprotocol
      have hp := hbase.append_right [reply]
      have hswap :
          (optionList wire2 ++ [reply]).Perm
            ([reply] ++ optionList wire2) := List.perm_append_comm
      simpa [reply, protocolMessages, optionList, List.append_assoc] using
        hp.trans hswap
    · have hcAdded := Covers.insert_both
        (left := appTokens pre ++ appTokens post ++ mailboxTokens mailbox)
        (right := tokens2) (added := [response]) hcRest
      simpa [a', response, responseToken, Candidate.stageTokens,
        appTokens, appToken, List.append_assoc] using hcAdded
    · simpa [a', haeq] using hstore'


theorem normalRel_store_failed_node2 {cfg : Storage.Config}
    {net : List ConcreteMessage} {now t : Time}
    {candidate : Candidate} {op next : Nat} {mailbox : List (Addr × CMsg)}
    {node1 : Running Storage.Config Nat CMsg} {store : Store}
    {wire1 : Option ConcreteMessage} {tokens1 : List AbstractMessage}
    {a : Experiment.Conf promises}
    (hstoreAddr : cfg.store = "s3")
    (happ : AppOnly mailbox) (hnext : next = op + 1)
    (hnone : take? (answers op) mailbox = none)
    (hvalid : candidate.Valid cfg)
    (hsnapshot : Snapshot store candidate.req.key candidate.doc)
    (hn1 : NodeRep cfg store "n1" node1 wire1 tokens1)
    (hprotocol : (protocolMessages net).Perm
      (optionList wire1 ++ [((.proc "n2", .proc "s3",
        .put op candidate.req.key candidate.promise
          (candidate.doc.map (·.2))) : ConcreteMessage)]))
    (hcover : Covers
      (appTokens net ++ tokens1 ++
        (mailboxTokens mailbox ++ candidate.stageTokens .pending)) a.net)
    (hstore : StoreRep store a.state) (htime : a.now ≤ now)
    (hstepTime : now ≤ t) (pre post : List ConcreteMessage)
    (hnet : net = pre ++
      ((.proc "n2", .proc "s3",
        .put op candidate.req.key candidate.promise
          (candidate.doc.map (·.2))) : ConcreteMessage) :: post) :
    let reply : ConcreteMessage := (.proc "s3", .proc "n2", .failed op)
    ∃ a',
      Network.Matches { cfg.app with unreliable := true } clientView a
        (.proc "s3", t, .receive (.proc "n2")
          (CMsg.put op candidate.req.key candidate.promise
            (candidate.doc.map (·.2)))) a' ∧
      NormalRel cfg
        ⟨pre ++ post ++ [reply],
          [("n1", .node node1),
           ("n2", .node ⟨next, mailbox,
            writeK candidate.tries (candidate.call.retry candidate.tries)
              candidate op⟩), ("s3", .store store)], t⟩ a' := by
  dsimp
  rw [hnet] at hcover
  have hc : Covers
      ((appTokens pre ++ appTokens post ++ tokens1 ++ mailboxTokens mailbox) ++
        candidate.stageTokens .pending) a.net := by
    simpa [appTokens, appToken, List.append_assoc] using hcover
  change Covers
      ((appTokens pre ++ appTokens post ++ tokens1 ++ mailboxTokens mailbox) ++
        [candidate.call.token]) a.net at hc
  have hcCall : Covers
      ((appTokens pre ++ appTokens post ++ tokens1 ++ mailboxTokens mailbox) ++
        candidate.call.token :: []) a.net := by
    simpa [List.append_assoc] using hc
  obtain ⟨apre, apost, hanet, hcRest⟩ := Covers.consume hcCall
  have hlin := linearize_candidate_shed
    (cfg := cfg) (cand := candidate) hstore hanet
  dsimp at hlin
  obtain ⟨hlegal, hobs, hstore'⟩ := hlin
  let response : AbstractMessage :=
    responseToken candidate.client candidate.id ⟨503, none⟩
  let a' : Experiment.Conf promises :=
    ⟨apre ++ apost ++ [response], a.state, a.now⟩
  have haeq : a' =
      ⟨apre ++ apost ++ Experiment.emits .server
        (.receive (.client candidate.client)
          (Msg.req candidate.id candidate.now candidate.req))
        [.send candidate.client
          (Msg.res candidate.id ⟨503, none⟩)], a.state, a.now⟩ := by
    simp [a', response, responseToken, Experiment.emits, sends]
  refine ⟨a', ?_, ?_⟩
  · refine ⟨[((.server, a.now,
      .receive (.client candidate.client)
        (Msg.req candidate.id candidate.now candidate.req)),
      [.send candidate.client (Msg.res candidate.id ⟨503, none⟩)], a')],
      ?_, hobs, rfl⟩
    simpa [haeq] using hlegal
  · let reply : ConcreteMessage := (.proc "s3", .proc "n2", .failed op)
    refine ⟨node1, _, store, wire1, some reply,
      tokens1, mailboxTokens mailbox ++ candidate.stageTokens .shed,
      rfl, hn1, ?_, ?_, ?_, ?_, Nat.le_trans htime hstepTime⟩
    · simpa [reply, hstoreAddr] using
        (NodeRep.writingShed
          (cfg := cfg) (store := store) (address := "n2")
          (candidate := candidate) happ hnext hnone hvalid hsnapshot)
    · rw [hnet] at hprotocol
      have hbase : (protocolMessages pre ++ protocolMessages post).Perm
          (optionList wire1) := by
        have hp := hprotocol.trans List.perm_append_comm
        apply Perm.cancel_exposed
        simpa [protocolMessages, List.append_assoc] using hp
      simpa [reply, protocolMessages, optionList, List.append_assoc] using
        hbase.append_right [reply]
    · have hcAdded := Covers.insert_both
        (left := appTokens pre ++ appTokens post ++ tokens1 ++
          mailboxTokens mailbox)
        (right := []) (added := [response]) hcRest
      simpa [a', response, responseToken, Candidate.stageTokens,
        appTokens, appToken, List.append_assoc] using hcAdded
    · simpa [a', haeq] using hstore'

theorem normalRel_store_written_node1 {cfg : Storage.Config}
    {net : List ConcreteMessage} {now t : Time}
    {candidate : Candidate} {op next : Nat} {mailbox : List (Addr × CMsg)}
    {node2 : Running Storage.Config Nat CMsg} {store : Store}
    {wire2 : Option ConcreteMessage} {tokens2 : List AbstractMessage}
    {a : Experiment.Conf promises}
    (hstoreAddr : cfg.store = "s3")
    (happ : AppOnly mailbox) (hnext : next = op + 1)
    (hnone : take? (answers op) mailbox = none)
    (hvalid : candidate.Valid cfg)
    (hsnapshot : Snapshot store candidate.req.key candidate.doc)
    (hmatch : candidate.doc.map (·.2) =
      (storeLookup store candidate.req.key).map (·.2))
    (hn2 : NodeRep cfg store "n2" node2 wire2 tokens2)
    (hprotocol : (protocolMessages net).Perm
      ([((.proc "n1", .proc "s3",
        .put op candidate.req.key candidate.promise
          (candidate.doc.map (·.2))) : ConcreteMessage)] ++ optionList wire2))
    (hcover : Covers
      (appTokens net ++
        (mailboxTokens mailbox ++ candidate.stageTokens .pending) ++
        tokens2) a.net)
    (hstore : StoreRep store a.state) (htime : a.now ≤ now)
    (hstepTime : now ≤ t) (pre post : List ConcreteMessage)
    (hnet : net = pre ++
      ((.proc "n1", .proc "s3",
        .put op candidate.req.key candidate.promise
          (candidate.doc.map (·.2))) : ConcreteMessage) :: post) :
    let committed := storeCommit store candidate.req.key candidate.promise
    let reply : ConcreteMessage := (.proc "s3", .proc "n1", .written op)
    ∃ a',
      Network.Matches { cfg.app with unreliable := true } clientView a
        (.proc "s3", t, .receive (.proc "n1")
          (CMsg.put op candidate.req.key candidate.promise
            (candidate.doc.map (·.2)))) a' ∧
      NormalRel cfg
        ⟨pre ++ post ++ [reply],
          [("n1", .node ⟨next, mailbox,
            writeK candidate.tries (candidate.call.retry candidate.tries)
              candidate op⟩),
           ("n2", .node node2), ("s3", .store committed)], t⟩ a' := by
  dsimp
  rw [hnet] at hcover
  have hc : Covers
      ((appTokens pre ++ appTokens post ++ mailboxTokens mailbox) ++
        [candidate.call.token] ++ tokens2) a.net := by
    simpa [appTokens, appToken, Candidate.stageTokens,
      List.append_assoc] using hcover
  have hcCall : Covers
      ((appTokens pre ++ appTokens post ++ mailboxTokens mailbox) ++
        candidate.call.token :: tokens2) a.net := by
    simpa [List.append_assoc] using hc
  obtain ⟨apre, apost, hanet, hcRest⟩ := Covers.consume hcCall
  have hdoc := Snapshot.eq_of_versions hsnapshot hmatch
  obtain ⟨globalAfter, serviceOut, abstractNext, hservice,
    hlegal, hobs, hstore', haeq⟩ :=
    linearize_candidate hvalid hstore hdoc hanet
  subst serviceOut
  subst abstractNext
  let emitted := candidate.stageTokens .served
  have hemitted :
      Experiment.emits .server
        (.receive (.client candidate.client)
          (Msg.req candidate.id candidate.now candidate.req))
        (candidate.outs ++ [.send candidate.client
          (Msg.res candidate.id candidate.res)]) = emitted := by
    simp [emitted, Candidate.stageTokens, emits_outputs_response]
  let a' : Experiment.Conf promises :=
    ⟨apre ++ apost ++ emitted, globalAfter, a.now⟩
  refine ⟨a', ?_, ?_⟩
  · refine ⟨[((.server, a.now,
      .receive (.client candidate.client)
        (Msg.req candidate.id candidate.now candidate.req)),
      candidate.outs ++ [.send candidate.client
        (Msg.res candidate.id candidate.res)], a')], ?_, hobs, rfl⟩
    simpa [a', hemitted] using hlegal
  · let reply : ConcreteMessage := (.proc "s3", .proc "n1", .written op)
    refine ⟨_, node2, storeCommit store candidate.req.key candidate.promise,
      some reply, wire2,
      mailboxTokens mailbox ++ candidate.stageTokens .served, tokens2,
      rfl, ?_, hn2.commit, ?_, ?_, hstore', Nat.le_trans htime hstepTime⟩
    · simpa [reply, hstoreAddr] using
        (NodeRep.writingServed
          (cfg := cfg) (store := storeCommit store candidate.req.key candidate.promise)
          (address := "n1") (candidate := candidate)
          happ hnext hnone hvalid)
    · rw [hnet] at hprotocol
      have hbase : (protocolMessages pre ++ protocolMessages post).Perm
          (optionList wire2) := by
        apply Perm.cancel_exposed
        simpa [protocolMessages, List.append_assoc] using hprotocol
      have hp := hbase.append_right [reply]
      have hswap : (optionList wire2 ++ [reply]).Perm
          ([reply] ++ optionList wire2) := List.perm_append_comm
      simpa [reply, protocolMessages, optionList, List.append_assoc] using
        hp.trans hswap
    · have hcAdded := Covers.insert_both
        (left := appTokens pre ++ appTokens post ++ mailboxTokens mailbox)
        (right := tokens2) (added := emitted) hcRest
      simpa [a', emitted, appTokens, appToken, List.append_assoc] using hcAdded



theorem normalRel_store_written_node2 {cfg : Storage.Config}
    {net : List ConcreteMessage} {now t : Time}
    {candidate : Candidate} {op next : Nat} {mailbox : List (Addr × CMsg)}
    {node1 : Running Storage.Config Nat CMsg} {store : Store}
    {wire1 : Option ConcreteMessage} {tokens1 : List AbstractMessage}
    {a : Experiment.Conf promises}
    (hstoreAddr : cfg.store = "s3")
    (happ : AppOnly mailbox) (hnext : next = op + 1)
    (hnone : take? (answers op) mailbox = none)
    (hvalid : candidate.Valid cfg)
    (hsnapshot : Snapshot store candidate.req.key candidate.doc)
    (hmatch : candidate.doc.map (·.2) =
      (storeLookup store candidate.req.key).map (·.2))
    (hn1 : NodeRep cfg store "n1" node1 wire1 tokens1)
    (hprotocol : (protocolMessages net).Perm
      (optionList wire1 ++ [((.proc "n2", .proc "s3",
        .put op candidate.req.key candidate.promise
          (candidate.doc.map (·.2))) : ConcreteMessage)]))
    (hcover : Covers
      (appTokens net ++ tokens1 ++
        (mailboxTokens mailbox ++ candidate.stageTokens .pending)) a.net)
    (hstore : StoreRep store a.state) (htime : a.now ≤ now)
    (hstepTime : now ≤ t) (pre post : List ConcreteMessage)
    (hnet : net = pre ++
      ((.proc "n2", .proc "s3",
        .put op candidate.req.key candidate.promise
          (candidate.doc.map (·.2))) : ConcreteMessage) :: post) :
    let committed := storeCommit store candidate.req.key candidate.promise
    let reply : ConcreteMessage := (.proc "s3", .proc "n2", .written op)
    ∃ a',
      Network.Matches { cfg.app with unreliable := true } clientView a
        (.proc "s3", t, .receive (.proc "n2")
          (CMsg.put op candidate.req.key candidate.promise
            (candidate.doc.map (·.2)))) a' ∧
      NormalRel cfg
        ⟨pre ++ post ++ [reply],
          [("n1", .node node1),
           ("n2", .node ⟨next, mailbox,
            writeK candidate.tries (candidate.call.retry candidate.tries)
              candidate op⟩), ("s3", .store committed)], t⟩ a' := by
  dsimp
  rw [hnet] at hcover
  have hc : Covers
      ((appTokens pre ++ appTokens post ++ tokens1 ++ mailboxTokens mailbox) ++
        [candidate.call.token]) a.net := by
    simpa [appTokens, appToken, Candidate.stageTokens,
      List.append_assoc] using hcover
  have hcCall : Covers
      ((appTokens pre ++ appTokens post ++ tokens1 ++ mailboxTokens mailbox) ++
        candidate.call.token :: []) a.net := by
    simpa [List.append_assoc] using hc
  obtain ⟨apre, apost, hanet, hcRest⟩ := Covers.consume hcCall
  have hdoc := Snapshot.eq_of_versions hsnapshot hmatch
  obtain ⟨globalAfter, serviceOut, abstractNext, hservice,
    hlegal, hobs, hstore', haeq⟩ :=
    linearize_candidate hvalid hstore hdoc hanet
  subst serviceOut
  subst abstractNext
  let emitted := candidate.stageTokens .served
  have hemitted :
      Experiment.emits .server
        (.receive (.client candidate.client)
          (Msg.req candidate.id candidate.now candidate.req))
        (candidate.outs ++ [.send candidate.client
          (Msg.res candidate.id candidate.res)]) = emitted := by
    simp [emitted, Candidate.stageTokens, emits_outputs_response]
  let a' : Experiment.Conf promises :=
    ⟨apre ++ apost ++ emitted, globalAfter, a.now⟩
  refine ⟨a', ?_, ?_⟩
  · refine ⟨[((.server, a.now,
      .receive (.client candidate.client)
        (Msg.req candidate.id candidate.now candidate.req)),
      candidate.outs ++ [.send candidate.client
        (Msg.res candidate.id candidate.res)], a')], ?_, hobs, rfl⟩
    simpa [a', hemitted] using hlegal
  · let reply : ConcreteMessage := (.proc "s3", .proc "n2", .written op)
    refine ⟨node1, _, storeCommit store candidate.req.key candidate.promise,
      wire1, some reply,
      tokens1, mailboxTokens mailbox ++ candidate.stageTokens .served,
      rfl, hn1.commit, ?_, ?_, ?_, hstore', Nat.le_trans htime hstepTime⟩
    · simpa [reply, hstoreAddr] using
        (NodeRep.writingServed
          (cfg := cfg) (store := storeCommit store candidate.req.key candidate.promise)
          (address := "n2") (candidate := candidate)
          happ hnext hnone hvalid)
    · rw [hnet] at hprotocol
      have hbase : (protocolMessages pre ++ protocolMessages post).Perm
          (optionList wire1) := by
        have hp := hprotocol.trans List.perm_append_comm
        apply Perm.cancel_exposed
        simpa [protocolMessages, List.append_assoc] using hp
      simpa [reply, protocolMessages, optionList, List.append_assoc] using
        hbase.append_right [reply]
    · have hcAdded := Covers.insert_both
        (left := appTokens pre ++ appTokens post ++ tokens1 ++ mailboxTokens mailbox)
        (right := []) (added := emitted) hcRest
      simpa [a', emitted, appTokens, appToken, List.append_assoc] using hcAdded


theorem normalRel_store_landedFailed_node1 {cfg : Storage.Config}
    {net : List ConcreteMessage} {now t : Time}
    {candidate : Candidate} {op next : Nat} {mailbox : List (Addr × CMsg)}
    {node2 : Running Storage.Config Nat CMsg} {store : Store}
    {wire2 : Option ConcreteMessage} {tokens2 : List AbstractMessage}
    {a : Experiment.Conf promises}
    (hstoreAddr : cfg.store = "s3")
    (happ : AppOnly mailbox) (hnext : next = op + 1)
    (hnone : take? (answers op) mailbox = none)
    (hvalid : candidate.Valid cfg)
    (hsnapshot : Snapshot store candidate.req.key candidate.doc)
    (hmatch : candidate.doc.map (·.2) =
      (storeLookup store candidate.req.key).map (·.2))
    (hn2 : NodeRep cfg store "n2" node2 wire2 tokens2)
    (hprotocol : (protocolMessages net).Perm
      ([((.proc "n1", .proc "s3",
        .put op candidate.req.key candidate.promise
          (candidate.doc.map (·.2))) : ConcreteMessage)] ++ optionList wire2))
    (hcover : Covers
      (appTokens net ++
        (mailboxTokens mailbox ++ candidate.stageTokens .pending) ++
        tokens2) a.net)
    (hstore : StoreRep store a.state) (htime : a.now ≤ now)
    (hstepTime : now ≤ t) (pre post : List ConcreteMessage)
    (hnet : net = pre ++
      ((.proc "n1", .proc "s3",
        .put op candidate.req.key candidate.promise
          (candidate.doc.map (·.2))) : ConcreteMessage) :: post) :
    let committed := storeCommit store candidate.req.key candidate.promise
    let reply : ConcreteMessage := (.proc "s3", .proc "n1", .failed op)
    ∃ a',
      Network.Matches { cfg.app with unreliable := true } clientView a
        (.proc "s3", t, .receive (.proc "n1")
          (CMsg.put op candidate.req.key candidate.promise
            (candidate.doc.map (·.2)))) a' ∧
      NormalRel cfg
        ⟨pre ++ post ++ [reply],
          [("n1", .node ⟨next, mailbox,
            writeK candidate.tries (candidate.call.retry candidate.tries)
              candidate op⟩),
           ("n2", .node node2), ("s3", .store committed)], t⟩ a' := by
  dsimp
  rw [hnet] at hcover
  have hc : Covers
      ((appTokens pre ++ appTokens post ++ mailboxTokens mailbox) ++
        [candidate.call.token] ++ tokens2) a.net := by
    simpa [appTokens, appToken, Candidate.stageTokens,
      List.append_assoc] using hcover
  have hcCall : Covers
      ((appTokens pre ++ appTokens post ++ mailboxTokens mailbox) ++
        candidate.call.token :: tokens2) a.net := by
    simpa [List.append_assoc] using hc
  obtain ⟨apre, apost, hanet, hcRest⟩ := Covers.consume hcCall
  have hdoc := Snapshot.eq_of_versions hsnapshot hmatch
  obtain ⟨globalAfter, serviceOut, abstractNext, hservice,
    hlegal, hobs, hstore', haeq⟩ :=
    linearize_candidate_lost hvalid hstore hdoc hanet
  subst serviceOut
  subst abstractNext
  let emitted := candidate.stageTokens .lost
  have hemitted :
      Experiment.emits .server
        (.receive (.client candidate.client)
          (Msg.req candidate.id candidate.now candidate.req))
        (candidate.outs ++ [.send candidate.client
          (Msg.res candidate.id ⟨503, none⟩)]) = emitted := by
    simp [emitted, Candidate.stageTokens, emits_outputs_response]
  let a' : Experiment.Conf promises :=
    ⟨apre ++ apost ++ emitted, globalAfter, a.now⟩
  refine ⟨a', ?_, ?_⟩
  · refine ⟨[((.server, a.now,
      .receive (.client candidate.client)
        (Msg.req candidate.id candidate.now candidate.req)),
      candidate.outs ++ [.send candidate.client
        (Msg.res candidate.id ⟨503, none⟩)], a')], ?_, hobs, rfl⟩
    simpa [a', hemitted] using hlegal
  · let reply : ConcreteMessage := (.proc "s3", .proc "n1", .failed op)
    refine ⟨_, node2, storeCommit store candidate.req.key candidate.promise,
      some reply, wire2,
      mailboxTokens mailbox ++ candidate.stageTokens .lost, tokens2,
      rfl, ?_, hn2.commit, ?_, ?_, hstore', Nat.le_trans htime hstepTime⟩
    · simpa [reply, hstoreAddr] using
        (NodeRep.writingLost
          (cfg := cfg) (store := storeCommit store candidate.req.key candidate.promise)
          (address := "n1") (candidate := candidate)
          happ hnext hnone hvalid)
    · rw [hnet] at hprotocol
      have hbase : (protocolMessages pre ++ protocolMessages post).Perm
          (optionList wire2) := by
        apply Perm.cancel_exposed
        simpa [protocolMessages, List.append_assoc] using hprotocol
      have hp := hbase.append_right [reply]
      have hswap : (optionList wire2 ++ [reply]).Perm
          ([reply] ++ optionList wire2) := List.perm_append_comm
      simpa [reply, protocolMessages, optionList, List.append_assoc] using
        hp.trans hswap
    · have hcAdded := Covers.insert_both
        (left := appTokens pre ++ appTokens post ++ mailboxTokens mailbox)
        (right := tokens2) (added := emitted) hcRest
      simpa [a', emitted, appTokens, appToken, List.append_assoc] using hcAdded


theorem normalRel_store_landedFailed_node2 {cfg : Storage.Config}
    {net : List ConcreteMessage} {now t : Time}
    {candidate : Candidate} {op next : Nat} {mailbox : List (Addr × CMsg)}
    {node1 : Running Storage.Config Nat CMsg} {store : Store}
    {wire1 : Option ConcreteMessage} {tokens1 : List AbstractMessage}
    {a : Experiment.Conf promises}
    (hstoreAddr : cfg.store = "s3")
    (happ : AppOnly mailbox) (hnext : next = op + 1)
    (hnone : take? (answers op) mailbox = none)
    (hvalid : candidate.Valid cfg)
    (hsnapshot : Snapshot store candidate.req.key candidate.doc)
    (hmatch : candidate.doc.map (·.2) =
      (storeLookup store candidate.req.key).map (·.2))
    (hn1 : NodeRep cfg store "n1" node1 wire1 tokens1)
    (hprotocol : (protocolMessages net).Perm
      (optionList wire1 ++ [((.proc "n2", .proc "s3",
        .put op candidate.req.key candidate.promise
          (candidate.doc.map (·.2))) : ConcreteMessage)]))
    (hcover : Covers
      (appTokens net ++ tokens1 ++
        (mailboxTokens mailbox ++ candidate.stageTokens .pending)) a.net)
    (hstore : StoreRep store a.state) (htime : a.now ≤ now)
    (hstepTime : now ≤ t) (pre post : List ConcreteMessage)
    (hnet : net = pre ++
      ((.proc "n2", .proc "s3",
        .put op candidate.req.key candidate.promise
          (candidate.doc.map (·.2))) : ConcreteMessage) :: post) :
    let committed := storeCommit store candidate.req.key candidate.promise
    let reply : ConcreteMessage := (.proc "s3", .proc "n2", .failed op)
    ∃ a',
      Network.Matches { cfg.app with unreliable := true } clientView a
        (.proc "s3", t, .receive (.proc "n2")
          (CMsg.put op candidate.req.key candidate.promise
            (candidate.doc.map (·.2)))) a' ∧
      NormalRel cfg
        ⟨pre ++ post ++ [reply],
          [("n1", .node node1),
           ("n2", .node ⟨next, mailbox,
            writeK candidate.tries (candidate.call.retry candidate.tries)
              candidate op⟩), ("s3", .store committed)], t⟩ a' := by
  dsimp
  rw [hnet] at hcover
  have hc : Covers
      ((appTokens pre ++ appTokens post ++ tokens1 ++ mailboxTokens mailbox) ++
        [candidate.call.token]) a.net := by
    simpa [appTokens, appToken, Candidate.stageTokens,
      List.append_assoc] using hcover
  have hcCall : Covers
      ((appTokens pre ++ appTokens post ++ tokens1 ++ mailboxTokens mailbox) ++
        candidate.call.token :: []) a.net := by
    simpa [List.append_assoc] using hc
  obtain ⟨apre, apost, hanet, hcRest⟩ := Covers.consume hcCall
  have hdoc := Snapshot.eq_of_versions hsnapshot hmatch
  obtain ⟨globalAfter, serviceOut, abstractNext, hservice,
    hlegal, hobs, hstore', haeq⟩ :=
    linearize_candidate_lost hvalid hstore hdoc hanet
  subst serviceOut
  subst abstractNext
  let emitted := candidate.stageTokens .lost
  have hemitted :
      Experiment.emits .server
        (.receive (.client candidate.client)
          (Msg.req candidate.id candidate.now candidate.req))
        (candidate.outs ++ [.send candidate.client
          (Msg.res candidate.id ⟨503, none⟩)]) = emitted := by
    simp [emitted, Candidate.stageTokens, emits_outputs_response]
  let a' : Experiment.Conf promises :=
    ⟨apre ++ apost ++ emitted, globalAfter, a.now⟩
  refine ⟨a', ?_, ?_⟩
  · refine ⟨[((.server, a.now,
      .receive (.client candidate.client)
        (Msg.req candidate.id candidate.now candidate.req)),
      candidate.outs ++ [.send candidate.client
        (Msg.res candidate.id ⟨503, none⟩)], a')], ?_, hobs, rfl⟩
    simpa [a', hemitted] using hlegal
  · let reply : ConcreteMessage := (.proc "s3", .proc "n2", .failed op)
    refine ⟨node1, _, storeCommit store candidate.req.key candidate.promise,
      wire1, some reply,
      tokens1, mailboxTokens mailbox ++ candidate.stageTokens .lost,
      rfl, hn1.commit, ?_, ?_, ?_, hstore', Nat.le_trans htime hstepTime⟩
    · simpa [reply, hstoreAddr] using
        (NodeRep.writingLost
          (cfg := cfg) (store := storeCommit store candidate.req.key candidate.promise)
          (address := "n2") (candidate := candidate)
          happ hnext hnone hvalid)
    · rw [hnet] at hprotocol
      have hbase : (protocolMessages pre ++ protocolMessages post).Perm
          (optionList wire1) := by
        have hp := hprotocol.trans List.perm_append_comm
        apply Perm.cancel_exposed
        simpa [protocolMessages, List.append_assoc] using hp
      simpa [reply, protocolMessages, optionList, List.append_assoc] using
        hbase.append_right [reply]
    · have hcAdded := Covers.insert_both
        (left := appTokens pre ++ appTokens post ++ tokens1 ++ mailboxTokens mailbox)
        (right := []) (added := emitted) hcRest
      simpa [a', emitted, appTokens, appToken, List.append_assoc] using hcAdded

set_option maxHeartbeats 1000000 in
/-- A handler outcome that leaves its loaded document unchanged linearizes
at the store read. The concrete store and abstract state remain related. -/
theorem linearize_unchanged {cfg : Storage.Config} {store : Store}
    {a : Experiment.Conf promises} {client : Addr} {id : CallId}
    {req : Request} {now : Time} {doc : Option (Promise × Version)}
    {res : Response} {after : Experiment.State} {outs : List (Out Msg)}
    {pre post : List (Experiment.Proc × Experiment.Proc × Msg)}
    (hrep : StoreRep store a.state)
    (hdoc : storeLookup store req.key = doc)
    (hout : (res, after, outs) ∈
      ((Experiment.request req now).run { cfg.app with unreliable := true }
        { promises := doc.toList.map (·.1) }).val)
    (hunchanged : after = { promises := doc.toList.map (·.1) })
    (hnet : a.net = pre ++ (.client client, .server, Msg.req id now req) :: post) :
    ∃ globalAfter serviceOut next,
      serviceOut = outs ++ [.send client (Msg.res id res)] ∧
      Experiment.Legal promises { cfg.app with unreliable := true } a
        [((.server, a.now, .receive (.client client) (Msg.req id now req)),
          serviceOut, next)] ∧
      Experiment.observe
        [((.server, a.now, .receive (.client client) (Msg.req id now req)),
          serviceOut, next)] = [] ∧
      StoreRep store globalAfter ∧
      next =
        ⟨pre ++ post ++ Experiment.emits .server
          (.receive (.client client) (Msg.req id now req)) serviceOut,
          globalAfter, a.now⟩ := by
  have hglobalDoc : Experiment.promiseAt a.state req.key = doc.map (·.1) := by
    rw [← hrep req.key]
    exact storeAt_of_lookup hdoc
  have hlocal : (res, after, outs) ∈
      ((Experiment.request req now).run { cfg.app with unreliable := true }
        { promises := (doc.map (·.1)).toList }).val := by
    cases hd : doc with
    | none =>
      simp only [hd, Option.toList, List.map_nil, Option.map] at hout ⊢
      change (res, after, outs) ∈
        (Experiment.request req now { cfg.app with unreliable := true } {}).val at hout
      exact hout
    | some value =>
      simp only [hd, Option.toList, List.map_cons, List.map_nil, Option.map] at hout ⊢
      change (res, after, outs) ∈
        (Experiment.request req now { cfg.app with unreliable := true }
          { promises := [value.1] }).val at hout
      exact hout
  have hlocal' : (res, after, outs) ∈
      (Experiment.request req now { cfg.app with unreliable := true }
        { promises := (doc.map (fun x : Promise × Version => x.1)).toList }).val := by
    change (res, after, outs) ∈
      ((Experiment.request req now).run { cfg.app with unreliable := true }
        { promises := (doc.map (fun x : Promise × Version => x.1)).toList }).val
    exact hlocal
  obtain ⟨globalAfter, hglobal, hstate⟩ :=
    request_transport req now { cfg.app with unreliable := true } a.state after
      (doc.map (fun x : Promise × Version => x.1)) res outs hglobalDoc hlocal'
  have hframe := footprint_frame_same a.state req.key (doc.map (·.1)) hglobalDoc
  have hsame : SameState a.state globalAfter := by
    apply hframe.symm.trans
    rw [hunchanged] at hstate
    cases hd : doc with
    | none => simpa [hd] using hstate
    | some value => simpa [hd] using hstate
  have hrep' : StoreRep store globalAfter :=
    fun key => (hrep key).trans (hsame key)
  let serviceOut := outs ++ [.send client (Msg.res id res)]
  let next : Experiment.Conf promises :=
    ⟨pre ++ post ++ Experiment.emits .server
      (.receive (.client client) (Msg.req id now req)) serviceOut,
      globalAfter, a.now⟩
  refine ⟨globalAfter, serviceOut, next, rfl, ?_, rfl, hrep', rfl⟩
  dsimp [next]
  refine ⟨.receive (r := (globalAfter, serviceOut)) (Nat.le_refl _) hnet ?_, trivial⟩
  exact request_step_mem hglobal

theorem normalRel_node2_conflict_exhausted {cfg : Storage.Config}
    {net : List ConcreteMessage} {now t : Time}
    {candidate : Candidate} {op next : Nat}
    {mailbox : List (Addr × CMsg)}
    {node1 : Running Storage.Config Nat CMsg} {store : Store}
    {wire1 : Option ConcreteMessage} {tokens1 : List AbstractMessage}
    {a : Experiment.Conf promises}
    (hstoreAddr : cfg.store = "s3")
    (hn1 : NodeRep cfg store "n1" node1 wire1 tokens1)
    (happ : AppOnly mailbox) (hnext : next = op + 1)
    (hnone : take? (answers op) mailbox = none)
    (htries : candidate.tries = 0)
    (hprotocol : (protocolMessages net).Perm
      (optionList wire1 ++
        [((.proc "s3", .proc "n2", .conflict op) : ConcreteMessage)]))
    (hcover : Covers
      (appTokens net ++ tokens1 ++
        (mailboxTokens mailbox ++ candidate.stageTokens .pending)) a.net)
    (hstore : StoreRep store a.state) (htime : a.now ≤ now)
    (hstepTime : now ≤ t) (source : Network.Who)
    (pre post : List ConcreteMessage)
    (hnet : net = pre ++
      ((.proc "s3", .proc "n2", .conflict op) : ConcreteMessage) :: post) :
    ∃ a' running rest wire tokens,
      let states : List (Addr × Local) :=
        [("n1", .node node1), ("n2", .node running), ("s3", .store store)]
      let emitted : List (Out CMsg) :=
        .send candidate.client (.app (.res candidate.id ⟨503, none⟩)) :: rest
      Network.Matches { cfg.app with unreliable := true } clientView a
        (.proc "n2", t, .receive source (CMsg.conflict op)) a' ∧
      (toStep node 64 source.addr (.conflict op) t cfg
        (⟨next, mailbox,
          writeK candidate.tries (candidate.call.retry candidate.tries)
            candidate op⟩ : Running Storage.Config Nat CMsg)).val =
          [((), running, emitted)] ∧
      RestartRep cfg store "n2" running rest wire tokens ∧
      NormalRel cfg
        ⟨pre ++ post ++ routedOuts states "n2" emitted, states, t⟩ a' := by
  rw [hnet] at hcover
  have hc : Covers
      ((appTokens pre ++ appTokens post ++ tokens1 ++ mailboxTokens mailbox) ++
        [candidate.call.token]) a.net := by
    simpa [appTokens, appToken, Candidate.stageTokens,
      List.append_assoc] using hcover
  have hcCall : Covers
      ((appTokens pre ++ appTokens post ++ tokens1 ++ mailboxTokens mailbox) ++
        candidate.call.token :: []) a.net := by
    simpa [List.append_assoc] using hc
  obtain ⟨apre, apost, hanet, hcRest⟩ := Covers.consume hcCall
  have hlin := linearize_candidate_shed
    (cfg := cfg) (cand := candidate) hstore hanet
  dsimp at hlin
  obtain ⟨hlegal, hobs, hstore'⟩ := hlin
  let response : AbstractMessage :=
    responseToken candidate.client candidate.id ⟨503, none⟩
  let a' : Experiment.Conf promises :=
    ⟨apre ++ apost ++ [response], a.state, a.now⟩
  have haeq : a' =
      ⟨apre ++ apost ++ Experiment.emits .server
        (.receive (.client candidate.client)
          (Msg.req candidate.id candidate.now candidate.req))
        [.send candidate.client (Msg.res candidate.id ⟨503, none⟩)],
        a.state, a.now⟩ := by
    simp [a', response, responseToken, Experiment.emits, sends]
  obtain ⟨running, rest, wire, tokens, hrun, hrestart, htokens⟩ :=
    writing_conflict_exhausted_restart
      (cfg := cfg) (store := store) (address := "n2")
      happ hnone htries source.addr t
  let states : List (Addr × Local) :=
    [("n1", .node node1), ("n2", .node running), ("s3", .store store)]
  let emitted : List (Out CMsg) :=
    .send candidate.client (.app (.res candidate.id ⟨503, none⟩)) :: rest
  have hrouteStore :
      (⟨[], states, 0⟩ : Network.Conf system).route cfg.store =
        .proc cfg.store := by
    simp [states, hstoreAddr, Network.Conf.route, Network.Conf.isProc]
  obtain ⟨hrouteProtocol, hrouteApp⟩ :=
    hrestart.routedResponse hrouteStore
      (client := candidate.client) (id := candidate.id)
      (response := ⟨503, none⟩)
  rw [hnet] at hprotocol
  have hbase :
      (protocolMessages pre ++ protocolMessages post).Perm
        (optionList wire1) := by
    have hp := hprotocol.trans List.perm_append_comm
    apply Perm.cancel_exposed
    simpa [protocolMessages, List.append_assoc] using hp
  have hprotocolFinal :
      (protocolMessages
        (pre ++ post ++ routedOuts states "n2" emitted)).Perm
        (optionList wire1 ++ optionList wire) := by
    rw [protocolMessages_append, protocolMessages_append, hrouteProtocol]
    simpa [List.append_assoc] using hbase.append_right (optionList wire)
  have hcAdded := Covers.insert_both
    (left := appTokens pre ++ appTokens post ++ tokens1 ++ mailboxTokens mailbox)
    (right := []) (added := [response]) hcRest
  have hcoverFinal : Covers
      (appTokens (pre ++ post ++ routedOuts states "n2" emitted) ++
        tokens1 ++ tokens) a'.net := by
    rw [appTokens_append, appTokens_append, hrouteApp]
    apply Covers.of_perm _ hcAdded
    have hlocal :
        (mailboxTokens mailbox ++ [response]).Perm
          ([response] ++ tokens) :=
      List.perm_append_comm.trans
        (List.Perm.append_left [response] htokens.symm)
    have hwith :
        (tokens1 ++ mailboxTokens mailbox ++ [response]).Perm
          (tokens1 ++ [response] ++ tokens) := by
      simpa [List.append_assoc] using List.Perm.append_left tokens1 hlocal
    have hmove :
        (tokens1 ++ [response] ++ tokens).Perm
          ([response] ++ tokens1 ++ tokens) := by
      simpa [List.append_assoc] using
        (List.Perm.append_right tokens
          (List.perm_append_comm :
            (tokens1 ++ [response]).Perm ([response] ++ tokens1)))
    simpa [a', List.append_assoc] using
      (List.Perm.append_left (appTokens pre ++ appTokens post)
        (hwith.trans hmove))
  refine ⟨a', running, rest, wire, tokens, ?_, ?_, hrestart, ?_⟩
  · refine ⟨[((.server, a.now,
      .receive (.client candidate.client)
        (Msg.req candidate.id candidate.now candidate.req)),
      [.send candidate.client (Msg.res candidate.id ⟨503, none⟩)], a')],
      ?_, hobs, rfl⟩
    simpa [haeq] using hlegal
  · simpa [emitted] using hrun
  · refine ⟨node1, running, store, wire1, wire, tokens1, tokens,
      rfl, hn1, hrestart.nodeRep, ?_, ?_, ?_,
      Nat.le_trans htime hstepTime⟩
    · simpa [states, emitted, List.append_assoc] using hprotocolFinal
    · simpa [states, emitted, List.append_assoc] using hcoverFinal
    · simpa [a', haeq] using hstore'

theorem dispatch_onlyNotifies {cfg : Storage.Config} {call : Call}
    {doc : Option (Promise × Version)} {res : Response}
    {after : Experiment.State} {outs : List (Out Msg)}
    (hpick :
      pick ((Experiment.dispatch call.req call.now).run
        { cfg.app with unreliable := true }
        { promises := doc.toList.map (·.1) }) 0 = (res, after, outs)) :
    OnlyNotifies outs := by
  apply EmitsOnlyNotifies.dispatch call.req call.now
    { cfg.app with unreliable := true }
    { promises := doc.toList.map (·.1) } (res, after, outs)
  rw [← hpick]
  exact pick_mem _ _

def PreservesNonempty (h : Experiment.Handler α) : Prop :=
  ∀ cfg state result, state.promises ≠ [] →
    result ∈ (h cfg state).val → result.2.1.promises ≠ []

namespace PreservesNonempty

theorem pure (value : α) :
    PreservesNonempty (Pure.pure value : Experiment.Handler α) := by
  intro cfg state result hn hout
  change result ∈ [(value, state, [])] at hout
  simp only [List.mem_singleton] at hout
  subst result
  exact hn

theorem bind {first : Experiment.Handler α}
    {next : α → Experiment.Handler β}
    (hfirst : PreservesNonempty first)
    (hnext : ∀ value, PreservesNonempty (next value)) :
    PreservesNonempty (first >>= next) := by
  intro cfg state result hn hout
  simp only [Bind.bind, Some.bind, Some.map, List.mem_flatMap,
    List.mem_map] at hout
  obtain ⟨⟨value, middle, firstOut⟩, hm,
    ⟨answer, final, nextOut⟩, hf, rfl⟩ := hout
  exact hnext value cfg middle (answer, final, nextOut)
    (hfirst cfg state (value, middle, firstOut) hn hm) hf

theorem unchanged (h : Experiment.Handler α)
    (hrun : ∀ cfg state result, result ∈ (h cfg state).val →
      result.2.1 = state) : PreservesNonempty h := by
  intro cfg state result hn hout
  rw [hrun cfg state result hout]
  exact hn

theorem read : PreservesNonempty (read : Experiment.Handler Experiment.Config) :=
  unchanged _ (by
    intro cfg state result hout
    change result ∈ [(cfg, state, [])] at hout
    simpa only [List.mem_singleton] using
      congrArg (fun x => x.2.1) (List.mem_singleton.mp hout))

theorem readDefaultTimeout : PreservesNonempty Experiment.readDefaultTimeout :=
  unchanged _ (by
    intro cfg state result hout
    change result ∈ [(cfg.defaultTimeout, state, [])] at hout
    simpa only [List.mem_singleton] using
      congrArg (fun x => x.2.1) (List.mem_singleton.mp hout))

theorem emit (out : Out Msg) :
    PreservesNonempty (Experiment.emit out : Experiment.Handler Unit) :=
  unchanged _ (by
    intro cfg state result hout
    change result ∈ [((), state, [out])] at hout
    simpa only [List.mem_singleton] using
      congrArg (fun x => x.2.1) (List.mem_singleton.mp hout))

theorem choose (values : Some α) :
    PreservesNonempty (Experiment.choose values : Experiment.Handler α) := by
  intro cfg state result hn hout
  change result ∈ values.val.map (fun value => (value, state, [])) at hout
  obtain ⟨value, _, rfl⟩ := List.mem_map.mp hout
  exact hn

theorem lookup (key : Ident) :
    PreservesNonempty (Experiment.lookup key) :=
  unchanged _ (by
    intro cfg state result hout
    change result ∈ [(Experiment.promiseAt state key, state, [])] at hout
    simpa only [List.mem_singleton] using
      congrArg (fun x => x.2.1) (List.mem_singleton.mp hout))

theorem save (promise : Promise) :
    PreservesNonempty (Experiment.save promise) := by
  intro cfg state result hn hout
  change result ∈
    [((), ({ promises := promise ::
      state.promises.filter (·.id != promise.id) } : Experiment.State), [])] at hout
  simp only [List.mem_singleton] at hout
  subst result
  simp

theorem notifyAll (promise : Record) :
    ∀ addresses, PreservesNonempty (Experiment.notifyAll promise addresses) := by
  intro addresses
  induction addresses with
  | nil => exact pure ()
  | cons address rest ih =>
    exact bind (emit (.send address (.notify promise))) (fun _ => ih)

theorem settle (promise : Promise) (state : PromiseState) (value : String) :
    PreservesNonempty (Experiment.settle promise state value) := by
  unfold Experiment.settle
  refine bind (emit (.always _ _)) fun _ => ?_
  refine bind (emit (.always _ _)) fun _ => ?_
  refine bind (save _) fun _ => ?_
  refine bind (notifyAll _ _) fun _ => pure _

theorem load (key : Ident) (now : Time) :
    PreservesNonempty (Experiment.load key now) := by
  unfold Experiment.load
  refine bind (lookup key) ?_
  intro doc
  cases doc with
  | none => exact pure none
  | some promise =>
    change PreservesNonempty
      (if promise.state == .pending && decide (promise.timeoutAt ≤ now) then
        do let settled ← Experiment.settle promise .rejectedTimedout ""
           return some settled
       else Pure.pure (some promise))
    split
    · exact bind (settle promise .rejectedTimedout "") (fun value => pure (some value))
    · exact pure (some promise)

theorem promiseGet (key : Ident) (now : Time) :
    PreservesNonempty (Experiment.promiseGet key now) := by
  unfold Experiment.promiseGet
  refine bind (load key now) ?_
  intro doc
  cases doc <;> exact pure _

theorem promiseCreate (key : Ident) (timeoutAt : Option Time) (now : Time) :
    PreservesNonempty (Experiment.promiseCreate key timeoutAt now) := by
  unfold Experiment.promiseCreate
  refine bind (load key now) ?_
  intro doc
  cases doc with
  | some promise =>
    exact bind (emit (.sometimes _ _)) (fun _ => pure _)
  | none =>
    exact bind readDefaultTimeout (fun _ =>
      bind (save _) (fun _ => pure _))

theorem promiseSettle (key : Ident) (state : PromiseState)
    (value : String) (now : Time) :
    PreservesNonempty (Experiment.promiseSettle key state value now) := by
  unfold Experiment.promiseSettle
  split
  · exact pure _
  · refine bind (pure ()) fun _ => ?_
    refine bind (load key now) ?_
    intro doc
    cases doc with
    | none => exact pure _
    | some promise =>
      change PreservesNonempty
        (if promise.state == .pending then
          do let settled ← Experiment.settle promise state value
             return Experiment.ok settled
         else do
          Experiment.sometimes "settle arrives after the timeout"
            (promise.state == .rejectedTimedout)
          return Experiment.ok promise)
      split
      · exact bind (settle promise state value) (fun settled => pure _)
      · exact bind (emit (.sometimes _ _)) (fun _ => pure _)

theorem promiseListen (key : Ident) (address : Addr) (now : Time) :
    PreservesNonempty (Experiment.promiseListen key address now) := by
  unfold Experiment.promiseListen
  refine bind (load key now) ?_
  intro doc
  cases doc with
  | none => exact pure _
  | some promise =>
    change PreservesNonempty
      (if promise.state == .pending && !promise.listeners.contains address then
        let updated := { promise with
          listeners := promise.listeners ++ [address] }
        do Experiment.save updated; return Experiment.ok updated
       else Pure.pure (Experiment.ok promise))
    split
    · exact bind (save { promise with
        listeners := promise.listeners ++ [address] }) (fun _ => pure _)
    · exact pure _

theorem dispatch (request : Request) (now : Time) :
    PreservesNonempty (Experiment.dispatch request now) := by
  cases request with
  | get key => exact promiseGet key now
  | create key timeoutAt => exact promiseCreate key timeoutAt now
  | settle key state value => exact promiseSettle key state value now
  | listen key address => exact promiseListen key address now

end PreservesNonempty

theorem dispatch_changed_has_promise {cfg : Storage.Config} {call : Call}
    {doc : Option (Promise × Version)} {res : Response}
    {after : Experiment.State} {outs : List (Out Msg)}
    (hdoc : DocAtKey call.req.key doc)
    (hpick :
      pick ((Experiment.dispatch call.req call.now).run
        { cfg.app with unreliable := true }
        { promises := doc.toList.map (·.1) }) 0 = (res, after, outs))
    (hchanged : after ≠ { promises := doc.toList.map (·.1) }) :
    ∃ promise,
      after.promises.find? (·.id == call.req.key) = some promise := by
  have hmem : (res, after, outs) ∈
      ((Experiment.dispatch call.req call.now).run
        { cfg.app with unreliable := true }
        { promises := doc.toList.map (·.1) }).val := by
    rw [← hpick]
    exact pick_mem _ _
  have hlocal := PreservesKey.dispatch call.req call.now
    { cfg.app with unreliable := true }
    { promises := doc.toList.map (·.1) } (res, after, outs)
    (keyLocal_of_doc hdoc) hmem
  rcases hlocal with hempty | ⟨promise, hsingle, hid⟩
  · cases hd : doc with
    | none =>
      exact (hchanged (by cases after; simp_all)).elim
    | some value =>
      have hbefore :
          ({ promises := doc.toList.map (·.1) } :
            Experiment.State).promises ≠ [] := by simp [hd]
      exact ((PreservesNonempty.dispatch call.req call.now
        { cfg.app with unreliable := true }
        { promises := doc.toList.map (·.1) } (res, after, outs)
        hbefore hmem) hempty).elim
  · refine ⟨promise, ?_⟩
    rw [hsingle]
    simp [hid]

theorem sends_notes (outs : List (Out Msg)) : sends (notes outs) = [] := by
  induction outs with
  | nil => rfl
  | cons out rest ih =>
    cases out with
    | send to message =>
      change sends (notes rest) = []
      exact ih
    | always name ok =>
      change sends (notes rest) = []
      exact ih
    | sometimes name hit =>
      change sends (notes rest) = []
      exact ih

theorem routedOuts_notes (states : List (Addr × Local)) (source : Addr)
    (outs : List (Out Msg)) :
    routedOuts states source (notes outs) = [] := by
  rw [routedOuts, sends_notes]
  rfl

theorem split_of_get?_eq_some {xs : List α} {index : Nat} {value : α}
    (h : xs[index]? = some value) :
    ∃ pre post, xs = pre ++ value :: post ∧
      xs.eraseIdx index = pre ++ post := by
  induction xs generalizing index with
  | nil => simp at h
  | cons head tail ih =>
    cases index with
    | zero =>
      simp at h
      subst head
      exact ⟨[], tail, rfl, rfl⟩
    | succ index =>
      simp at h
      obtain ⟨pre, post, htail, herase⟩ := ih h
      refine ⟨head :: pre, post, ?_, ?_⟩
      · simp [htail]
      · simp [herase]

theorem normalRel_store_get_done_node1 {cfg : Storage.Config}
    {net : List ConcreteMessage} {now t : Time}
    {call : Call} {tries op next : Nat} {mailbox : List (Addr × CMsg)}
    {doc : Option (Promise × Version)} {res : Response}
    {after : Experiment.State} {outs : List (Out Msg)}
    {node2 : Running Storage.Config Nat CMsg} {store : Store}
    {wire2 : Option ConcreteMessage} {tokens2 : List AbstractMessage}
    {a : Experiment.Conf promises}
    (hstoreAddr : cfg.store = "s3")
    (happ : AppOnly mailbox) (hnext : next = op + 1)
    (hnone : take? (answers op) mailbox = none)
    (hpick :
      pick ((Experiment.dispatch call.req call.now).run
        { cfg.app with unreliable := true }
        { promises := doc.toList.map (·.1) }) 0 = (res, after, outs))
    (hunchanged : after = { promises := doc.toList.map (·.1) })
    (hn2 : NodeRep cfg store "n2" node2 wire2 tokens2)
    (hprotocol : (protocolMessages net).Perm
      ([((.proc "n1", .proc "s3", .get op call.req.key) :
        ConcreteMessage)] ++ optionList wire2))
    (hcover : Covers
      (appTokens net ++
        (mailboxTokens mailbox ++ [call.token]) ++ tokens2) a.net)
    (hstore : StoreRep store a.state) (htime : a.now ≤ now)
    (hstepTime : now ≤ t)
    (pre post : List ConcreteMessage)
    (hnet : net = pre ++
      ((.proc "n1", .proc "s3", .get op call.req.key) :
        ConcreteMessage) :: post)
    (hdocValue : doc = storeLookup store call.req.key) :
    let reply : ConcreteMessage := (.proc "s3", .proc "n1", .got op doc)
    ∃ a',
      Network.Matches { cfg.app with unreliable := true } clientView a
        (.proc "s3", t, .receive (.proc "n1")
          (CMsg.get op call.req.key)) a' ∧
      NormalRel cfg
        ⟨pre ++ post ++ [reply],
          [("n1", .node ⟨next, mailbox,
            loadK tries (call.retry tries)
              call.client call.id call.req call.now op⟩),
           ("n2", .node node2), ("s3", .store store)], t⟩ a' := by
  dsimp
  rw [hnet] at hcover
  have hcCall : Covers
      ((appTokens pre ++ appTokens post ++ mailboxTokens mailbox) ++
        call.token :: tokens2) a.net := by
    simpa [appTokens, appToken, List.append_assoc] using hcover
  obtain ⟨apre, apost, hanet, hcRest⟩ := Covers.consume hcCall
  have hdispatch :
      (res, after, outs) ∈
        ((Experiment.dispatch call.req call.now).run
          { cfg.app with unreliable := true }
          { promises := doc.toList.map (·.1) }).val := by
    rw [← hpick]
    exact pick_mem _ _
  have hrequest :
      (res, after, outs) ∈
        ((Experiment.request call.req call.now).run
          { cfg.app with unreliable := true }
          { promises := doc.toList.map (·.1) }).val :=
    dispatch_as_serve hdispatch
  obtain ⟨globalAfter, serviceOut, abstractNext, hservice,
      hlegal, hobs, hstore', haeq⟩ :=
    linearize_unchanged (cfg := cfg) hstore hdocValue.symm
      hrequest hunchanged hanet
  subst serviceOut
  subst abstractNext
  let emitted : List AbstractMessage :=
    outputTokens outs ++ [responseToken call.client call.id res]
  have hemitted :
      Experiment.emits .server
        (.receive (.client call.client)
          (Msg.req call.id call.now call.req))
        (outs ++ [.send call.client (Msg.res call.id res)]) = emitted := by
    simp [emitted, emits_outputs_response]
  let a' : Experiment.Conf promises :=
    ⟨apre ++ apost ++ emitted, globalAfter, a.now⟩
  refine ⟨a', ?_, ?_⟩
  · refine ⟨[((.server, a.now,
      .receive (.client call.client)
        (Msg.req call.id call.now call.req)),
      outs ++ [.send call.client (Msg.res call.id res)], a')], ?_, hobs, rfl⟩
    simpa [a', hemitted] using hlegal
  · let reply : ConcreteMessage := (.proc "s3", .proc "n1", .got op doc)
    refine ⟨_, node2, store, some reply, wire2,
      mailboxTokens mailbox ++ outputTokens outs ++
        [responseToken call.client call.id res],
      tokens2, rfl, ?_, hn2, ?_, ?_, hstore',
      Nat.le_trans htime hstepTime⟩
    · simpa [reply, hstoreAddr] using
        (NodeRep.loadingDone
          (cfg := cfg) (store := store) (address := "n1")
          (call := call) (tries := tries) (doc := doc)
          happ hnext hnone hpick hunchanged
          (Snapshot.of_lookup hdocValue.symm)
          (docAtKey_of_rep_lookup hstore hdocValue.symm))
    · rw [hnet] at hprotocol
      have hbase :
          (protocolMessages pre ++ protocolMessages post).Perm
            (optionList wire2) := by
        apply Perm.cancel_exposed
        simpa [protocolMessages, List.append_assoc] using hprotocol
      have hp := hbase.append_right [reply]
      have hswap :
          (optionList wire2 ++ [reply]).Perm
            ([reply] ++ optionList wire2) := List.perm_append_comm
      simpa [reply, protocolMessages, optionList, List.append_assoc] using
        hp.trans hswap
    · have hcAdded := Covers.insert_both
        (left := appTokens pre ++ appTokens post ++ mailboxTokens mailbox)
        (right := tokens2) (added := emitted) hcRest
      simpa [a', emitted, reply, appTokens, appToken,
        List.append_assoc] using hcAdded

theorem normalRel_store_get_done_node2 {cfg : Storage.Config}
    {net : List ConcreteMessage} {now t : Time}
    {call : Call} {tries op next : Nat} {mailbox : List (Addr × CMsg)}
    {doc : Option (Promise × Version)} {res : Response}
    {after : Experiment.State} {outs : List (Out Msg)}
    {node1 : Running Storage.Config Nat CMsg} {store : Store}
    {wire1 : Option ConcreteMessage} {tokens1 : List AbstractMessage}
    {a : Experiment.Conf promises}
    (hstoreAddr : cfg.store = "s3")
    (hn1 : NodeRep cfg store "n1" node1 wire1 tokens1)
    (happ : AppOnly mailbox) (hnext : next = op + 1)
    (hnone : take? (answers op) mailbox = none)
    (hpick :
      pick ((Experiment.dispatch call.req call.now).run
        { cfg.app with unreliable := true }
        { promises := doc.toList.map (·.1) }) 0 = (res, after, outs))
    (hunchanged : after = { promises := doc.toList.map (·.1) })
    (hprotocol : (protocolMessages net).Perm
      (optionList wire1 ++
        [((.proc "n2", .proc "s3", .get op call.req.key) :
          ConcreteMessage)]))
    (hcover : Covers
      (appTokens net ++ tokens1 ++
        (mailboxTokens mailbox ++ [call.token])) a.net)
    (hstore : StoreRep store a.state) (htime : a.now ≤ now)
    (hstepTime : now ≤ t)
    (pre post : List ConcreteMessage)
    (hnet : net = pre ++
      ((.proc "n2", .proc "s3", .get op call.req.key) :
        ConcreteMessage) :: post)
    (hdocValue : doc = storeLookup store call.req.key) :
    let reply : ConcreteMessage := (.proc "s3", .proc "n2", .got op doc)
    ∃ a',
      Network.Matches { cfg.app with unreliable := true } clientView a
        (.proc "s3", t, .receive (.proc "n2")
          (CMsg.get op call.req.key)) a' ∧
      NormalRel cfg
        ⟨pre ++ post ++ [reply],
          [("n1", .node node1),
           ("n2", .node ⟨next, mailbox,
            loadK tries (call.retry tries)
              call.client call.id call.req call.now op⟩),
           ("s3", .store store)], t⟩ a' := by
  dsimp
  rw [hnet] at hcover
  have hcCall : Covers
      ((appTokens pre ++ appTokens post ++ tokens1 ++ mailboxTokens mailbox) ++
        call.token :: []) a.net := by
    simpa [appTokens, appToken, List.append_assoc] using hcover
  obtain ⟨apre, apost, hanet, hcRest⟩ := Covers.consume hcCall
  have hdispatch :
      (res, after, outs) ∈
        ((Experiment.dispatch call.req call.now).run
          { cfg.app with unreliable := true }
          { promises := doc.toList.map (·.1) }).val := by
    rw [← hpick]
    exact pick_mem _ _
  have hrequest :
      (res, after, outs) ∈
        ((Experiment.request call.req call.now).run
          { cfg.app with unreliable := true }
          { promises := doc.toList.map (·.1) }).val :=
    dispatch_as_serve hdispatch
  obtain ⟨globalAfter, serviceOut, abstractNext, hservice,
      hlegal, hobs, hstore', haeq⟩ :=
    linearize_unchanged (cfg := cfg) hstore hdocValue.symm
      hrequest hunchanged hanet
  subst serviceOut
  subst abstractNext
  let emitted : List AbstractMessage :=
    outputTokens outs ++ [responseToken call.client call.id res]
  have hemitted :
      Experiment.emits .server
        (.receive (.client call.client)
          (Msg.req call.id call.now call.req))
        (outs ++ [.send call.client (Msg.res call.id res)]) = emitted := by
    simp [emitted, emits_outputs_response]
  let a' : Experiment.Conf promises :=
    ⟨apre ++ apost ++ emitted, globalAfter, a.now⟩
  refine ⟨a', ?_, ?_⟩
  · refine ⟨[((.server, a.now,
      .receive (.client call.client)
        (Msg.req call.id call.now call.req)),
      outs ++ [.send call.client (Msg.res call.id res)], a')], ?_, hobs, rfl⟩
    simpa [a', hemitted] using hlegal
  · let reply : ConcreteMessage := (.proc "s3", .proc "n2", .got op doc)
    refine ⟨node1, _, store, wire1, some reply, tokens1,
      mailboxTokens mailbox ++ outputTokens outs ++
        [responseToken call.client call.id res],
      rfl, hn1, ?_, ?_, ?_, hstore',
      Nat.le_trans htime hstepTime⟩
    · simpa [reply, hstoreAddr] using
        (NodeRep.loadingDone
          (cfg := cfg) (store := store) (address := "n2")
          (call := call) (tries := tries) (doc := doc)
          happ hnext hnone hpick hunchanged
          (Snapshot.of_lookup hdocValue.symm)
          (docAtKey_of_rep_lookup hstore hdocValue.symm))
    · rw [hnet] at hprotocol
      have hbase :
          (protocolMessages pre ++ protocolMessages post).Perm
            (optionList wire1) := by
        have hp := hprotocol.trans List.perm_append_comm
        apply Perm.cancel_exposed
        simpa [protocolMessages, List.append_assoc] using hp
      simpa [reply, protocolMessages, optionList, List.append_assoc] using
        hbase.append_right [reply]
    · have hcAdded := Covers.insert_both
        (left := appTokens pre ++ appTokens post ++ tokens1 ++
          mailboxTokens mailbox)
        (right := []) (added := emitted) hcRest
      simpa [a', emitted, reply, appTokens, appToken,
        List.append_assoc] using hcAdded

theorem normalRel_node1_got_done {cfg : Storage.Config}
    {net : List ConcreteMessage} {now t : Time}
    {call : Call} {tries op next : Nat} {mailbox : List (Addr × CMsg)}
    {doc : Option (Promise × Version)} {res : Response}
    {after : Experiment.State} {outs : List (Out Msg)}
    {node2 : Running Storage.Config Nat CMsg} {store : Store}
    {wire2 : Option ConcreteMessage} {tokens2 : List AbstractMessage}
    {a : Experiment.Conf promises}
    (hstoreAddr : cfg.store = "s3")
    (happ : AppOnly mailbox) (hnext : next = op + 1)
    (hnone : take? (answers op) mailbox = none)
    (hpick :
      pick ((Experiment.dispatch call.req call.now).run
        { cfg.app with unreliable := true }
        { promises := doc.toList.map (·.1) }) 0 = (res, after, outs))
    (hunchanged : after = { promises := doc.toList.map (·.1) })
    (hn2 : NodeRep cfg store "n2" node2 wire2 tokens2)
    (hprotocol : (protocolMessages net).Perm
      ([((.proc "s3", .proc "n1", .got op doc) : ConcreteMessage)] ++
        optionList wire2))
    (hcover : Covers
      (appTokens net ++
        (mailboxTokens mailbox ++ outputTokens outs ++
          [responseToken call.client call.id res]) ++ tokens2) a.net)
    (hstore : StoreRep store a.state) (htime : a.now ≤ now)
    (hstepTime : now ≤ t) (source : Network.Who)
    (pre post : List ConcreteMessage)
    (hnet : net = pre ++
      ((.proc "s3", .proc "n1", .got op doc) : ConcreteMessage) :: post) :
    ∃ running rest wire tokens,
      let states : List (Addr × Local) :=
        [("n1", .node running), ("n2", .node node2), ("s3", .store store)]
      let emitted : List (Out CMsg) :=
        notes outs ++
          .send call.client (.app (.res call.id res)) ::
            (sends outs).map (fun (address, message) =>
              .send address (.app message)) ++ rest
      (toStep node 64 source.addr (.got op doc) t cfg
        (⟨next, mailbox,
          loadK tries (call.retry tries)
            call.client call.id call.req call.now op⟩ :
          Running Storage.Config Nat CMsg)).val =
          [((), running, emitted)] ∧
      RestartRep cfg store "n1" running rest wire tokens ∧
      NormalRel cfg
        ⟨pre ++ post ++ routedOuts states "n1" emitted, states, t⟩ a := by
  obtain ⟨running, rest, wire, tokens, hrun, hrestart, htokens⟩ :=
    loading_got_unchanged_restart
      (cfg := cfg) (store := store) (address := "n1")
      happ hnone hpick hunchanged source.addr t
  let states : List (Addr × Local) :=
    [("n1", .node running), ("n2", .node node2), ("s3", .store store)]
  let emittedPrefix : List (Out CMsg) :=
    [.send call.client (.app (.res call.id res))] ++
      (sends outs).map
        (fun (address, message) => .send address (.app message))
  let emitted : List (Out CMsg) := notes outs ++ emittedPrefix ++ rest
  have hprefixProtocol :
      protocolMessages (routedOuts states "n1" emittedPrefix) = [] := by
    rw [show emittedPrefix =
      [.send call.client (.app (.res call.id res))] ++
        (sends outs).map
          (fun (address, message) => .send address (.app message)) from rfl]
    rw [routedOuts_append, protocolMessages_append,
      protocolMessages_routedResponse, protocolMessages_routedOutputs]
    rfl
  have hprefixApp :
      appTokens (routedOuts states "n1" emittedPrefix) =
        [responseToken call.client call.id res] ++ outputTokens outs := by
    rw [show emittedPrefix =
      [.send call.client (.app (.res call.id res))] ++
        (sends outs).map
          (fun (address, message) => .send address (.app message)) from rfl]
    rw [routedOuts_append, appTokens_append, appTokens_routedResponse,
      appTokens_routedOutputs states "n1" outs
        (dispatch_onlyNotifies (cfg := cfg) hpick)]
  have hrouteProtocol :
      protocolMessages (routedOuts states "n1" emitted) =
        optionList wire := by
    rw [show emitted = notes outs ++ (emittedPrefix ++ rest) by
          simp [emitted, List.append_assoc],
      routedOuts_append, routedOuts_notes, List.nil_append,
      routedOuts_append, protocolMessages_append, hprefixProtocol,
      List.nil_append]
    cases hrestart with
    | idle happ' hnone' => rfl
    | @loading nextCall nextOp next' mailbox' happ' hnext' hnone' =>
      simp [routedOuts, routedMessages, sends, protocolMessages,
        optionList, states, hstoreAddr, Network.Conf.route,
        Network.Conf.isProc]
  have hrouteApp :
      appTokens (routedOuts states "n1" emitted) =
        [responseToken call.client call.id res] ++ outputTokens outs := by
    rw [show emitted = notes outs ++ (emittedPrefix ++ rest) by
          simp [emitted, List.append_assoc],
      routedOuts_append, routedOuts_notes, List.nil_append,
      routedOuts_append, appTokens_append, hprefixApp]
    cases hrestart <;>
      simp [routedOuts, routedMessages, sends, appTokens, appToken,
        states, hstoreAddr, Network.Conf.route, Network.Conf.isProc]
  rw [hnet] at hprotocol hcover
  have hbase :
      (protocolMessages pre ++ protocolMessages post).Perm
        (optionList wire2) := by
    apply Perm.cancel_exposed
    simpa [protocolMessages, List.append_assoc] using hprotocol
  have hprotocolFinal :
      (protocolMessages
        (pre ++ post ++ routedOuts states "n1" emitted)).Perm
        (optionList wire ++ optionList wire2) := by
    rw [protocolMessages_append, protocolMessages_append, hrouteProtocol]
    have hp := hbase.append_right (optionList wire)
    simpa [List.append_assoc] using hp.trans
      (List.perm_append_comm :
        (optionList wire2 ++ optionList wire).Perm
          (optionList wire ++ optionList wire2))
  have hlocal :
      (mailboxTokens mailbox ++ outputTokens outs ++
          [responseToken call.client call.id res]).Perm
        ([responseToken call.client call.id res] ++
          outputTokens outs ++ tokens) := by
    have hfirst :
        (mailboxTokens mailbox ++ outputTokens outs ++
            [responseToken call.client call.id res]).Perm
          ([responseToken call.client call.id res] ++
            mailboxTokens mailbox ++ outputTokens outs) := by
      simpa [List.append_assoc] using
        (List.perm_append_comm :
          (mailboxTokens mailbox ++ outputTokens outs ++
            [responseToken call.client call.id res]).Perm
          ([responseToken call.client call.id res] ++
            mailboxTokens mailbox ++ outputTokens outs))
    have hmiddle :
        ([responseToken call.client call.id res] ++
            mailboxTokens mailbox ++ outputTokens outs).Perm
          ([responseToken call.client call.id res] ++
            tokens ++ outputTokens outs) := by
      simpa [List.append_assoc] using
        (List.Perm.append_left [responseToken call.client call.id res]
          (htokens.symm.append_right (outputTokens outs)))
    have hlast :
        ([responseToken call.client call.id res] ++
            tokens ++ outputTokens outs).Perm
          ([responseToken call.client call.id res] ++
            outputTokens outs ++ tokens) := by
      simpa [List.append_assoc] using
        (List.Perm.append_left [responseToken call.client call.id res]
          (List.perm_append_comm :
            (tokens ++ outputTokens outs).Perm
              (outputTokens outs ++ tokens)))
    exact hfirst.trans (hmiddle.trans hlast)
  have hold : Covers
      (appTokens pre ++ appTokens post ++
        (mailboxTokens mailbox ++ outputTokens outs ++
          [responseToken call.client call.id res]) ++ tokens2) a.net := by
    simpa [appTokens, appToken, List.append_assoc] using hcover
  have hcoverFinal : Covers
      (appTokens (pre ++ post ++ routedOuts states "n1" emitted) ++
        tokens ++ tokens2) a.net := by
    rw [appTokens_append, appTokens_append, hrouteApp]
    apply Covers.of_perm _ hold
    simpa [List.append_assoc] using
      (List.Perm.append_right tokens2
        (List.Perm.append_left (appTokens pre ++ appTokens post) hlocal))
  refine ⟨running, rest, wire, tokens, ?_, hrestart, ?_⟩
  · simpa [emitted, emittedPrefix, List.append_assoc] using hrun
  · refine ⟨running, node2, store, wire, wire2, tokens, tokens2,
      rfl, hrestart.nodeRep, hn2, ?_, ?_, hstore,
      Nat.le_trans htime hstepTime⟩
    · simpa [states, emitted, emittedPrefix, List.append_assoc] using
        hprotocolFinal
    · simpa [states, emitted, emittedPrefix, List.append_assoc] using
        hcoverFinal

theorem normalRel_node2_got_done {cfg : Storage.Config}
    {net : List ConcreteMessage} {now t : Time}
    {call : Call} {tries op next : Nat} {mailbox : List (Addr × CMsg)}
    {doc : Option (Promise × Version)} {res : Response}
    {after : Experiment.State} {outs : List (Out Msg)}
    {node1 : Running Storage.Config Nat CMsg} {store : Store}
    {wire1 : Option ConcreteMessage} {tokens1 : List AbstractMessage}
    {a : Experiment.Conf promises}
    (hstoreAddr : cfg.store = "s3")
    (hn1 : NodeRep cfg store "n1" node1 wire1 tokens1)
    (happ : AppOnly mailbox) (hnext : next = op + 1)
    (hnone : take? (answers op) mailbox = none)
    (hpick :
      pick ((Experiment.dispatch call.req call.now).run
        { cfg.app with unreliable := true }
        { promises := doc.toList.map (·.1) }) 0 = (res, after, outs))
    (hunchanged : after = { promises := doc.toList.map (·.1) })
    (hprotocol : (protocolMessages net).Perm
      (optionList wire1 ++
        [((.proc "s3", .proc "n2", .got op doc) : ConcreteMessage)]))
    (hcover : Covers
      (appTokens net ++ tokens1 ++
        (mailboxTokens mailbox ++ outputTokens outs ++
          [responseToken call.client call.id res])) a.net)
    (hstore : StoreRep store a.state) (htime : a.now ≤ now)
    (hstepTime : now ≤ t) (source : Network.Who)
    (pre post : List ConcreteMessage)
    (hnet : net = pre ++
      ((.proc "s3", .proc "n2", .got op doc) : ConcreteMessage) :: post) :
    ∃ running rest wire tokens,
      let states : List (Addr × Local) :=
        [("n1", .node node1), ("n2", .node running), ("s3", .store store)]
      let emitted : List (Out CMsg) :=
        notes outs ++
          .send call.client (.app (.res call.id res)) ::
            (sends outs).map (fun (address, message) =>
              .send address (.app message)) ++ rest
      (toStep node 64 source.addr (.got op doc) t cfg
        (⟨next, mailbox,
          loadK tries (call.retry tries)
            call.client call.id call.req call.now op⟩ :
          Running Storage.Config Nat CMsg)).val =
          [((), running, emitted)] ∧
      RestartRep cfg store "n2" running rest wire tokens ∧
      NormalRel cfg
        ⟨pre ++ post ++ routedOuts states "n2" emitted, states, t⟩ a := by
  obtain ⟨running, rest, wire, tokens, hrun, hrestart, htokens⟩ :=
    loading_got_unchanged_restart
      (cfg := cfg) (store := store) (address := "n2")
      happ hnone hpick hunchanged source.addr t
  let states : List (Addr × Local) :=
    [("n1", .node node1), ("n2", .node running), ("s3", .store store)]
  let emittedPrefix : List (Out CMsg) :=
    [.send call.client (.app (.res call.id res))] ++
      (sends outs).map
        (fun (address, message) => .send address (.app message))
  let emitted : List (Out CMsg) := notes outs ++ emittedPrefix ++ rest
  have hprefixProtocol :
      protocolMessages (routedOuts states "n2" emittedPrefix) = [] := by
    rw [show emittedPrefix =
      [.send call.client (.app (.res call.id res))] ++
        (sends outs).map
          (fun (address, message) => .send address (.app message)) from rfl]
    rw [routedOuts_append, protocolMessages_append,
      protocolMessages_routedResponse, protocolMessages_routedOutputs]
    rfl
  have hprefixApp :
      appTokens (routedOuts states "n2" emittedPrefix) =
        [responseToken call.client call.id res] ++ outputTokens outs := by
    rw [show emittedPrefix =
      [.send call.client (.app (.res call.id res))] ++
        (sends outs).map
          (fun (address, message) => .send address (.app message)) from rfl]
    rw [routedOuts_append, appTokens_append, appTokens_routedResponse,
      appTokens_routedOutputs states "n2" outs
        (dispatch_onlyNotifies (cfg := cfg) hpick)]
  have hrouteProtocol :
      protocolMessages (routedOuts states "n2" emitted) =
        optionList wire := by
    rw [show emitted = notes outs ++ (emittedPrefix ++ rest) by
          simp [emitted, List.append_assoc],
      routedOuts_append, routedOuts_notes, List.nil_append,
      routedOuts_append, protocolMessages_append, hprefixProtocol,
      List.nil_append]
    cases hrestart with
    | idle happ' hnone' => rfl
    | @loading nextCall nextOp next' mailbox' happ' hnext' hnone' =>
      simp [routedOuts, routedMessages, sends, protocolMessages,
        optionList, states, hstoreAddr, Network.Conf.route,
        Network.Conf.isProc]
  have hrouteApp :
      appTokens (routedOuts states "n2" emitted) =
        [responseToken call.client call.id res] ++ outputTokens outs := by
    rw [show emitted = notes outs ++ (emittedPrefix ++ rest) by
          simp [emitted, List.append_assoc],
      routedOuts_append, routedOuts_notes, List.nil_append,
      routedOuts_append, appTokens_append, hprefixApp]
    cases hrestart <;>
      simp [routedOuts, routedMessages, sends, appTokens, appToken,
        states, hstoreAddr, Network.Conf.route, Network.Conf.isProc]
  rw [hnet] at hprotocol hcover
  have hbase :
      (protocolMessages pre ++ protocolMessages post).Perm
        (optionList wire1) := by
    have hp := hprotocol.trans List.perm_append_comm
    apply Perm.cancel_exposed
    simpa [protocolMessages, List.append_assoc] using hp
  have hprotocolFinal :
      (protocolMessages
        (pre ++ post ++ routedOuts states "n2" emitted)).Perm
        (optionList wire1 ++ optionList wire) := by
    rw [protocolMessages_append, protocolMessages_append, hrouteProtocol]
    simpa [List.append_assoc] using hbase.append_right (optionList wire)
  have hlocal :
      (mailboxTokens mailbox ++ outputTokens outs ++
          [responseToken call.client call.id res]).Perm
        ([responseToken call.client call.id res] ++
          outputTokens outs ++ tokens) := by
    have hfirst :
        (mailboxTokens mailbox ++ outputTokens outs ++
            [responseToken call.client call.id res]).Perm
          ([responseToken call.client call.id res] ++
            mailboxTokens mailbox ++ outputTokens outs) := by
      simpa [List.append_assoc] using
        (List.perm_append_comm :
          (mailboxTokens mailbox ++ outputTokens outs ++
            [responseToken call.client call.id res]).Perm
          ([responseToken call.client call.id res] ++
            mailboxTokens mailbox ++ outputTokens outs))
    have hmiddle :
        ([responseToken call.client call.id res] ++
            mailboxTokens mailbox ++ outputTokens outs).Perm
          ([responseToken call.client call.id res] ++
            tokens ++ outputTokens outs) := by
      simpa [List.append_assoc] using
        (List.Perm.append_left [responseToken call.client call.id res]
          (htokens.symm.append_right (outputTokens outs)))
    have hlast :
        ([responseToken call.client call.id res] ++
            tokens ++ outputTokens outs).Perm
          ([responseToken call.client call.id res] ++
            outputTokens outs ++ tokens) := by
      simpa [List.append_assoc] using
        (List.Perm.append_left [responseToken call.client call.id res]
          (List.perm_append_comm :
            (tokens ++ outputTokens outs).Perm
              (outputTokens outs ++ tokens)))
    exact hfirst.trans (hmiddle.trans hlast)
  have hold : Covers
      (appTokens pre ++ appTokens post ++ tokens1 ++
        (mailboxTokens mailbox ++ outputTokens outs ++
          [responseToken call.client call.id res])) a.net := by
    simpa [appTokens, appToken, List.append_assoc] using hcover
  have hcoverFinal : Covers
      (appTokens (pre ++ post ++ routedOuts states "n2" emitted) ++
        tokens1 ++ tokens) a.net := by
    rw [appTokens_append, appTokens_append, hrouteApp]
    apply Covers.of_perm _ hold
    have hwith := List.Perm.append_left tokens1 hlocal
    have hmove :
        (tokens1 ++
          ([responseToken call.client call.id res] ++
            outputTokens outs ++ tokens)).Perm
        ([responseToken call.client call.id res] ++
          outputTokens outs ++ tokens1 ++ tokens) := by
      simpa [List.append_assoc] using
        (List.Perm.append_right tokens
          (List.perm_append_comm :
            (tokens1 ++
              ([responseToken call.client call.id res] ++
                outputTokens outs)).Perm
            (([responseToken call.client call.id res] ++
              outputTokens outs) ++ tokens1)))
    simpa [List.append_assoc] using
      (List.Perm.append_left (appTokens pre ++ appTokens post)
        (hwith.trans hmove))
  refine ⟨running, rest, wire, tokens, ?_, hrestart, ?_⟩
  · simpa [emitted, emittedPrefix, List.append_assoc] using hrun
  · refine ⟨node1, running, store, wire1, wire, tokens1, tokens,
      rfl, hn1, hrestart.nodeRep, ?_, ?_, hstore,
      Nat.le_trans htime hstepTime⟩
    · simpa [states, emitted, emittedPrefix, List.append_assoc] using
        hprotocolFinal
    · simpa [states, emitted, emittedPrefix, List.append_assoc] using
        hcoverFinal

theorem protocol_to_node1_is_wire {cfg : Storage.Config} {store : Store}
    {node1 node2 : Running Storage.Config Nat CMsg}
    {wire1 wire2 : Option ConcreteMessage}
    {tokens1 tokens2 : List AbstractMessage} {net : List ConcreteMessage}
    (hstoreAddr : cfg.store = "s3")
    (hn1 : NodeRep cfg store "n1" node1 wire1 tokens1)
    (hn2 : NodeRep cfg store "n2" node2 wire2 tokens2)
    (hp : (protocolMessages net).Perm
      (optionList wire1 ++ optionList wire2))
    {source : Network.Who} {message : CMsg}
    (hm : (source, .proc "n1", message) ∈ protocolMessages net) :
    wire1 = some (source, .proc "n1", message) := by
  have hout := (hp.mem_iff).1 hm
  simp only [List.mem_append] at hout
  rcases hout with hout | hout
  · cases wire1 <;> simp [optionList] at hout ⊢
    exact hout.symm
  · cases hn2 <;> simp [optionList, hstoreAddr] at hout

theorem protocol_to_node2_is_wire {cfg : Storage.Config} {store : Store}
    {node1 node2 : Running Storage.Config Nat CMsg}
    {wire1 wire2 : Option ConcreteMessage}
    {tokens1 tokens2 : List AbstractMessage} {net : List ConcreteMessage}
    (hstoreAddr : cfg.store = "s3")
    (hn1 : NodeRep cfg store "n1" node1 wire1 tokens1)
    (hn2 : NodeRep cfg store "n2" node2 wire2 tokens2)
    (hp : (protocolMessages net).Perm
      (optionList wire1 ++ optionList wire2))
    {source : Network.Who} {message : CMsg}
    (hm : (source, .proc "n2", message) ∈ protocolMessages net) :
    wire2 = some (source, .proc "n2", message) := by
  have hout := (hp.mem_iff).1 hm
  simp only [List.mem_append] at hout
  rcases hout with hout | hout
  · cases hn1 <;> simp [optionList, hstoreAddr] at hout
  · cases wire2 <;> simp [optionList] at hout ⊢
    exact hout.symm

theorem protocol_from_node1_to_store_is_wire {cfg : Storage.Config}
    {store : Store} {node1 node2 : Running Storage.Config Nat CMsg}
    {wire1 wire2 : Option ConcreteMessage}
    {tokens1 tokens2 : List AbstractMessage} {net : List ConcreteMessage}
    (hstoreAddr : cfg.store = "s3")
    (hn1 : NodeRep cfg store "n1" node1 wire1 tokens1)
    (hn2 : NodeRep cfg store "n2" node2 wire2 tokens2)
    (hp : (protocolMessages net).Perm
      (optionList wire1 ++ optionList wire2))
    {message : CMsg}
    (hm : (.proc "n1", .proc "s3", message) ∈ protocolMessages net) :
    wire1 = some (.proc "n1", .proc "s3", message) := by
  have hout := (hp.mem_iff).1 hm
  simp only [List.mem_append] at hout
  rcases hout with hout | hout
  · cases wire1 <;> simp [optionList] at hout ⊢
    exact hout.symm
  · cases hn2 <;> simp [optionList, hstoreAddr] at hout

theorem protocol_from_node2_to_store_is_wire {cfg : Storage.Config}
    {store : Store} {node1 node2 : Running Storage.Config Nat CMsg}
    {wire1 wire2 : Option ConcreteMessage}
    {tokens1 tokens2 : List AbstractMessage} {net : List ConcreteMessage}
    (hstoreAddr : cfg.store = "s3")
    (hn1 : NodeRep cfg store "n1" node1 wire1 tokens1)
    (hn2 : NodeRep cfg store "n2" node2 wire2 tokens2)
    (hp : (protocolMessages net).Perm
      (optionList wire1 ++ optionList wire2))
    {message : CMsg}
    (hm : (.proc "n2", .proc "s3", message) ∈ protocolMessages net) :
    wire2 = some (.proc "n2", .proc "s3", message) := by
  have hout := (hp.mem_iff).1 hm
  simp only [List.mem_append] at hout
  rcases hout with hout | hout
  · cases hn1 <;> simp [optionList, hstoreAddr] at hout
  · cases wire2 <;> simp [optionList] at hout ⊢
    exact hout.symm

theorem source_eq_s3_of_inbound_wire {cfg : Storage.Config}
    (hstoreAddr : cfg.store = "s3") {source destination : Network.Who}
    {message message' : CMsg}
    (h : (some (.proc cfg.store, destination, message) :
      Option ConcreteMessage) = some (source, destination, message')) :
    source = .proc "s3" := by
  cases source with
  | client address => simp at h
  | proc address =>
    simp only [Option.some.injEq, Prod.mk.injEq,
      Network.Who.proc.injEq] at h
    exact congrArg Network.Who.proc (h.1.symm.trans hstoreAddr)

@[simp] theorem sends_nil_cmsg : sends ([] : List (Out CMsg)) = [] := rfl

@[simp] theorem sends_singleton_cmsg (address : Addr) (message : CMsg) :
    sends [Out.send address message] = [(address, message)] := rfl

@[simp] theorem sends_append_cmsg (left right : List (Out CMsg)) :
    sends (left ++ right) = sends left ++ sends right := by
  induction left with
  | nil => rfl
  | cons out rest ih =>
    cases out <;> simp [sends, ih]

attribute [local simp] Network.Conf.route Network.Conf.isProc

set_option maxHeartbeats 2000000 in
theorem storage_simulationOn {cfg : Storage.Config}
    (hconditional : cfg.conditional = true) (hstoreAddr : cfg.store = "s3") :
    Network.SimulationOn cfg { cfg.app with unreliable := true }
      clientView DriveSafe (NormalRel cfg) := by
  intro c l stepOut c' a hrel hstep hok
  obtain ⟨t, act, htake⟩ := hstep
  cases act with
  | request client to message =>
    simp only [Network.Conf.take] at htake
    split at htake
    next hguard =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hguard
      have hstepTime : c.now ≤ t := by
        exact hguard.1
      simp only [Option.some.injEq, Prod.mk.injEq] at htake
      obtain ⟨rfl, rfl, rfl⟩ := htake
      cases message with
      | app message =>
        obtain ⟨node1, node2, store, wire1, wire2, tokens1, tokens2,
          hstates, hn1, hn2, hprotocol, hcover, hstore, htime⟩ := hrel
        let a' : Experiment.Conf promises :=
          ⟨a.net ++ [(.client client, .server, message)], a.state, t⟩
        refine ⟨a', matches_client_request
          (Nat.le_trans htime hstepTime), ?_⟩
        exact NormalRel.clientRequest
          ⟨node1, node2, store, wire1, wire2, tokens1, tokens2,
            hstates, hn1, hn2, hprotocol, hcover, hstore, htime⟩
          client to t message
      | get op key => simp [DriveSafe] at hok
      | put op key promise ifMatch => simp [DriveSafe] at hok
      | got op doc => simp [DriveSafe] at hok
      | written op => simp [DriveSafe] at hok
      | conflict op => simp [DriveSafe] at hok
      | failed op => simp [DriveSafe] at hok
    next => contradiction
  | deliver index choice =>
    simp only [Network.Conf.take] at htake
    split at htake <;> try contradiction
    next hstepTime =>
      split at htake <;> try contradiction
      next from_ client message hmessage =>
        simp only [Option.some.injEq, Prod.mk.injEq] at htake
        obtain ⟨rfl, rfl, rfl⟩ := htake
        obtain ⟨pre, post, hnet, herase⟩ :=
          split_of_get?_eq_some hmessage
        cases message with
        | app message =>
          obtain ⟨apre, apost, hanet, hrel'⟩ :=
            hrel.clientReceive from_ client t message pre post hnet
          let a' : Experiment.Conf promises :=
            ⟨apre ++ apost, a.state, t⟩
          refine ⟨a', matches_client_receive
            (Nat.le_trans (by
              obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, htime⟩ := hrel
              exact htime) hstepTime) hanet, ?_⟩
          simpa [a', herase] using hrel'
        | get op key =>
          obtain ⟨node1, node2, store, wire1, wire2, tokens1, tokens2,
            _, hn1, hn2, hprotocol, _, _, _⟩ := hrel
          have hm : (from_, .client client, CMsg.get op key) ∈
              protocolMessages c.net := by
            rw [hnet]
            simp [protocolMessages]
          obtain ⟨source, dest, m, heq⟩ :=
            protocol_message_is_between_procs hn1 hn2 hprotocol hm
          cases heq
        | put op key promise ifMatch =>
          obtain ⟨node1, node2, store, wire1, wire2, tokens1, tokens2,
            _, hn1, hn2, hprotocol, _, _, _⟩ := hrel
          have hm : (from_, .client client, CMsg.put op key promise ifMatch) ∈
              protocolMessages c.net := by
            rw [hnet]
            simp [protocolMessages]
          obtain ⟨source, dest, m, heq⟩ :=
            protocol_message_is_between_procs hn1 hn2 hprotocol hm
          cases heq
        | got op doc =>
          obtain ⟨node1, node2, store, wire1, wire2, tokens1, tokens2,
            _, hn1, hn2, hprotocol, _, _, _⟩ := hrel
          have hm : (from_, .client client, CMsg.got op doc) ∈
              protocolMessages c.net := by
            rw [hnet]
            simp [protocolMessages]
          obtain ⟨source, dest, m, heq⟩ :=
            protocol_message_is_between_procs hn1 hn2 hprotocol hm
          cases heq
        | written op =>
          obtain ⟨node1, node2, store, wire1, wire2, tokens1, tokens2,
            _, hn1, hn2, hprotocol, _, _, _⟩ := hrel
          have hm : (from_, .client client, CMsg.written op) ∈
              protocolMessages c.net := by
            rw [hnet]
            simp [protocolMessages]
          obtain ⟨source, dest, m, heq⟩ :=
            protocol_message_is_between_procs hn1 hn2 hprotocol hm
          cases heq
        | conflict op =>
          obtain ⟨node1, node2, store, wire1, wire2, tokens1, tokens2,
            _, hn1, hn2, hprotocol, _, _, _⟩ := hrel
          have hm : (from_, .client client, CMsg.conflict op) ∈
              protocolMessages c.net := by
            rw [hnet]
            simp [protocolMessages]
          obtain ⟨source, dest, m, heq⟩ :=
            protocol_message_is_between_procs hn1 hn2 hprotocol hm
          cases heq
        | failed op =>
          obtain ⟨node1, node2, store, wire1, wire2, tokens1, tokens2,
            _, hn1, hn2, hprotocol, _, _, _⟩ := hrel
          have hm : (from_, .client client, CMsg.failed op) ∈
              protocolMessages c.net := by
            rw [hnet]
            simp [protocolMessages]
          obtain ⟨source, dest, m, heq⟩ :=
            protocol_message_is_between_procs hn1 hn2 hprotocol hm
          cases heq
      next from_ proc message hmessage =>
        obtain ⟨node1, node2, store, wire1, wire2, tokens1, tokens2,
          hstates, hn1, hn2, hprotocol, hcover, hstore, htime⟩ := hrel
        obtain ⟨pre, post, hnet, herase⟩ :=
          split_of_get?_eq_some hmessage
        by_cases hp1 : proc = "n1"
        · subst proc
          cases message with
          | app message =>
            cases message with
            | res id response =>
              obtain ⟨node1', hrun, hrel'⟩ :=
                normalRel_node1_nonrequest hn1 hn2 hprotocol hcover hstore htime
                  from_ (.res id response) t hstepTime rfl pre post hnet
              have hservice := node_service_step_singleton hrun
              have hservice' :
                  system.step cfg (.node node1) t
                    (.msg from_.addr (.app (.res id response))) =
                    Some.one (.node node1', []) :=
                Subtype.ext hservice
              rw [herase] at htake
              simp [Network.Conf.run, Network.Conf.state?, hstates,
                hservice', Experiment.pick, Some.one] at htake
              obtain ⟨rfl, rfl, rfl⟩ := htake
              refine ⟨a, matches_hidden rfl, ?_⟩
              simpa [routedOuts, routedMessages, List.append_assoc,
                sends_notes] using hrel'
            | req id requestNow request =>
              by_cases hbusy : wire1 ≠ none
              · obtain ⟨node1', hrun, hrel'⟩ :=
                  normalRel_node1_request_busy hn1 hn2 hbusy hprotocol hcover
                    hstore htime from_ id requestNow t request hstepTime
                    pre post hnet
                have hservice := node_service_step_singleton hrun
                have hservice' :
                    system.step cfg (.node node1) t
                      (.msg from_.addr (.app (.req id requestNow request))) =
                      Some.one (.node node1', []) :=
                  Subtype.ext hservice
                rw [herase] at htake
                simp [Network.Conf.run, Network.Conf.state?, hstates,
                  hservice', Experiment.pick, Some.one] at htake
                obtain ⟨rfl, rfl, rfl⟩ := htake
                refine ⟨a, matches_hidden rfl, ?_⟩
                simpa [routedOuts, routedMessages, List.append_assoc,
                  sends_notes] using hrel'
              · have hw : wire1 = none := Classical.not_not.mp hbusy
                subst wire1
                cases hn1 with
                | @idle next mailbox happ hn =>
                  obtain ⟨hrun, hrel'⟩ :=
                    normalRel_node1_request_idle hstoreAddr happ hn hn2
                      (by simpa [optionList] using hprotocol)
                      (by simpa [List.append_assoc] using hcover)
                      hstore htime from_ id requestNow t request hstepTime
                      pre post hnet
                  have hservice := node_service_step_singleton hrun
                  have hservice' :
                      system.step cfg (.node ⟨next, mailbox, node⟩) t
                        (.msg from_.addr (.app (.req id requestNow request))) =
                        Some.one (.node
                          ⟨next + 1, mailbox,
                            loadK cfg.retries
                              (Call.retry
                                ⟨from_.addr, id, request, requestNow⟩
                                cfg.retries)
                              from_.addr id request requestNow next⟩,
                          [.send "s3" (.get next request.key)]) :=
                    Subtype.ext hservice
                  rw [herase] at htake
                  simp [Network.Conf.run, Network.Conf.state?, hstates,
                    hservice', Experiment.pick, Some.one] at htake
                  obtain ⟨rfl, rfl, rfl⟩ := htake
                  refine ⟨a, matches_hidden rfl, ?_⟩
                  simpa [List.append_assoc] using hrel'
            | notify promise =>
              obtain ⟨node1', hrun, hrel'⟩ :=
                normalRel_node1_nonrequest hn1 hn2 hprotocol hcover hstore htime
                  from_ (.notify promise) t hstepTime rfl pre post hnet
              have hservice := node_service_step_singleton hrun
              have hservice' :
                  system.step cfg (.node node1) t
                    (.msg from_.addr (.app (.notify promise))) =
                    Some.one (.node node1', []) :=
                Subtype.ext hservice
              rw [herase] at htake
              simp [Network.Conf.run, Network.Conf.state?, hstates,
                hservice', Experiment.pick, Some.one] at htake
              obtain ⟨rfl, rfl, rfl⟩ := htake
              refine ⟨a, matches_hidden rfl, ?_⟩
              simpa [routedOuts, routedMessages, List.append_assoc,
                sends_notes] using hrel'
          | get op key =>
            have hm : (from_, .proc "n1", CMsg.get op key) ∈
                protocolMessages c.net := by
              rw [hnet]
              simp [protocolMessages]
            have hw := protocol_to_node1_is_wire hstoreAddr hn1 hn2
              hprotocol hm
            cases hn1 <;> simp [hstoreAddr] at hw
          | put op key promise ifMatch =>
            have hm : (from_, .proc "n1", CMsg.put op key promise ifMatch) ∈
                protocolMessages c.net := by
              rw [hnet]
              simp [protocolMessages]
            have hw := protocol_to_node1_is_wire hstoreAddr hn1 hn2
              hprotocol hm
            cases hn1 <;> simp [hstoreAddr] at hw
          | got op doc =>
            have hm : (from_, .proc "n1", CMsg.got op doc) ∈
                protocolMessages c.net := by
              rw [hnet]
              simp [protocolMessages]
            have hw := protocol_to_node1_is_wire hstoreAddr hn1 hn2
              hprotocol hm
            cases hn1 with
            | idle happ hn => simp [optionList] at hw
            | loadingGet happ hnext hn => simp [hstoreAddr] at hw
            | @loadingGot call tries loadedOp next mailbox loadedDoc
                happ hnext hn hchanged hs hd =>
              have hfrom := source_eq_s3_of_inbound_wire hstoreAddr hw
              subst from_
              simp only [hstoreAddr] at hprotocol
              have hmsg := congrArg (fun x : ConcreteMessage => x.2.2)
                (Option.some.inj hw)
              injection hmsg with hop hdoc
              subst op
              subst doc
              obtain ⟨res, after, outs, hpick, hchanged⟩ := hchanged
              obtain ⟨promise, hpromise⟩ :=
                dispatch_changed_has_promise hd hpick hchanged
              obtain ⟨hrun, hrel'⟩ :=
                normalRel_node1_got_changed hstoreAddr happ hnext hn hpick
                  (beq_eq_false_iff_ne.mpr hchanged) hpromise hs hd hn2
                  hprotocol hcover hstore htime hstepTime (.proc "s3") pre post hnet
              have hservice := node_service_step_singleton hrun
              have hservice' :
                  system.step cfg (.node ⟨next, mailbox,
                    loadK tries (call.retry tries)
                      call.client call.id call.req call.now loadedOp⟩) t
                    (.msg (Network.Who.proc "s3").addr (.got loadedOp loadedDoc)) =
                    Some.one (.node _, _) :=
                Subtype.ext hservice
              rw [herase] at htake
              simp [Network.Conf.run, Network.Conf.state?, hstates,
                hservice', Experiment.pick, Some.one] at htake
              obtain ⟨rfl, rfl, rfl⟩ := htake
              refine ⟨a, matches_hidden rfl, ?_⟩
              simpa [routedOuts, routedMessages, List.append_assoc,
                sends_notes] using hrel'
            | @loadingDone call tries loadedOp next mailbox loadedDoc
                res after outs happ hnext hn hpick hunchanged hs hd =>
              have hfrom := source_eq_s3_of_inbound_wire hstoreAddr hw
              subst from_
              simp only [hstoreAddr] at hprotocol
              have hmsg := congrArg (fun x : ConcreteMessage => x.2.2)
                (Option.some.inj hw)
              injection hmsg with hop hdoc
              subst op
              subst doc
              obtain ⟨running, rest, wire, tokens, hrun, hrestart, hrel'⟩ :=
                normalRel_node1_got_done hstoreAddr happ hnext hn hpick
                  hunchanged hn2 hprotocol hcover hstore htime hstepTime
                  (.proc "s3") pre post hnet
              have hservice := node_service_step_singleton hrun
              have hservice' :
                  system.step cfg (.node ⟨next, mailbox,
                    loadK tries (call.retry tries)
                      call.client call.id call.req call.now loadedOp⟩) t
                    (.msg (Network.Who.proc "s3").addr (.got loadedOp loadedDoc)) =
                    Some.one (.node running, _) :=
                Subtype.ext hservice
              rw [herase] at htake
              simp [Network.Conf.run, Network.Conf.state?, hstates,
                hservice', Experiment.pick, Some.one] at htake
              obtain ⟨rfl, rfl, rfl⟩ := htake
              refine ⟨a, matches_hidden rfl, ?_⟩
              simpa [routedOuts, routedMessages, List.append_assoc,
                sends_notes] using hrel'
            | writingPut happ hnext hn hv hs => simp [hstoreAddr] at hw
            | writingConflict happ hnext hn hv hs => simp at hw
            | writingServed happ hnext hn hv => simp at hw
            | writingLost happ hnext hn hv => simp at hw
            | writingShed happ hnext hn hv hs => simp at hw
          | written op =>
            have hm : (from_, .proc "n1", CMsg.written op) ∈
                protocolMessages c.net := by
              rw [hnet]
              simp [protocolMessages]
            have hw := protocol_to_node1_is_wire hstoreAddr hn1 hn2
              hprotocol hm
            cases hn1 with
            | idle happ hn => simp at hw
            | loadingGet happ hnext hn => simp [hstoreAddr] at hw
            | loadingGot happ hnext hn hc hs hd => simp at hw
            | loadingDone happ hnext hn hp hu hs hd => simp at hw
            | writingPut happ hnext hn hv hs => simp [hstoreAddr] at hw
            | writingConflict happ hnext hn hv hs => simp at hw
            | @writingServed candidate loadedOp next mailbox
                happ hnext hn hvalid =>
              have hfrom := source_eq_s3_of_inbound_wire hstoreAddr hw
              subst from_
              simp only [hstoreAddr] at hprotocol
              have hmsg := congrArg (fun x : ConcreteMessage => x.2.2)
                (Option.some.inj hw)
              injection hmsg with hop
              subst op
              obtain ⟨running, rest, wire, tokens, hrun, hrestart, hrel'⟩ :=
                normalRel_node1_written hstoreAddr happ hnext hn hvalid hn2
                  hprotocol hcover hstore htime hstepTime (.proc "s3") pre post hnet
              have hservice := node_service_step_singleton hrun
              have hservice' :
                  system.step cfg (.node ⟨next, mailbox,
                    writeK candidate.tries
                      (candidate.call.retry candidate.tries)
                      candidate loadedOp⟩) t
                    (.msg (Network.Who.proc "s3").addr (.written loadedOp)) =
                    Some.one (.node running, _) :=
                Subtype.ext hservice
              rw [herase] at htake
              simp [Network.Conf.run, Network.Conf.state?, hstates,
                hservice', Experiment.pick, Some.one] at htake
              obtain ⟨rfl, rfl, rfl⟩ := htake
              refine ⟨a, matches_hidden rfl, ?_⟩
              simpa [routedOuts, routedMessages, List.append_assoc,
                sends_notes] using hrel'
            | writingLost happ hnext hn hv => simp at hw
            | writingShed happ hnext hn hv hs => simp at hw
          | conflict op =>
            have hm : (from_, .proc "n1", CMsg.conflict op) ∈
                protocolMessages c.net := by
              rw [hnet]
              simp [protocolMessages]
            have hw := protocol_to_node1_is_wire hstoreAddr hn1 hn2
              hprotocol hm
            cases hn1 with
            | idle happ hn => simp at hw
            | loadingGet happ hnext hn => simp [hstoreAddr] at hw
            | loadingGot happ hnext hn hc hs hd => simp at hw
            | loadingDone happ hnext hn hp hu hs hd => simp at hw
            | writingPut happ hnext hn hv hs => simp [hstoreAddr] at hw
            | @writingConflict candidate loadedOp next mailbox
                happ hnext hn hvalid hs =>
              have hfrom := source_eq_s3_of_inbound_wire hstoreAddr hw
              subst from_
              simp only [hstoreAddr] at hprotocol
              have hmsg := congrArg (fun x : ConcreteMessage => x.2.2)
                (Option.some.inj hw)
              injection hmsg with hop
              subst op
              cases htries : candidate.tries with
              | zero =>
                obtain ⟨a', running, rest, wire, tokens,
                    hmatch, hrun, hrestart, hrel'⟩ :=
                  normalRel_node1_conflict_exhausted hstoreAddr happ hnext hn
                    htries hn2 hprotocol hcover hstore htime hstepTime (.proc "s3")
                    pre post hnet
                have hservice := node_service_step_singleton hrun
                have hservice' :
                    system.step cfg (.node ⟨next, mailbox,
                      writeK candidate.tries
                        (candidate.call.retry candidate.tries)
                        candidate loadedOp⟩) t
                      (.msg (Network.Who.proc "s3").addr (.conflict loadedOp)) =
                      Some.one (.node running, _) :=
                  Subtype.ext hservice
                rw [herase] at htake
                simp [Network.Conf.run, Network.Conf.state?, hstates,
                  hservice', Experiment.pick, Some.one] at htake
                obtain ⟨rfl, rfl, rfl⟩ := htake
                refine ⟨a', hmatch, ?_⟩
                simpa [routedOuts, routedMessages, List.append_assoc,
                  sends_notes] using hrel'
              | succ k =>
                obtain ⟨hrun, hrel'⟩ :=
                  normalRel_node1_conflict_retry hstoreAddr happ hnext hn
                    hvalid hs htries hn2 hprotocol hcover hstore htime
                    hstepTime (.proc "s3") pre post hnet
                have hservice := node_service_step_singleton hrun
                have hservice' :
                    system.step cfg (.node ⟨next, mailbox,
                      writeK candidate.tries
                        (candidate.call.retry candidate.tries)
                        candidate loadedOp⟩) t
                      (.msg (Network.Who.proc "s3").addr (.conflict loadedOp)) =
                      Some.one (.node _, _) :=
                  Subtype.ext hservice
                rw [herase] at htake
                simp [Network.Conf.run, Network.Conf.state?, hstates,
                  hservice', Experiment.pick, Some.one] at htake
                obtain ⟨rfl, rfl, rfl⟩ := htake
                refine ⟨a, matches_hidden rfl, ?_⟩
                simpa [routedOuts, routedMessages, List.append_assoc,
                  sends_notes] using hrel'
            | writingServed happ hnext hn hv => simp at hw
            | writingLost happ hnext hn hv => simp at hw
            | writingShed happ hnext hn hv hs => simp at hw
          | failed op =>
            have hm : (from_, .proc "n1", CMsg.failed op) ∈
                protocolMessages c.net := by
              rw [hnet]
              simp [protocolMessages]
            have hw := protocol_to_node1_is_wire hstoreAddr hn1 hn2
              hprotocol hm
            cases hn1 with
            | idle happ hn => simp at hw
            | loadingGet happ hnext hn => simp [hstoreAddr] at hw
            | loadingGot happ hnext hn hc hs hd => simp at hw
            | loadingDone happ hnext hn hp hu hs hd => simp at hw
            | writingPut happ hnext hn hv hs => simp [hstoreAddr] at hw
            | writingConflict happ hnext hn hv hs => simp at hw
            | writingServed happ hnext hn hv => simp at hw
            | @writingLost candidate loadedOp next mailbox
                happ hnext hn hvalid =>
              have hfrom := source_eq_s3_of_inbound_wire hstoreAddr hw
              subst from_
              simp only [hstoreAddr] at hprotocol
              have hmsg := congrArg (fun x : ConcreteMessage => x.2.2)
                (Option.some.inj hw)
              injection hmsg with hop
              subst op
              obtain ⟨running, rest, wire, tokens, hrun, hrestart, hrel'⟩ :=
                normalRel_node1_failed hstoreAddr happ hnext hn (Or.inr rfl)
                  hn2 hprotocol hcover hstore htime hstepTime (.proc "s3")
                  pre post hnet
              have hservice := node_service_step_singleton hrun
              have hservice' :
                  system.step cfg (.node ⟨next, mailbox,
                    writeK candidate.tries
                      (candidate.call.retry candidate.tries)
                      candidate loadedOp⟩) t
                    (.msg (Network.Who.proc "s3").addr (.failed loadedOp)) =
                    Some.one (.node running, _) :=
                Subtype.ext hservice
              rw [herase] at htake
              simp [Network.Conf.run, Network.Conf.state?, hstates,
                hservice', Experiment.pick, Some.one] at htake
              obtain ⟨rfl, rfl, rfl⟩ := htake
              refine ⟨a, matches_hidden rfl, ?_⟩
              simpa [routedOuts, routedMessages, List.append_assoc,
                sends_notes] using hrel'
            | @writingShed candidate loadedOp next mailbox
                happ hnext hn hvalid hs =>
              have hfrom := source_eq_s3_of_inbound_wire hstoreAddr hw
              subst from_
              simp only [hstoreAddr] at hprotocol
              have hmsg := congrArg (fun x : ConcreteMessage => x.2.2)
                (Option.some.inj hw)
              injection hmsg with hop
              subst op
              obtain ⟨running, rest, wire, tokens, hrun, hrestart, hrel'⟩ :=
                normalRel_node1_failed hstoreAddr happ hnext hn (Or.inl rfl)
                  hn2 hprotocol hcover hstore htime hstepTime (.proc "s3")
                  pre post hnet
              have hservice := node_service_step_singleton hrun
              have hservice' :
                  system.step cfg (.node ⟨next, mailbox,
                    writeK candidate.tries
                      (candidate.call.retry candidate.tries)
                      candidate loadedOp⟩) t
                    (.msg (Network.Who.proc "s3").addr (.failed loadedOp)) =
                    Some.one (.node running, _) :=
                Subtype.ext hservice
              rw [herase] at htake
              simp [Network.Conf.run, Network.Conf.state?, hstates,
                hservice', Experiment.pick, Some.one] at htake
              obtain ⟨rfl, rfl, rfl⟩ := htake
              refine ⟨a, matches_hidden rfl, ?_⟩
              simpa [routedOuts, routedMessages, List.append_assoc,
                sends_notes] using hrel'
        · by_cases hp2 : proc = "n2"
          · subst proc
            cases message with
            | app message =>
              cases message with
              | res id response =>
                obtain ⟨node2', hrun, hrel'⟩ :=
                  normalRel_node2_nonrequest hn1 hn2 hprotocol hcover hstore htime
                    from_ (.res id response) t hstepTime rfl pre post hnet
                have hservice := node_service_step_singleton hrun
                have hservice' :
                    system.step cfg (.node node2) t
                      (.msg from_.addr (.app (.res id response))) =
                      Some.one (.node node2', []) :=
                  Subtype.ext hservice
                rw [herase] at htake
                simp [Network.Conf.run, Network.Conf.state?, hstates,
                  hservice', Experiment.pick, Some.one] at htake
                obtain ⟨rfl, rfl, rfl⟩ := htake
                refine ⟨a, matches_hidden rfl, ?_⟩
                simpa [routedOuts, routedMessages, List.append_assoc,
                  sends_notes] using hrel'
              | req id requestNow request =>
                by_cases hbusy : wire2 ≠ none
                · obtain ⟨node2', hrun, hrel'⟩ :=
                    normalRel_node2_request_busy hn1 hn2 hbusy hprotocol hcover
                      hstore htime from_ id requestNow t request hstepTime
                      pre post hnet
                  have hservice := node_service_step_singleton hrun
                  have hservice' :
                      system.step cfg (.node node2) t
                        (.msg from_.addr (.app (.req id requestNow request))) =
                        Some.one (.node node2', []) :=
                    Subtype.ext hservice
                  rw [herase] at htake
                  simp [Network.Conf.run, Network.Conf.state?, hstates,
                    hservice', Experiment.pick, Some.one] at htake
                  obtain ⟨rfl, rfl, rfl⟩ := htake
                  refine ⟨a, matches_hidden rfl, ?_⟩
                  simpa [routedOuts, routedMessages, List.append_assoc,
                    sends_notes] using hrel'
                · have hw : wire2 = none := Classical.not_not.mp hbusy
                  subst wire2
                  cases hn2 with
                  | @idle next mailbox happ hn =>
                    obtain ⟨hrun, hrel'⟩ :=
                      normalRel_node2_request_idle hstoreAddr hn1 happ hn
                        (by simpa [optionList] using hprotocol)
                        (by simpa [List.append_assoc] using hcover)
                        hstore htime from_ id requestNow t request hstepTime
                        pre post hnet
                    have hservice := node_service_step_singleton hrun
                    have hservice' :
                        system.step cfg (.node ⟨next, mailbox, node⟩) t
                          (.msg from_.addr (.app (.req id requestNow request))) =
                          Some.one (.node
                            ⟨next + 1, mailbox,
                              loadK cfg.retries
                                (Call.retry
                                  ⟨from_.addr, id, request, requestNow⟩
                                  cfg.retries)
                                from_.addr id request requestNow next⟩,
                            [.send "s3" (.get next request.key)]) :=
                      Subtype.ext hservice
                    rw [herase] at htake
                    simp [Network.Conf.run, Network.Conf.state?, hstates,
                      hservice', Experiment.pick, Some.one] at htake
                    obtain ⟨rfl, rfl, rfl⟩ := htake
                    refine ⟨a, matches_hidden rfl, ?_⟩
                    simpa [List.append_assoc] using hrel'
              | notify promise =>
                obtain ⟨node2', hrun, hrel'⟩ :=
                  normalRel_node2_nonrequest hn1 hn2 hprotocol hcover hstore htime
                    from_ (.notify promise) t hstepTime rfl pre post hnet
                have hservice := node_service_step_singleton hrun
                have hservice' :
                    system.step cfg (.node node2) t
                      (.msg from_.addr (.app (.notify promise))) =
                      Some.one (.node node2', []) :=
                  Subtype.ext hservice
                rw [herase] at htake
                simp [Network.Conf.run, Network.Conf.state?, hstates,
                  hservice', Experiment.pick, Some.one] at htake
                obtain ⟨rfl, rfl, rfl⟩ := htake
                refine ⟨a, matches_hidden rfl, ?_⟩
                simpa [routedOuts, routedMessages, List.append_assoc,
                  sends_notes] using hrel'
            | get op key =>
              have hm : (from_, .proc "n2", CMsg.get op key) ∈
                  protocolMessages c.net := by
                rw [hnet]
                simp [protocolMessages]
              have hw := protocol_to_node2_is_wire hstoreAddr hn1 hn2
                hprotocol hm
              cases hn2 <;> simp [hstoreAddr] at hw
            | put op key promise ifMatch =>
              have hm : (from_, .proc "n2", CMsg.put op key promise ifMatch) ∈
                  protocolMessages c.net := by
                rw [hnet]
                simp [protocolMessages]
              have hw := protocol_to_node2_is_wire hstoreAddr hn1 hn2
                hprotocol hm
              cases hn2 <;> simp [hstoreAddr] at hw
            | got op doc =>
              have hm : (from_, .proc "n2", CMsg.got op doc) ∈
                  protocolMessages c.net := by
                rw [hnet]
                simp [protocolMessages]
              have hw := protocol_to_node2_is_wire hstoreAddr hn1 hn2
                hprotocol hm
              cases hn2 with
              | idle happ hn => simp [optionList] at hw
              | loadingGet happ hnext hn => simp [hstoreAddr] at hw
              | @loadingGot call tries loadedOp next mailbox loadedDoc
                  happ hnext hn hchanged hs hd =>
                have hfrom := source_eq_s3_of_inbound_wire hstoreAddr hw
                subst from_
                simp only [hstoreAddr] at hprotocol
                have hmsg := congrArg (fun x : ConcreteMessage => x.2.2)
                  (Option.some.inj hw)
                injection hmsg with hop hdoc
                subst op
                subst doc
                obtain ⟨res, after, outs, hpick, hchanged⟩ := hchanged
                obtain ⟨promise, hpromise⟩ :=
                  dispatch_changed_has_promise hd hpick hchanged
                obtain ⟨hrun, hrel'⟩ :=
                  normalRel_node2_got_changed hstoreAddr hn1 happ hnext hn hpick
                    (beq_eq_false_iff_ne.mpr hchanged) hpromise hs hd
                    hprotocol hcover hstore htime hstepTime (.proc "s3") pre post hnet
                have hservice := node_service_step_singleton hrun
                have hservice' :
                    system.step cfg (.node ⟨next, mailbox,
                      loadK tries (call.retry tries)
                        call.client call.id call.req call.now loadedOp⟩) t
                      (.msg (Network.Who.proc "s3").addr (.got loadedOp loadedDoc)) =
                      Some.one (.node _, _) :=
                  Subtype.ext hservice
                rw [herase] at htake
                simp [Network.Conf.run, Network.Conf.state?, hstates,
                  hservice', Experiment.pick, Some.one] at htake
                obtain ⟨rfl, rfl, rfl⟩ := htake
                refine ⟨a, matches_hidden rfl, ?_⟩
                simpa [routedOuts, routedMessages, List.append_assoc,
                  sends_notes] using hrel'
              | @loadingDone call tries loadedOp next mailbox loadedDoc
                  res after outs happ hnext hn hpick hunchanged hs hd =>
                have hfrom := source_eq_s3_of_inbound_wire hstoreAddr hw
                subst from_
                simp only [hstoreAddr] at hprotocol
                have hmsg := congrArg (fun x : ConcreteMessage => x.2.2)
                  (Option.some.inj hw)
                injection hmsg with hop hdoc
                subst op
                subst doc
                obtain ⟨running, rest, wire, tokens, hrun, hrestart, hrel'⟩ :=
                  normalRel_node2_got_done hstoreAddr hn1 happ hnext hn hpick
                    hunchanged hprotocol hcover hstore htime hstepTime
                    (.proc "s3") pre post hnet
                have hservice := node_service_step_singleton hrun
                have hservice' :
                    system.step cfg (.node ⟨next, mailbox,
                      loadK tries (call.retry tries)
                        call.client call.id call.req call.now loadedOp⟩) t
                      (.msg (Network.Who.proc "s3").addr (.got loadedOp loadedDoc)) =
                      Some.one (.node running, _) :=
                  Subtype.ext hservice
                rw [herase] at htake
                simp [Network.Conf.run, Network.Conf.state?, hstates,
                  hservice', Experiment.pick, Some.one] at htake
                obtain ⟨rfl, rfl, rfl⟩ := htake
                refine ⟨a, matches_hidden rfl, ?_⟩
                simpa [routedOuts, routedMessages, List.append_assoc,
                  sends_notes] using hrel'
              | writingPut happ hnext hn hv hs => simp [hstoreAddr] at hw
              | writingConflict happ hnext hn hv hs => simp at hw
              | writingServed happ hnext hn hv => simp at hw
              | writingLost happ hnext hn hv => simp at hw
              | writingShed happ hnext hn hv hs => simp at hw
            | written op =>
              have hm : (from_, .proc "n2", CMsg.written op) ∈
                  protocolMessages c.net := by
                rw [hnet]
                simp [protocolMessages]
              have hw := protocol_to_node2_is_wire hstoreAddr hn1 hn2
                hprotocol hm
              cases hn2 with
              | idle happ hn => simp at hw
              | loadingGet happ hnext hn => simp [hstoreAddr] at hw
              | loadingGot happ hnext hn hc hs hd => simp at hw
              | loadingDone happ hnext hn hp hu hs hd => simp at hw
              | writingPut happ hnext hn hv hs => simp [hstoreAddr] at hw
              | writingConflict happ hnext hn hv hs => simp at hw
              | @writingServed candidate loadedOp next mailbox
                  happ hnext hn hvalid =>
                have hfrom := source_eq_s3_of_inbound_wire hstoreAddr hw
                subst from_
                simp only [hstoreAddr] at hprotocol
                have hmsg := congrArg (fun x : ConcreteMessage => x.2.2)
                  (Option.some.inj hw)
                injection hmsg with hop
                subst op
                obtain ⟨running, rest, wire, tokens, hrun, hrestart, hrel'⟩ :=
                  normalRel_node2_written hstoreAddr hn1 happ hnext hn hvalid
                    hprotocol hcover hstore htime hstepTime (.proc "s3") pre post hnet
                have hservice := node_service_step_singleton hrun
                have hservice' :
                    system.step cfg (.node ⟨next, mailbox,
                      writeK candidate.tries
                        (candidate.call.retry candidate.tries)
                        candidate loadedOp⟩) t
                      (.msg (Network.Who.proc "s3").addr (.written loadedOp)) =
                      Some.one (.node running, _) :=
                  Subtype.ext hservice
                rw [herase] at htake
                simp [Network.Conf.run, Network.Conf.state?, hstates,
                  hservice', Experiment.pick, Some.one] at htake
                obtain ⟨rfl, rfl, rfl⟩ := htake
                refine ⟨a, matches_hidden rfl, ?_⟩
                simpa [routedOuts, routedMessages, List.append_assoc,
                  sends_notes] using hrel'
              | writingLost happ hnext hn hv => simp at hw
              | writingShed happ hnext hn hv hs => simp at hw
            | conflict op =>
              have hm : (from_, .proc "n2", CMsg.conflict op) ∈
                  protocolMessages c.net := by
                rw [hnet]
                simp [protocolMessages]
              have hw := protocol_to_node2_is_wire hstoreAddr hn1 hn2
                hprotocol hm
              cases hn2 with
              | idle happ hn => simp at hw
              | loadingGet happ hnext hn => simp [hstoreAddr] at hw
              | loadingGot happ hnext hn hc hs hd => simp at hw
              | loadingDone happ hnext hn hp hu hs hd => simp at hw
              | writingPut happ hnext hn hv hs => simp [hstoreAddr] at hw
              | @writingConflict candidate loadedOp next mailbox
                  happ hnext hn hvalid hs =>
                have hfrom := source_eq_s3_of_inbound_wire hstoreAddr hw
                subst from_
                simp only [hstoreAddr] at hprotocol
                have hmsg := congrArg (fun x : ConcreteMessage => x.2.2)
                  (Option.some.inj hw)
                injection hmsg with hop
                subst op
                cases htries : candidate.tries with
                | zero =>
                  obtain ⟨a', running, rest, wire, tokens,
                      hmatch, hrun, hrestart, hrel'⟩ :=
                    normalRel_node2_conflict_exhausted hstoreAddr hn1 happ hnext
                      hn htries hprotocol hcover hstore htime hstepTime (.proc "s3")
                      pre post hnet
                  have hservice := node_service_step_singleton hrun
                  have hservice' :
                      system.step cfg (.node ⟨next, mailbox,
                        writeK candidate.tries
                          (candidate.call.retry candidate.tries)
                          candidate loadedOp⟩) t
                        (.msg (Network.Who.proc "s3").addr (.conflict loadedOp)) =
                        Some.one (.node running, _) :=
                    Subtype.ext hservice
                  rw [herase] at htake
                  simp [Network.Conf.run, Network.Conf.state?, hstates,
                    hservice', Experiment.pick, Some.one] at htake
                  obtain ⟨rfl, rfl, rfl⟩ := htake
                  refine ⟨a', hmatch, ?_⟩
                  simpa [routedOuts, routedMessages, List.append_assoc,
                    sends_notes] using hrel'
                | succ k =>
                  obtain ⟨hrun, hrel'⟩ :=
                    normalRel_node2_conflict_retry hstoreAddr hn1 happ hnext hn
                      hvalid hs htries hprotocol hcover hstore htime
                      hstepTime (.proc "s3") pre post hnet
                  have hservice := node_service_step_singleton hrun
                  have hservice' :
                      system.step cfg (.node ⟨next, mailbox,
                        writeK candidate.tries
                          (candidate.call.retry candidate.tries)
                          candidate loadedOp⟩) t
                        (.msg (Network.Who.proc "s3").addr (.conflict loadedOp)) =
                        Some.one (.node _, _) :=
                    Subtype.ext hservice
                  rw [herase] at htake
                  simp [Network.Conf.run, Network.Conf.state?, hstates,
                    hservice', Experiment.pick, Some.one] at htake
                  obtain ⟨rfl, rfl, rfl⟩ := htake
                  refine ⟨a, matches_hidden rfl, ?_⟩
                  simpa [routedOuts, routedMessages, List.append_assoc,
                    sends_notes] using hrel'
              | writingServed happ hnext hn hv => simp at hw
              | writingLost happ hnext hn hv => simp at hw
              | writingShed happ hnext hn hv hs => simp at hw
            | failed op =>
              have hm : (from_, .proc "n2", CMsg.failed op) ∈
                  protocolMessages c.net := by
                rw [hnet]
                simp [protocolMessages]
              have hw := protocol_to_node2_is_wire hstoreAddr hn1 hn2
                hprotocol hm
              cases hn2 with
              | idle happ hn => simp at hw
              | loadingGet happ hnext hn => simp [hstoreAddr] at hw
              | loadingGot happ hnext hn hc hs hd => simp at hw
              | loadingDone happ hnext hn hp hu hs hd => simp at hw
              | writingPut happ hnext hn hv hs => simp [hstoreAddr] at hw
              | writingConflict happ hnext hn hv hs => simp at hw
              | writingServed happ hnext hn hv => simp at hw
              | @writingLost candidate loadedOp next mailbox
                  happ hnext hn hvalid =>
                have hfrom := source_eq_s3_of_inbound_wire hstoreAddr hw
                subst from_
                simp only [hstoreAddr] at hprotocol
                have hmsg := congrArg (fun x : ConcreteMessage => x.2.2)
                  (Option.some.inj hw)
                injection hmsg with hop
                subst op
                obtain ⟨running, rest, wire, tokens, hrun, hrestart, hrel'⟩ :=
                  normalRel_node2_failed hstoreAddr hn1 happ hnext hn
                    (Or.inr rfl) hprotocol hcover hstore htime hstepTime
                    (.proc "s3") pre post hnet
                have hservice := node_service_step_singleton hrun
                have hservice' :
                    system.step cfg (.node ⟨next, mailbox,
                      writeK candidate.tries
                        (candidate.call.retry candidate.tries)
                        candidate loadedOp⟩) t
                      (.msg (Network.Who.proc "s3").addr (.failed loadedOp)) =
                      Some.one (.node running, _) :=
                  Subtype.ext hservice
                rw [herase] at htake
                simp [Network.Conf.run, Network.Conf.state?, hstates,
                  hservice', Experiment.pick, Some.one] at htake
                obtain ⟨rfl, rfl, rfl⟩ := htake
                refine ⟨a, matches_hidden rfl, ?_⟩
                simpa [routedOuts, routedMessages, List.append_assoc,
                  sends_notes] using hrel'
              | @writingShed candidate loadedOp next mailbox
                  happ hnext hn hvalid hs =>
                have hfrom := source_eq_s3_of_inbound_wire hstoreAddr hw
                subst from_
                simp only [hstoreAddr] at hprotocol
                have hmsg := congrArg (fun x : ConcreteMessage => x.2.2)
                  (Option.some.inj hw)
                injection hmsg with hop
                subst op
                obtain ⟨running, rest, wire, tokens, hrun, hrestart, hrel'⟩ :=
                  normalRel_node2_failed hstoreAddr hn1 happ hnext hn
                    (Or.inl rfl) hprotocol hcover hstore htime hstepTime
                    (.proc "s3") pre post hnet
                have hservice := node_service_step_singleton hrun
                have hservice' :
                    system.step cfg (.node ⟨next, mailbox,
                      writeK candidate.tries
                        (candidate.call.retry candidate.tries)
                        candidate loadedOp⟩) t
                      (.msg (Network.Who.proc "s3").addr (.failed loadedOp)) =
                      Some.one (.node running, _) :=
                  Subtype.ext hservice
                rw [herase] at htake
                simp [Network.Conf.run, Network.Conf.state?, hstates,
                  hservice', Experiment.pick, Some.one] at htake
                obtain ⟨rfl, rfl, rfl⟩ := htake
                refine ⟨a, matches_hidden rfl, ?_⟩
                simpa [routedOuts, routedMessages, List.append_assoc,
                  sends_notes] using hrel'
          · by_cases hp3 : proc = "s3"
            · subst proc
              cases message with
              | app message =>
                have hrel0 : NormalRel cfg
                    ⟨c.net,
                      [("n1", .node node1), ("n2", .node node2),
                        ("s3", .store store)], c.now⟩ a :=
                  ⟨node1, node2, store, wire1, wire2, tokens1, tokens2,
                    rfl, hn1, hn2, hprotocol, hcover, hstore, htime⟩
                have hrel' :=
                  hrel0.storeApp from_ message hstepTime pre post hnet
                have hraw :
                    ((storeReceive from_.addr (.app message)).run cfg store).val =
                      [((), store, [])] := by
                  cases message <;> rfl
                have hservice := store_service_step_singleton
                  (now := t) hraw
                have hservice' :
                    system.step cfg (.store store) t
                      (.msg from_.addr (.app message)) =
                      Some.one (.store store, []) :=
                  Subtype.ext hservice
                rw [herase] at htake
                simp [Network.Conf.run, Network.Conf.state?, hstates,
                  hservice', Experiment.pick, Some.one] at htake
                obtain ⟨rfl, rfl, rfl⟩ := htake
                refine ⟨a, matches_hidden rfl, ?_⟩
                simpa [routedOuts, routedMessages, List.append_assoc,
                  sends_notes] using hrel'
              | get op key =>
                have hm : (from_, .proc "s3", CMsg.get op key) ∈
                    protocolMessages c.net := by
                  rw [hnet]
                  simp [protocolMessages]
                obtain ⟨source, dest, protocol, hproc⟩ :=
                  protocol_message_is_between_procs hn1 hn2 hprotocol hm
                cases hproc
                by_cases hs1 : source = "n1"
                · subst source
                  have hw := protocol_from_node1_to_store_is_wire
                    hstoreAddr hn1 hn2 hprotocol hm
                  cases hn1 with
                  | idle happ hn => simp at hw
                  | @loadingGet call tries loadedOp next mailbox
                      happ hnext hn =>
                    rw [hstoreAddr] at hw
                    simp only [hstoreAddr] at hprotocol
                    simp only [Option.some.injEq, Prod.mk.injEq,
                      Network.Who.proc.injEq, CMsg.get.injEq, true_and] at hw
                    obtain ⟨rfl, rfl⟩ := hw
                    let picked := pick
                      ((Experiment.dispatch call.req call.now).run
                        { cfg.app with unreliable := true }
                        { promises :=
                          (storeLookup store call.req.key).toList.map (·.1) }) 0
                    have hpick :
                        pick ((Experiment.dispatch call.req call.now).run
                          { cfg.app with unreliable := true }
                          { promises :=
                            (storeLookup store call.req.key).toList.map (·.1) }) 0 =
                          picked := rfl
                    obtain ⟨res, after, outs⟩ := picked
                    by_cases hunchanged : after =
                        { promises :=
                          (storeLookup store call.req.key).toList.map (·.1) }
                    · obtain ⟨a', hmatch, hrel'⟩ :=
                        normalRel_store_get_done_node1 hstoreAddr happ hnext hn
                          hpick hunchanged hn2 hprotocol hcover hstore htime
                          hstepTime pre post hnet rfl
                      have hraw := store_get_run cfg store "n1" loadedOp
                        call.req.key
                      have hservice := store_service_step_singleton
                        (now := t) hraw
                      have hservice' :
                          system.step cfg (.store store) t
                            (.msg (Network.Who.proc "n1").addr
                              (.get loadedOp call.req.key)) =
                            Some.one (.store store,
                              [.send "n1"
                                (.got loadedOp
                                  (storeLookup store call.req.key))]) :=
                        Subtype.ext hservice
                      rw [herase] at htake
                      simp [Network.Conf.run, Network.Conf.state?, hstates,
                        hservice', Experiment.pick, Some.one] at htake
                      obtain ⟨rfl, rfl, rfl⟩ := htake
                      refine ⟨a', hmatch, ?_⟩
                      simpa [routedOuts, routedMessages, List.append_assoc,
                        sends_notes] using hrel'
                    · obtain ⟨hrun, hrel'⟩ :=
                        normalRel_store_get_node1 hstoreAddr happ hnext hn hpick
                          hunchanged hn2 hprotocol hcover hstore htime hstepTime
                          pre post hnet
                      have hservice := store_service_step_singleton
                        (now := t) hrun
                      have hservice' :
                          system.step cfg (.store store) t
                            (.msg (Network.Who.proc "n1").addr
                              (.get loadedOp call.req.key)) =
                            Some.one (.store store,
                              [.send "n1"
                                (.got loadedOp
                                  (storeLookup store call.req.key))]) :=
                        Subtype.ext hservice
                      rw [herase] at htake
                      simp [Network.Conf.run, Network.Conf.state?, hstates,
                        hservice', Experiment.pick, Some.one] at htake
                      obtain ⟨rfl, rfl, rfl⟩ := htake
                      refine ⟨a, matches_hidden rfl, ?_⟩
                      simpa [routedOuts, routedMessages, List.append_assoc,
                        sends_notes] using hrel'
                  | loadingGot happ hnext hn hc hs hd => simp at hw
                  | loadingDone happ hnext hn hp hu hs hd => simp at hw
                  | writingPut happ hnext hn hv hs => simp at hw
                  | writingConflict happ hnext hn hv hs => simp at hw
                  | writingServed happ hnext hn hv => simp at hw
                  | writingLost happ hnext hn hv => simp at hw
                  | writingShed happ hnext hn hv hs => simp at hw
                · by_cases hs2 : source = "n2"
                  · subst source
                    have hw := protocol_from_node2_to_store_is_wire
                      hstoreAddr hn1 hn2 hprotocol hm
                    cases hn2 with
                    | idle happ hn => simp at hw
                    | @loadingGet call tries loadedOp next mailbox
                        happ hnext hn =>
                      rw [hstoreAddr] at hw
                      simp only [hstoreAddr] at hprotocol
                      simp only [Option.some.injEq, Prod.mk.injEq,
                        Network.Who.proc.injEq, CMsg.get.injEq, true_and] at hw
                      obtain ⟨rfl, rfl⟩ := hw
                      let picked := pick
                        ((Experiment.dispatch call.req call.now).run
                          { cfg.app with unreliable := true }
                          { promises :=
                            (storeLookup store call.req.key).toList.map (·.1) }) 0
                      have hpick :
                          pick ((Experiment.dispatch call.req call.now).run
                            { cfg.app with unreliable := true }
                            { promises :=
                              (storeLookup store call.req.key).toList.map (·.1) }) 0 =
                            picked := rfl
                      obtain ⟨res, after, outs⟩ := picked
                      by_cases hunchanged : after =
                          { promises :=
                            (storeLookup store call.req.key).toList.map (·.1) }
                      · obtain ⟨a', hmatch, hrel'⟩ :=
                          normalRel_store_get_done_node2 hstoreAddr hn1 happ hnext
                            hn hpick hunchanged hprotocol hcover hstore htime
                            hstepTime pre post hnet rfl
                        have hraw := store_get_run cfg store "n2" loadedOp
                          call.req.key
                        have hservice := store_service_step_singleton
                          (now := t) hraw
                        have hservice' :
                            system.step cfg (.store store) t
                              (.msg (Network.Who.proc "n2").addr
                                (.get loadedOp call.req.key)) =
                              Some.one (.store store,
                                [.send "n2"
                                  (.got loadedOp
                                    (storeLookup store call.req.key))]) :=
                          Subtype.ext hservice
                        rw [herase] at htake
                        simp [Network.Conf.run, Network.Conf.state?, hstates,
                          hservice', Experiment.pick, Some.one] at htake
                        obtain ⟨rfl, rfl, rfl⟩ := htake
                        refine ⟨a', hmatch, ?_⟩
                        simpa [routedOuts, routedMessages, List.append_assoc,
                          sends_notes] using hrel'
                      · obtain ⟨hrun, hrel'⟩ :=
                          normalRel_store_get_node2 hstoreAddr hn1 happ hnext hn
                            hpick hunchanged hprotocol hcover hstore htime
                            hstepTime pre post hnet
                        have hservice := store_service_step_singleton
                          (now := t) hrun
                        have hservice' :
                            system.step cfg (.store store) t
                              (.msg (Network.Who.proc "n2").addr
                                (.get loadedOp call.req.key)) =
                              Some.one (.store store,
                                [.send "n2"
                                  (.got loadedOp
                                    (storeLookup store call.req.key))]) :=
                          Subtype.ext hservice
                        rw [herase] at htake
                        simp [Network.Conf.run, Network.Conf.state?, hstates,
                          hservice', Experiment.pick, Some.one] at htake
                        obtain ⟨rfl, rfl, rfl⟩ := htake
                        refine ⟨a, matches_hidden rfl, ?_⟩
                        simpa [routedOuts, routedMessages, List.append_assoc,
                          sends_notes] using hrel'
                    | loadingGot happ hnext hn hc hs hd => simp at hw
                    | loadingDone happ hnext hn hp hu hs hd => simp at hw
                    | writingPut happ hnext hn hv hs => simp at hw
                    | writingConflict happ hnext hn hv hs => simp at hw
                    | writingServed happ hnext hn hv => simp at hw
                    | writingLost happ hnext hn hv => simp at hw
                    | writingShed happ hnext hn hv hs => simp at hw
                  · have hout := (hprotocol.mem_iff).1 hm
                    cases hn1 <;> cases hn2 <;>
                      simp [optionList, hstoreAddr, hs1, hs2] at hout
              | put op key promise ifMatch =>
                have hm : (from_, .proc "s3",
                    CMsg.put op key promise ifMatch) ∈
                    protocolMessages c.net := by
                  rw [hnet]
                  simp [protocolMessages]
                obtain ⟨source, dest, protocol, hproc⟩ :=
                  protocol_message_is_between_procs hn1 hn2 hprotocol hm
                cases hproc
                by_cases hs1 : source = "n1"
                · subst source
                  have hw := protocol_from_node1_to_store_is_wire
                    hstoreAddr hn1 hn2 hprotocol hm
                  cases hn1 with
                  | idle happ hn => simp at hw
                  | loadingGet happ hnext hn => simp at hw
                  | loadingGot happ hnext hn hc hs hd => simp at hw
                  | loadingDone happ hnext hn hp hu hs hd => simp at hw
                  | @writingPut candidate loadedOp next mailbox
                      happ hnext hn hvalid hs =>
                    rw [hstoreAddr] at hw
                    simp only [hstoreAddr] at hprotocol
                    simp only [Option.some.injEq, Prod.mk.injEq,
                      Network.Who.proc.injEq, CMsg.put.injEq, true_and] at hw
                    obtain ⟨rfl, rfl, rfl, rfl⟩ := hw
                    let chosen := pick
                      ((storeReceive "n1"
                        (.put loadedOp candidate.req.key candidate.promise
                          (candidate.doc.map (·.2)))).run cfg store) choice
                    have hchosen :
                        pick ((storeReceive "n1"
                          (.put loadedOp candidate.req.key candidate.promise
                            (candidate.doc.map (·.2)))).run cfg store) choice =
                          chosen := rfl
                    obtain ⟨unit, afterStore, emitted⟩ := chosen
                    cases unit
                    have hout :
                        ((), afterStore, emitted) ∈
                          ((storeReceive "n1"
                            (.put loadedOp candidate.req.key candidate.promise
                              (candidate.doc.map (·.2)))).run cfg store).val := by
                      rw [← hchosen]
                      exact pick_mem _ _
                    have hservicePick :
                        pick (system.step cfg (.store store) t
                          (.msg (Network.Who.proc "n1").addr
                            (.put loadedOp candidate.req.key candidate.promise
                              (candidate.doc.map (·.2))))) choice =
                          (Local.store afterStore, emitted) := by
                      exact store_service_step_pick (now := t) hchosen
                    cases store_put_classify hconditional hout with
                    | conflict =>
                      have hrel' :=
                        normalRel_store_conflict_node1 hstoreAddr happ hnext hn
                          hvalid hs hn2 hprotocol hcover hstore htime hstepTime
                          pre post hnet
                      rw [herase] at htake
                      simp [Network.Conf.run, Network.Conf.state?, hstates,
                        hservicePick, Network.Conf.route, Network.Conf.isProc]
                        at htake
                      obtain ⟨rfl, rfl, rfl⟩ := htake
                      refine ⟨a, matches_hidden rfl, ?_⟩
                      simpa [List.append_assoc] using hrel'
                    | written hmatch =>
                      obtain ⟨a', hmatchAbstract, hrel'⟩ :=
                        normalRel_store_written_node1 hstoreAddr happ hnext hn
                          hvalid hs hmatch hn2 hprotocol hcover hstore htime
                          hstepTime pre post hnet
                      rw [herase] at htake
                      simp [Network.Conf.run, Network.Conf.state?, hstates,
                        hservicePick, Network.Conf.route, Network.Conf.isProc]
                        at htake
                      obtain ⟨rfl, rfl, rfl⟩ := htake
                      refine ⟨a', hmatchAbstract, ?_⟩
                      simpa [List.append_assoc] using hrel'
                    | landedFailed hmatch =>
                      obtain ⟨a', hmatchAbstract, hrel'⟩ :=
                        normalRel_store_landedFailed_node1 hstoreAddr happ hnext
                          hn hvalid hs hmatch hn2 hprotocol hcover hstore htime
                          hstepTime pre post hnet
                      rw [herase] at htake
                      simp [Network.Conf.run, Network.Conf.state?, hstates,
                        hservicePick, Network.Conf.route, Network.Conf.isProc]
                        at htake
                      obtain ⟨rfl, rfl, rfl⟩ := htake
                      refine ⟨a', hmatchAbstract, ?_⟩
                      simpa [List.append_assoc] using hrel'
                    | failed =>
                      obtain ⟨a', hmatchAbstract, hrel'⟩ :=
                        normalRel_store_failed_node1 hstoreAddr happ hnext hn
                          hvalid hs hn2 hprotocol hcover hstore htime hstepTime
                          pre post hnet
                      rw [herase] at htake
                      simp [Network.Conf.run, Network.Conf.state?, hstates,
                        hservicePick, Network.Conf.route, Network.Conf.isProc]
                        at htake
                      obtain ⟨rfl, rfl, rfl⟩ := htake
                      refine ⟨a', hmatchAbstract, ?_⟩
                      simpa [List.append_assoc] using hrel'
                  | writingConflict happ hnext hn hv hs => simp at hw
                  | writingServed happ hnext hn hv => simp at hw
                  | writingLost happ hnext hn hv => simp at hw
                  | writingShed happ hnext hn hv hs => simp at hw
                · by_cases hs2 : source = "n2"
                  · subst source
                    have hw := protocol_from_node2_to_store_is_wire
                      hstoreAddr hn1 hn2 hprotocol hm
                    cases hn2 with
                    | idle happ hn => simp at hw
                    | loadingGet happ hnext hn => simp at hw
                    | loadingGot happ hnext hn hc hs hd => simp at hw
                    | loadingDone happ hnext hn hp hu hs hd => simp at hw
                    | @writingPut candidate loadedOp next mailbox
                        happ hnext hn hvalid hs =>
                      rw [hstoreAddr] at hw
                      simp only [hstoreAddr] at hprotocol
                      simp only [Option.some.injEq, Prod.mk.injEq,
                        Network.Who.proc.injEq, CMsg.put.injEq, true_and] at hw
                      obtain ⟨rfl, rfl, rfl, rfl⟩ := hw
                      let chosen := pick
                        ((storeReceive "n2"
                          (.put loadedOp candidate.req.key candidate.promise
                            (candidate.doc.map (·.2)))).run cfg store) choice
                      have hchosen :
                          pick ((storeReceive "n2"
                            (.put loadedOp candidate.req.key candidate.promise
                              (candidate.doc.map (·.2)))).run cfg store) choice =
                            chosen := rfl
                      obtain ⟨unit, afterStore, emitted⟩ := chosen
                      cases unit
                      have hout :
                          ((), afterStore, emitted) ∈
                            ((storeReceive "n2"
                              (.put loadedOp candidate.req.key candidate.promise
                                (candidate.doc.map (·.2)))).run cfg store).val := by
                        rw [← hchosen]
                        exact pick_mem _ _
                      have hservicePick :
                          pick (system.step cfg (.store store) t
                            (.msg (Network.Who.proc "n2").addr
                              (.put loadedOp candidate.req.key candidate.promise
                                (candidate.doc.map (·.2))))) choice =
                            (Local.store afterStore, emitted) := by
                        exact store_service_step_pick (now := t) hchosen
                      cases store_put_classify hconditional hout with
                      | conflict =>
                        have hrel' :=
                          normalRel_store_conflict_node2 hstoreAddr hn1 happ
                            hnext hn hvalid hs hprotocol hcover hstore htime
                            hstepTime pre post hnet
                        rw [herase] at htake
                        simp [Network.Conf.run, Network.Conf.state?, hstates,
                          hservicePick, Network.Conf.route, Network.Conf.isProc]
                          at htake
                        obtain ⟨rfl, rfl, rfl⟩ := htake
                        refine ⟨a, matches_hidden rfl, ?_⟩
                        simpa [List.append_assoc] using hrel'
                      | written hmatch =>
                        obtain ⟨a', hmatchAbstract, hrel'⟩ :=
                          normalRel_store_written_node2 hstoreAddr happ
                            hnext hn hvalid hs hmatch hn1 hprotocol hcover hstore
                            htime hstepTime pre post hnet
                        rw [herase] at htake
                        simp [Network.Conf.run, Network.Conf.state?, hstates,
                          hservicePick, Network.Conf.route, Network.Conf.isProc]
                          at htake
                        obtain ⟨rfl, rfl, rfl⟩ := htake
                        refine ⟨a', hmatchAbstract, ?_⟩
                        simpa [List.append_assoc] using hrel'
                      | landedFailed hmatch =>
                        obtain ⟨a', hmatchAbstract, hrel'⟩ :=
                          normalRel_store_landedFailed_node2 hstoreAddr happ
                            hnext hn hvalid hs hmatch hn1 hprotocol hcover hstore
                            htime hstepTime pre post hnet
                        rw [herase] at htake
                        simp [Network.Conf.run, Network.Conf.state?, hstates,
                          hservicePick, Network.Conf.route, Network.Conf.isProc]
                          at htake
                        obtain ⟨rfl, rfl, rfl⟩ := htake
                        refine ⟨a', hmatchAbstract, ?_⟩
                        simpa [List.append_assoc] using hrel'
                      | failed =>
                        obtain ⟨a', hmatchAbstract, hrel'⟩ :=
                          normalRel_store_failed_node2 hstoreAddr happ hnext
                            hn hvalid hs hn1 hprotocol hcover hstore htime hstepTime
                            pre post hnet
                        rw [herase] at htake
                        simp [Network.Conf.run, Network.Conf.state?, hstates,
                          hservicePick, Network.Conf.route, Network.Conf.isProc]
                          at htake
                        obtain ⟨rfl, rfl, rfl⟩ := htake
                        refine ⟨a', hmatchAbstract, ?_⟩
                        simpa [List.append_assoc] using hrel'
                    | writingConflict happ hnext hn hv hs => simp at hw
                    | writingServed happ hnext hn hv => simp at hw
                    | writingLost happ hnext hn hv => simp at hw
                    | writingShed happ hnext hn hv hs => simp at hw
                  · have hout := (hprotocol.mem_iff).1 hm
                    cases hn1 <;> cases hn2 <;>
                      simp [optionList, hstoreAddr, hs1, hs2] at hout
              | got op doc =>
                have hm : (from_, .proc "s3", CMsg.got op doc) ∈
                    protocolMessages c.net := by
                  rw [hnet]
                  simp [protocolMessages]
                have hout := (hprotocol.mem_iff).1 hm
                cases hn1 <;> cases hn2 <;>
                  simp [optionList, hstoreAddr] at hout
              | written op =>
                have hm : (from_, .proc "s3", CMsg.written op) ∈
                    protocolMessages c.net := by
                  rw [hnet]
                  simp [protocolMessages]
                have hout := (hprotocol.mem_iff).1 hm
                cases hn1 <;> cases hn2 <;>
                  simp [optionList, hstoreAddr] at hout
              | conflict op =>
                have hm : (from_, .proc "s3", CMsg.conflict op) ∈
                    protocolMessages c.net := by
                  rw [hnet]
                  simp [protocolMessages]
                have hout := (hprotocol.mem_iff).1 hm
                cases hn1 <;> cases hn2 <;>
                  simp [optionList, hstoreAddr] at hout
              | failed op =>
                have hm : (from_, .proc "s3", CMsg.failed op) ∈
                    protocolMessages c.net := by
                  rw [hnet]
                  simp [protocolMessages]
                have hout := (hprotocol.mem_iff).1 hm
                cases hn1 <;> cases hn2 <;>
                  simp [optionList, hstoreAddr] at hout
            · have hp1' : "n1" ≠ proc := fun h => hp1 h.symm
              have hp2' : "n2" ≠ proc := fun h => hp2 h.symm
              have hp3' : "s3" ≠ proc := fun h => hp3 h.symm
              simp [Network.Conf.run, Network.Conf.state?, hstates,
                hp1', hp2', hp3'] at htake
  | tick address choice =>
    simp only [Network.Conf.take] at htake
    split at htake
    next hstepTime =>
      obtain ⟨node1, node2, store, wire1, wire2, tokens1, tokens2,
        hstates, hn1, hn2, hprotocol, hcover, hstore, htime⟩ := hrel
      have hrel' : NormalRel cfg
          ⟨c.net,
            [("n1", .node node1), ("n2", .node node2), ("s3", .store store)],
            t⟩ a :=
        ⟨node1, node2, store, wire1, wire2, tokens1, tokens2,
          rfl, hn1, hn2, hprotocol, hcover, hstore,
          Nat.le_trans htime hstepTime⟩
      by_cases hp1 : address = "n1"
      · subst address
        have hservice :
            system.step cfg (.node node1) t .tick =
              Some.one (.node node1, []) := by rfl
        simp [Network.Conf.run, Network.Conf.state?, hstates, hservice,
          Experiment.pick, Some.one] at htake
        obtain ⟨rfl, rfl, rfl⟩ := htake
        exact ⟨a, matches_hidden rfl, hrel'⟩
      · by_cases hp2 : address = "n2"
        · subst address
          have hservice :
              system.step cfg (.node node2) t .tick =
                Some.one (.node node2, []) := by rfl
          simp [Network.Conf.run, Network.Conf.state?, hstates, hservice,
            Experiment.pick, Some.one] at htake
          obtain ⟨rfl, rfl, rfl⟩ := htake
          exact ⟨a, matches_hidden rfl, hrel'⟩
        · by_cases hp3 : address = "s3"
          · subst address
            have hservice :
                system.step cfg (.store store) t .tick =
                  Some.one (.store store, []) := by rfl
            simp [Network.Conf.run, Network.Conf.state?, hstates, hservice,
              Experiment.pick, Some.one] at htake
            obtain ⟨rfl, rfl, rfl⟩ := htake
            exact ⟨a, matches_hidden rfl, hrel'⟩
          · have hp1' : "n1" ≠ address := fun h => hp1 h.symm
            have hp2' : "n2" ≠ address := fun h => hp2 h.symm
            have hp3' : "s3" ≠ address := fun h => hp3 h.symm
            simp [Network.Conf.run, Network.Conf.state?, hstates,
              hp1', hp2', hp3'] at htake
    next => contradiction

def RequestOnlyMsg : CMsg → Prop
  | .app _ | .get _ _ => True
  | _ => False

def RequestOnlyMailbox (mailbox : List (Addr × CMsg)) : Prop :=
  ∀ sender message, (sender, message) ∈ mailbox → RequestOnlyMsg message

theorem RequestOnlyMailbox.append {mailbox : List (Addr × CMsg)}
    (h : RequestOnlyMailbox mailbox) (sender : Addr) (message : CMsg)
    (hm : RequestOnlyMsg message) :
    RequestOnlyMailbox (mailbox ++ [(sender, message)]) := by
  intro a m hmem
  rw [List.mem_append] at hmem
  rcases hmem with hmem | hmem
  · exact h a m hmem
  · simp only [List.mem_singleton, Prod.mk.injEq] at hmem
    obtain ⟨rfl, rfl⟩ := hmem
    exact hm

theorem RequestOnlyMailbox.answers_none (h : RequestOnlyMailbox mailbox)
    (op : Nat) : take? (answers op) mailbox = none := by
  induction mailbox with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨sender, message⟩ := entry
    have hm := h sender message List.mem_cons_self
    have hrest : RequestOnlyMailbox rest :=
      fun a m hmem => h a m (List.mem_cons_of_mem _ hmem)
    cases message with
    | app message =>
      simp only [take?, answers, Bool.false_eq_true, if_false]
      simp [ih hrest]
    | get op key =>
      simp only [take?, answers, Bool.false_eq_true, if_false]
      simp [ih hrest]
    | put op key promise ifMatch => contradiction
    | got op doc => contradiction
    | written op => contradiction
    | conflict op => contradiction
    | failed op => contradiction

theorem RequestOnlyMailbox.rest_of_take {mailbox rest : List (Addr × CMsg)}
    {sender : Addr} {message : CMsg}
    (h : RequestOnlyMailbox mailbox)
    (htake : take? isRequest mailbox = some (sender, message, rest)) :
    RequestOnlyMailbox rest := by
  induction mailbox generalizing rest with
  | nil => simp [take?] at htake
  | cons entry tail ih =>
    obtain ⟨a, m⟩ := entry
    by_cases ha : isRequest a m = true
    · simp only [take?, ha, if_true, Option.some.injEq, Prod.mk.injEq] at htake
      obtain ⟨rfl, rfl, rfl⟩ := htake
      exact fun b q hq => h b q (List.mem_cons_of_mem _ hq)
    · have haf : isRequest a m = false := by
        simpa only [Bool.not_eq_true] using ha
      simp only [take?, haf, Bool.false_eq_true, if_false] at htake
      obtain ⟨found, hfound, heq⟩ := Option.map_eq_some_iff.mp htake
      obtain ⟨b, q, tail'⟩ := found
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      intro c x hx
      simp only [List.mem_cons] at hx
      rcases hx with hx | hx
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hx
        exact h _ _ List.mem_cons_self
      · exact ih
          (fun c x hx => h c x (List.mem_cons_of_mem _ hx)) hfound c x hx

theorem idle_requestOnly_request_run {cfg : Storage.Config}
    {mailbox : List (Addr × CMsg)}
    (hmail : RequestOnlyMailbox mailbox)
    (hn : take? isRequest mailbox = none)
    (next : Nat) (client : Addr) (id : CallId)
    (requestNow stepNow : Time) (request : Request) :
    (toStep node 64 client (.app (.req id requestNow request)) stepNow cfg
      (⟨next, mailbox, node⟩ : Running Storage.Config Nat CMsg)).val =
    [((), ⟨next + 1, mailbox,
      loadK cfg.retries
        (Call.retry ⟨client, id, request, requestNow⟩ cfg.retries)
        client id request requestNow next⟩,
      [.send cfg.store (.get next request.key)])] := by
  have ha : advance node cfg stepNow 64 next
      (mailbox ++ [(client, .app (.req id requestNow request))]) node =
      [(⟨next + 1, mailbox,
        loadK cfg.retries
          (Call.retry ⟨client, id, request, requestNow⟩ cfg.retries)
          client id request requestNow next⟩,
        [.send cfg.store (.get next request.key)])] := by
    change advance node cfg stepNow (63 + 1) next
      (mailbox ++ [(client, .app (.req id requestNow request))])
      (.receive isRequest _) = _
    rw [advance.eq_def]
    simp only
    rw [take?_append_match hn rfl]
    simp only [Proc.bind]
    change advance node cfg stepNow (62 + 1) next mailbox
      (.ask fun cfg' => serve client id request requestNow cfg'.retries) = _
    rw [advance_ask, serve.eq_1]
    exact advance_startK 57 (hmail.answers_none next)
  simp [toStep, ha, someOr]

theorem idle_requestOnly_miss_run {cfg : Storage.Config}
    {mailbox : List (Addr × CMsg)} {next : Nat}
    (hn : take? isRequest mailbox = none)
    (sender : Addr) (message : CMsg) (now : Time)
    (hm : isRequest sender message = false) :
    (toStep node 64 sender message now cfg
      (⟨next, mailbox, node⟩ : Running Storage.Config Nat CMsg)).val =
    [((), ⟨next, mailbox ++ [(sender, message)], node⟩, [])] := by
  have hnone : take? isRequest (mailbox ++ [(sender, message)]) = none :=
    take?_append_miss hn hm
  have ha : advance node cfg now 64 next
      (mailbox ++ [(sender, message)]) node =
      [(⟨next, mailbox ++ [(sender, message)], node⟩, [])] := by
    change advance node cfg now (63 + 1) next
      (mailbox ++ [(sender, message)]) (.receive isRequest _) = _
    exact advance_receive_none _ _ _ 63 _ _ _ _ hnone
  simp [toStep, ha, someOr]

theorem loading_requestOnly_run {cfg : Storage.Config}
    {mailbox : List (Addr × CMsg)} {call : Call} {tries op next : Nat}
    (hn : take? (answers op) mailbox = none)
    (sender : Addr) (message : CMsg) (now : Time)
    (hm : answers op sender message = false) :
    (toStep node 64 sender message now cfg
      (⟨next, mailbox,
        loadK tries (call.retry tries)
          call.client call.id call.req call.now op⟩ :
        Running Storage.Config Nat CMsg)).val =
    [((), ⟨next, mailbox ++ [(sender, message)],
      loadK tries (call.retry tries)
        call.client call.id call.req call.now op⟩, [])] := by
  have hnone : take? (answers op) (mailbox ++ [(sender, message)]) = none :=
    take?_append_miss hn hm
  have ha : advance node cfg now 64 next
      (mailbox ++ [(sender, message)])
      (loadK tries (call.retry tries)
        call.client call.id call.req call.now op) =
      [(⟨next, mailbox ++ [(sender, message)],
        loadK tries (call.retry tries)
          call.client call.id call.req call.now op⟩, [])] := by
    unfold loadK Proc.recv
    change advance node cfg now (63 + 1) next
      (mailbox ++ [(sender, message)]) (.receive (answers op) _) = _
    exact advance_receive_none _ _ _ 63 _ _ _ _ hnone
  simp [toStep, ha, someOr]

inductive RequestNode (cfg : Storage.Config) :
    Running Storage.Config Nat CMsg → Prop where
  | idle {next mailbox} :
      RequestOnlyMailbox mailbox →
      take? isRequest mailbox = none →
      RequestNode cfg ⟨next, mailbox, node⟩
  | loading {call : Call} {tries op next mailbox} :
      RequestOnlyMailbox mailbox →
      next = op + 1 →
      take? (answers op) mailbox = none →
      RequestNode cfg
        ⟨next, mailbox,
          loadK tries (call.retry tries)
            call.client call.id call.req call.now op⟩

theorem RequestNode.receive {cfg : Storage.Config}
    {running : Running Storage.Config Nat CMsg}
    (hnode : RequestNode cfg running)
    (sender : Addr) (message : CMsg) (now : Time)
    (hm : RequestOnlyMsg message) :
    ∃ running' outs,
      (toStep node 64 sender message now cfg running).val =
        [((), running', outs)] ∧
      RequestNode cfg running' ∧
      (outs = [] ∨ ∃ op key, outs = [.send cfg.store (.get op key)]) := by
  cases hnode with
  | @idle next mailbox hmail hn =>
    cases message with
    | app message =>
      cases message with
      | req id requestNow request =>
        let call : Call := ⟨sender, id, request, requestNow⟩
        refine ⟨_, [.send cfg.store (.get next request.key)],
          idle_requestOnly_request_run hmail hn next sender id requestNow now
            request, ?_, Or.inr ⟨next, request.key, rfl⟩⟩
        exact .loading (call := call) (tries := cfg.retries)
          hmail rfl (hmail.answers_none next)
      | res id response =>
        refine ⟨_, [], idle_requestOnly_miss_run hn sender
          (.app (.res id response)) now rfl, ?_, Or.inl rfl⟩
        exact .idle
          (hmail.append sender (.app (.res id response)) trivial)
          (take?_append_miss hn rfl)
      | notify promise =>
        refine ⟨_, [], idle_requestOnly_miss_run hn sender
          (.app (.notify promise)) now rfl, ?_, Or.inl rfl⟩
        exact .idle
          (hmail.append sender (.app (.notify promise)) trivial)
          (take?_append_miss hn rfl)
    | get op key =>
      refine ⟨_, [], idle_requestOnly_miss_run hn sender (.get op key) now rfl,
        ?_, Or.inl rfl⟩
      exact .idle (hmail.append sender (.get op key) trivial)
        (take?_append_miss hn rfl)
    | put op key promise ifMatch => contradiction
    | got op doc => contradiction
    | written op => contradiction
    | conflict op => contradiction
    | failed op => contradiction
  | @loading call tries op next mailbox hmail hnext hn =>
    refine ⟨_, [], loading_requestOnly_run hn sender message now ?_, ?_, Or.inl rfl⟩
    · cases message <;> simp_all [RequestOnlyMsg, answers]
    · exact .loading (hmail.append sender message hm) hnext
        (take?_append_miss hn (by
          cases message <;> simp_all [RequestOnlyMsg, answers]))

def requestRoute (cfg : Storage.Config) : Network.Who :=
  (⟨[], world, 0⟩ : Network.Conf system).route cfg.store

def RequestNet (cfg : Storage.Config) (net : List ConcreteMessage) : Prop :=
  ∀ source destination message, (source, destination, message) ∈ net →
    match message with
    | .app _ => ∃ address, destination = .proc address
    | .get _ _ =>
        (source = .proc "n1" ∨ source = .proc "n2") ∧
          destination = requestRoute cfg
    | _ => False

theorem request_route_eq {cfg : Storage.Config}
    (node1 node2 : Running Storage.Config Nat CMsg) (store : Store) :
    (⟨[], [("n1", .node node1), ("n2", .node node2), ("s3", .store store)], 0⟩ :
      Network.Conf system).route cfg.store = requestRoute cfg := by
  simp [requestRoute, world, Network.initial, Network.Conf.route,
    Network.Conf.isProc]

theorem request_route_ne_s3 {cfg : Storage.Config} (hstore : cfg.store ≠ "s3") :
    requestRoute cfg ≠ .proc "s3" := by
  intro heq
  by_cases hproc :
      "n1" = cfg.store ∨ "n2" = cfg.store ∨ "s3" = cfg.store
  · simp [requestRoute, world, Network.Conf.route, Network.Conf.isProc,
      hproc] at heq
    exact hstore heq
  · simp [requestRoute, world, Network.Conf.route, Network.Conf.isProc,
      hproc] at heq

theorem RequestNet.request {cfg : Storage.Config} {net : List ConcreteMessage}
    (h : RequestNet cfg net) (client : Addr) (to : Addr) (message : Msg) :
    RequestNet cfg
      (net ++ [(.client client, .proc to, CMsg.app message)]) := by
  intro source destination concreteMessage hm
  rw [List.mem_append] at hm
  rcases hm with hm | hm
  · exact h source destination concreteMessage hm
  · simp only [List.mem_singleton, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl, rfl⟩ := hm
    exact ⟨to, rfl⟩

theorem RequestNet.remove {cfg : Storage.Config} {net : List ConcreteMessage}
    (h : RequestNet cfg net) {message : ConcreteMessage}
    (pre post : List ConcreteMessage) (hnet : net = pre ++ message :: post) :
    RequestNet cfg (pre ++ post) := by
  intro source destination concreteMessage hm
  apply h source destination concreteMessage
  rw [hnet]
  simp only [List.mem_append, List.mem_cons]
  rcases List.mem_append.mp hm with hm | hm
  · exact Or.inl hm
  · exact Or.inr (Or.inr hm)

theorem RequestNet.emitGet {cfg : Storage.Config}
    {net : List ConcreteMessage} (h : RequestNet cfg net)
    (node1 node2 : Running Storage.Config Nat CMsg) (store : Store)
    (source : Addr) (hsource : source = "n1" ∨ source = "n2")
    (op : Nat) (key : Ident) :
    RequestNet cfg
      (net ++
        [(.proc source,
          (⟨[], [("n1", .node node1), ("n2", .node node2),
            ("s3", .store store)], 0⟩ : Network.Conf system).route cfg.store,
          .get op key)]) := by
  intro from_ destination message hm
  rw [List.mem_append] at hm
  rcases hm with hm | hm
  · exact h from_ destination message hm
  · simp only [List.mem_singleton, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl, rfl⟩ := hm
    exact ⟨by
      rcases hsource with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl,
      request_route_eq node1 node2 store⟩

def RequestOnlyRel (cfg : Storage.Config)
    (concrete : Network.Conf system) (abstract : Experiment.Conf promises) : Prop :=
  ∃ node1 node2 store,
    concrete.states =
      [("n1", .node node1), ("n2", .node node2), ("s3", .store store)] ∧
    RequestNode cfg node1 ∧
    RequestNode cfg node2 ∧
    RequestNet cfg concrete.net ∧
    abstract.state = {} ∧
    abstract.now ≤ concrete.now

theorem initial_requestOnlyRel (cfg : Storage.Config) :
    RequestOnlyRel cfg (Network.initial world) (Experiment.initial {}) := by
  refine ⟨⟨0, [], node⟩, ⟨0, [], node⟩, {}, rfl, ?_, ?_, ?_, rfl,
    Nat.le_refl 0⟩
  · exact .idle (by simp [RequestOnlyMailbox]) rfl
  · exact .idle (by simp [RequestOnlyMailbox]) rfl
  · intro source destination message hm
    simp [Network.initial] at hm

set_option maxHeartbeats 1000000 in
theorem storage_simulationOn_not_s3 {cfg : Storage.Config}
    (hstoreAddr : cfg.store ≠ "s3") :
    Network.SimulationOn cfg { cfg.app with unreliable := true }
      clientView DriveSafe (RequestOnlyRel cfg) := by
  intro c l stepOut c' a hrel hstep hok
  obtain ⟨t, act, htake⟩ := hstep
  cases act with
  | request client to message =>
    simp only [Network.Conf.take] at htake
    split at htake
    next hguard =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hguard
      have hstepTime : c.now ≤ t := hguard.1
      simp only [Option.some.injEq, Prod.mk.injEq] at htake
      obtain ⟨rfl, rfl, rfl⟩ := htake
      cases message with
      | app message =>
        obtain ⟨node1, node2, store, hstates, hn1, hn2,
          hnet, hstate, htime⟩ := hrel
        let a' : Experiment.Conf promises :=
          ⟨a.net ++ [(.client client, .server, message)], a.state, t⟩
        refine ⟨a', matches_client_request
          (Nat.le_trans htime hstepTime), ?_⟩
        exact ⟨node1, node2, store, hstates, hn1, hn2,
          hnet.request client to message, hstate, Nat.le_refl t⟩
      | get op key => simp [DriveSafe] at hok
      | put op key promise ifMatch => simp [DriveSafe] at hok
      | got op doc => simp [DriveSafe] at hok
      | written op => simp [DriveSafe] at hok
      | conflict op => simp [DriveSafe] at hok
      | failed op => simp [DriveSafe] at hok
    next => contradiction
  | deliver index choice =>
    simp only [Network.Conf.take] at htake
    split at htake <;> try contradiction
    next hstepTime =>
      split at htake <;> try contradiction
      next from_ client message hmessage =>
        simp only [Option.some.injEq, Prod.mk.injEq] at htake
        obtain ⟨rfl, rfl, rfl⟩ := htake
        obtain ⟨node1, node2, store, hstates, hn1, hn2,
          hsafe, hstate, htime⟩ := hrel
        obtain ⟨pre, post, hnet, herase⟩ :=
          split_of_get?_eq_some hmessage
        have hm : (from_, .client client, message) ∈ c.net := by
          rw [hnet]
          simp
        have hs := hsafe from_ (.client client) message hm
        cases message with
        | app message =>
          obtain ⟨address, hbad⟩ := hs
          cases hbad
        | get op key =>
          refine ⟨a, matches_hidden rfl, node1, node2, store, ?_,
            hn1, hn2, ?_, hstate,
            Nat.le_trans htime hstepTime⟩
          · simpa [herase] using hstates
          · simpa [herase] using hsafe.remove pre post hnet
        | put op key promise ifMatch => contradiction
        | got op doc => contradiction
        | written op => contradiction
        | conflict op => contradiction
        | failed op => contradiction
      next from_ proc message hmessage =>
        obtain ⟨node1, node2, store, hstates, hn1, hn2,
          hsafe, hstate, htime⟩ := hrel
        obtain ⟨pre, post, hnet, herase⟩ :=
          split_of_get?_eq_some hmessage
        have hm : (from_, .proc proc, message) ∈ c.net := by
          rw [hnet]
          simp
        have hs := hsafe from_ (.proc proc) message hm
        have hbase := hsafe.remove pre post hnet
        by_cases hp1 : proc = "n1"
        · subst proc
          have hmessageSafe : RequestOnlyMsg message := by
            cases message <;> simp_all [RequestOnlyMsg]
          obtain ⟨node1', outs, hrun, hn1', hout⟩ :=
            hn1.receive from_.addr message t hmessageSafe
          have hservice := node_service_step_singleton hrun
          have hservice' :
              system.step cfg (.node node1) t (.msg from_.addr message) =
                Some.one (.node node1', outs) :=
            Subtype.ext hservice
          rw [herase] at htake
          rcases hout with rfl | ⟨op, key, rfl⟩
          · simp [Network.Conf.run, Network.Conf.state?, hstates,
              hservice', Experiment.pick, Some.one] at htake
            obtain ⟨rfl, rfl, rfl⟩ := htake
            exact ⟨a, matches_hidden rfl, node1', node2, store, rfl,
              hn1', hn2, hbase, hstate, Nat.le_trans htime hstepTime⟩
          · simp [Network.Conf.run, Network.Conf.state?, hstates,
              hservice', Experiment.pick, Some.one] at htake
            obtain ⟨rfl, rfl, rfl⟩ := htake
            refine ⟨a, matches_hidden rfl, node1', node2, store, rfl,
              hn1', hn2, ?_, hstate, Nat.le_trans htime hstepTime⟩
            simpa [Network.Conf.route, Network.Conf.isProc] using
              hbase.emitGet node1' node2 store "n1" (Or.inl rfl) op key
        · by_cases hp2 : proc = "n2"
          · subst proc
            have hmessageSafe : RequestOnlyMsg message := by
              cases message <;> simp_all [RequestOnlyMsg]
            obtain ⟨node2', outs, hrun, hn2', hout⟩ :=
              hn2.receive from_.addr message t hmessageSafe
            have hservice := node_service_step_singleton hrun
            have hservice' :
                system.step cfg (.node node2) t (.msg from_.addr message) =
                  Some.one (.node node2', outs) :=
              Subtype.ext hservice
            rw [herase] at htake
            rcases hout with rfl | ⟨op, key, rfl⟩
            · simp [Network.Conf.run, Network.Conf.state?, hstates,
                hservice', Experiment.pick, Some.one] at htake
              obtain ⟨rfl, rfl, rfl⟩ := htake
              exact ⟨a, matches_hidden rfl, node1, node2', store, rfl,
                hn1, hn2', hbase, hstate, Nat.le_trans htime hstepTime⟩
            · simp [Network.Conf.run, Network.Conf.state?, hstates,
                hservice', Experiment.pick, Some.one] at htake
              obtain ⟨rfl, rfl, rfl⟩ := htake
              refine ⟨a, matches_hidden rfl, node1, node2', store, rfl,
                hn1, hn2', ?_, hstate, Nat.le_trans htime hstepTime⟩
              simpa [Network.Conf.route, Network.Conf.isProc] using
                hbase.emitGet node1 node2' store "n2" (Or.inr rfl) op key
          · by_cases hp3 : proc = "s3"
            · subst proc
              cases message with
              | app message =>
                have hraw :
                    ((storeReceive from_.addr (.app message)).run cfg store).val =
                      [((), store, [])] := by
                  cases message <;> rfl
                have hservice := store_service_step_singleton
                  (now := t) hraw
                have hservice' :
                    system.step cfg (.store store) t
                      (.msg from_.addr (.app message)) =
                      Some.one (.store store, []) :=
                  Subtype.ext hservice
                rw [herase] at htake
                simp [Network.Conf.run, Network.Conf.state?, hstates,
                  hservice', Experiment.pick, Some.one] at htake
                obtain ⟨rfl, rfl, rfl⟩ := htake
                exact ⟨a, matches_hidden rfl, node1, node2, store, rfl,
                  hn1, hn2, hbase, hstate, Nat.le_trans htime hstepTime⟩
              | get op key =>
                exact (request_route_ne_s3 hstoreAddr hs.2.symm).elim
              | put op key promise ifMatch => contradiction
              | got op doc => contradiction
              | written op => contradiction
              | conflict op => contradiction
              | failed op => contradiction
            · have hp1' : "n1" ≠ proc := fun h => hp1 h.symm
              have hp2' : "n2" ≠ proc := fun h => hp2 h.symm
              have hp3' : "s3" ≠ proc := fun h => hp3 h.symm
              simp [Network.Conf.run, Network.Conf.state?, hstates,
                hp1', hp2', hp3'] at htake
  | tick address choice =>
    simp only [Network.Conf.take] at htake
    split at htake
    next hstepTime =>
      obtain ⟨node1, node2, store, hstates, hn1, hn2,
        hsafe, hstate, htime⟩ := hrel
      by_cases hp1 : address = "n1"
      · subst address
        have hservice :
            system.step cfg (.node node1) t .tick =
              Some.one (.node node1, []) := by rfl
        simp [Network.Conf.run, Network.Conf.state?, hstates, hservice,
          Experiment.pick, Some.one] at htake
        obtain ⟨rfl, rfl, rfl⟩ := htake
        exact ⟨a, matches_hidden rfl, node1, node2, store, rfl,
          hn1, hn2, hsafe, hstate, Nat.le_trans htime hstepTime⟩
      · by_cases hp2 : address = "n2"
        · subst address
          have hservice :
              system.step cfg (.node node2) t .tick =
                Some.one (.node node2, []) := by rfl
          simp [Network.Conf.run, Network.Conf.state?, hstates, hservice,
            Experiment.pick, Some.one] at htake
          obtain ⟨rfl, rfl, rfl⟩ := htake
          exact ⟨a, matches_hidden rfl, node1, node2, store, rfl,
            hn1, hn2, hsafe, hstate, Nat.le_trans htime hstepTime⟩
        · by_cases hp3 : address = "s3"
          · subst address
            have hservice :
                system.step cfg (.store store) t .tick =
                  Some.one (.store store, []) := by rfl
            simp [Network.Conf.run, Network.Conf.state?, hstates, hservice,
              Experiment.pick, Some.one] at htake
            obtain ⟨rfl, rfl, rfl⟩ := htake
            exact ⟨a, matches_hidden rfl, node1, node2, store, rfl,
              hn1, hn2, hsafe, hstate, Nat.le_trans htime hstepTime⟩
          · have hp1' : "n1" ≠ address := fun h => hp1 h.symm
            have hp2' : "n2" ≠ address := fun h => hp2 h.symm
            have hp3' : "s3" ≠ address := fun h => hp3 h.symm
            simp [Network.Conf.run, Network.Conf.state?, hstates,
              hp1', hp2', hp3'] at htake
    next => contradiction

theorem system_refines (cfg : Storage.Config) : Refines cfg := by
  intro hconditional script execution hdrive
  by_cases hstoreAddr : cfg.store = "s3"
  · exact drive_refines_of_simulationOn
      (storage_simulationOn hconditional hstoreAddr)
      (initial_normalRel cfg) hdrive
  · exact drive_refines_of_simulationOn
      (storage_simulationOn_not_s3 hstoreAddr)
      (initial_requestOnlyRel cfg) hdrive

end Exp2
