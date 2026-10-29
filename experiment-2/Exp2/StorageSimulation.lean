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

theorem perm_cancel_middle {xs ys left right : List α} {value : α}
    (h : (xs ++ value :: ys).Perm (left ++ value :: right)) :
    (xs ++ ys).Perm (left ++ right) := by
  have hleft :
      (value :: xs ++ ys).Perm (value :: left ++ right) :=
    (perm_append_cons_head xs ys value).symm.trans
      (h.trans (perm_append_cons_head left right value))
  exact List.Perm.cons_inv hleft

theorem perm_append_insert_middle {xs before after added : List α}
    (h : xs.Perm (before ++ after)) :
    (xs ++ added).Perm (before ++ added ++ after) := by
  have happ := h.append_right added
  have hinsert :
      ((before ++ after) ++ added).Perm
        (before ++ added ++ after) := by
    simpa [List.append_assoc] using
      (List.Perm.append_left before
        (List.perm_append_comm :
          (after ++ added).Perm (added ++ after)))
  exact happ.trans hinsert

theorem perm_replace_middle_to_front
    {base before old after added new : List α}
    (h : old.Perm (added ++ new)) :
    (base ++ before ++ old ++ after).Perm
      (base ++ added ++ before ++ new ++ after) := by
  have hreplace :
      (base ++ before ++ old ++ after).Perm
        (base ++ before ++ (added ++ new) ++ after) := by
    simpa [List.append_assoc] using
      (List.Perm.append_right after
        (List.Perm.append_left (base ++ before) h))
  have hmove :
      (base ++ before ++ (added ++ new) ++ after).Perm
        (base ++ added ++ before ++ new ++ after) := by
    simpa [List.append_assoc] using
      (List.Perm.append_right (new ++ after)
        (List.Perm.append_left base
          (List.perm_append_comm :
            (before ++ added).Perm (added ++ before))))
  exact hreplace.trans hmove

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

theorem some_eq_one_of_val_eq {value : Some α} {item : α}
    (h : value.val = [item]) : value = Some.one item := by
  apply Subtype.eq
  exact h

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

/-- `NodeRep` witnesses aligned with an arbitrary list of server addresses.
The last two indices are the flattened concrete protocol wires and abstract
tokens contributed by the represented nodes. -/
inductive NodesRep (cfg : Storage.Config) (store : Store) :
    List Addr → List (Addr × Local) →
      List ConcreteMessage → List AbstractMessage → Prop where
  | nil : NodesRep cfg store [] [] [] []
  | cons {address : Addr} {addresses : List Addr}
      {running : Running Storage.Config Nat CMsg}
      {states : List (Addr × Local)}
      {wire : Option ConcreteMessage} {wires : List ConcreteMessage}
      {tokens nodeTokens : List AbstractMessage} :
      NodeRep cfg store address running wire nodeTokens →
      NodesRep cfg store addresses states wires tokens →
      NodesRep cfg store (address :: addresses)
        ((address, .node running) :: states)
        (optionList wire ++ wires) (nodeTokens ++ tokens)

theorem NodesRep.append {cfg : Storage.Config} {store : Store}
    {leftNodes rightNodes : List Addr}
    {leftStates rightStates : List (Addr × Local)}
    {leftWires rightWires : List ConcreteMessage}
    {leftTokens rightTokens : List AbstractMessage}
    (left : NodesRep cfg store leftNodes leftStates leftWires leftTokens)
    (right : NodesRep cfg store rightNodes rightStates rightWires rightTokens) :
    NodesRep cfg store (leftNodes ++ rightNodes) (leftStates ++ rightStates)
      (leftWires ++ rightWires) (leftTokens ++ rightTokens) := by
  induction left with
  | nil => exact right
  | cons hnode _ ih =>
    simpa [List.append_assoc] using NodesRep.cons hnode ih

/-- A member of an aligned node relation, with the represented prefix and
suffix retained so the member can be replaced after a local transition. -/
structure NodesRep.Focus (cfg : Storage.Config) (store : Store)
    (nodes : List Addr) (states : List (Addr × Local))
    (wires : List ConcreteMessage) (tokens : List AbstractMessage)
    (address : Addr) where
  beforeNodes : List Addr
  afterNodes : List Addr
  beforeStates : List (Addr × Local)
  afterStates : List (Addr × Local)
  beforeWires : List ConcreteMessage
  afterWires : List ConcreteMessage
  beforeTokens : List AbstractMessage
  afterTokens : List AbstractMessage
  running : Running Storage.Config Nat CMsg
  wire : Option ConcreteMessage
  nodeTokens : List AbstractMessage
  nodes_eq : nodes = beforeNodes ++ address :: afterNodes
  states_eq :
    states = beforeStates ++ (address, .node running) :: afterStates
  wires_eq :
    wires = beforeWires ++ optionList wire ++ afterWires
  tokens_eq :
    tokens = beforeTokens ++ nodeTokens ++ afterTokens
  before : NodesRep cfg store beforeNodes beforeStates beforeWires beforeTokens
  selected : NodeRep cfg store address running wire nodeTokens
  after : NodesRep cfg store afterNodes afterStates afterWires afterTokens

theorem NodesRep.exists_focus {cfg : Storage.Config} {store : Store}
    {nodes : List Addr} {states : List (Addr × Local)}
    {wires : List ConcreteMessage} {tokens : List AbstractMessage}
    (h : NodesRep cfg store nodes states wires tokens)
    {address : Addr} (hm : address ∈ nodes) :
    ∃ focus : NodesRep.Focus cfg store nodes states wires tokens address,
      True := by
  induction h with
  | nil => simp at hm
  | @cons head tail running tailStates wire tailWires
      tailTokens nodeTokens hhead htail ih =>
    simp only [List.mem_cons] at hm
    rcases hm with rfl | hm
    · refine ⟨{
        beforeNodes := []
        afterNodes := tail
        beforeStates := []
        afterStates := tailStates
        beforeWires := []
        afterWires := tailWires
        beforeTokens := []
        afterTokens := tailTokens
        running := running
        wire := wire
        nodeTokens := nodeTokens
        nodes_eq := rfl
        states_eq := rfl
        wires_eq := by simp
        tokens_eq := by simp
        before := .nil
        selected := hhead
        after := htail }, trivial⟩
    · obtain ⟨focused, _⟩ := ih hm
      refine ⟨{
        beforeNodes := head :: focused.beforeNodes
        afterNodes := focused.afterNodes
        beforeStates := (head, .node running) :: focused.beforeStates
        afterStates := focused.afterStates
        beforeWires := optionList wire ++ focused.beforeWires
        afterWires := focused.afterWires
        beforeTokens := nodeTokens ++ focused.beforeTokens
        afterTokens := focused.afterTokens
        running := focused.running
        wire := focused.wire
        nodeTokens := focused.nodeTokens
        nodes_eq := by simp [focused.nodes_eq]
        states_eq := by simp [focused.states_eq]
        wires_eq := by simp [focused.wires_eq, List.append_assoc]
        tokens_eq := by simp [focused.tokens_eq, List.append_assoc]
        before := .cons hhead focused.before
        selected := focused.selected
        after := focused.after }, trivial⟩

noncomputable def NodesRep.focus {cfg : Storage.Config} {store : Store}
    {nodes : List Addr} {states : List (Addr × Local)}
    {wires : List ConcreteMessage} {tokens : List AbstractMessage}
    (h : NodesRep cfg store nodes states wires tokens)
    {address : Addr} (hm : address ∈ nodes) :
    NodesRep.Focus cfg store nodes states wires tokens address :=
  (h.exists_focus hm).choose

theorem NodesRep.Focus.replace
    {cfg : Storage.Config} {store : Store}
    {nodes : List Addr} {states : List (Addr × Local)}
    {wires : List ConcreteMessage} {tokens : List AbstractMessage}
    {address : Addr}
    (focus : NodesRep.Focus cfg store nodes states wires tokens address)
    {running : Running Storage.Config Nat CMsg}
    {wire : Option ConcreteMessage} {nodeTokens : List AbstractMessage}
    (selected : NodeRep cfg store address running wire nodeTokens) :
    NodesRep cfg store nodes
      (focus.beforeStates ++ (address, .node running) :: focus.afterStates)
      (focus.beforeWires ++ optionList wire ++ focus.afterWires)
      (focus.beforeTokens ++ nodeTokens ++ focus.afterTokens) := by
  have hbuilt := focus.before.append (NodesRep.cons selected focus.after)
  simpa only [focus.nodes_eq, List.append_assoc] using hbuilt

theorem NodesRep.Focus.replaceRestart
    {cfg : Storage.Config} {store : Store}
    {nodes : List Addr} {states : List (Addr × Local)}
    {wires : List ConcreteMessage} {tokens : List AbstractMessage}
    {address : Addr}
    (focus : NodesRep.Focus cfg store nodes states wires tokens address)
    {running : Running Storage.Config Nat CMsg} {outs : List (Out CMsg)}
    {wire : Option ConcreteMessage} {nodeTokens : List AbstractMessage}
    (restart : RestartRep cfg store address running outs wire nodeTokens) :
    NodesRep cfg store nodes
      (focus.beforeStates ++ (address, .node running) :: focus.afterStates)
      (focus.beforeWires ++ optionList wire ++ focus.afterWires)
      (focus.beforeTokens ++ nodeTokens ++ focus.afterTokens) :=
  focus.replace restart.nodeRep

/-- The storage simulation invariant. Node states and their wire/token
contributions are represented recursively and flattened in address order. -/
def NormalRel (nodes : List Addr) (cfg : Storage.Config)
    (concrete : Network.Conf system) (abstract : Experiment.Conf promises) : Prop :=
  ∃ nodeStates store wires tokens,
    concrete.states = nodeStates ++ [("s3", .store store)] ∧
    NodesRep cfg store nodes nodeStates wires tokens ∧
    (protocolMessages concrete.net).Perm wires ∧
    Covers (appTokens concrete.net ++ tokens) abstract.net ∧
    StoreRep store abstract.state ∧
    abstract.now ≤ concrete.now

theorem NormalRel.time {nodes : List Addr} {cfg : Storage.Config}
    {concrete : Network.Conf system} {abstract : Experiment.Conf promises}
    (h : NormalRel nodes cfg concrete abstract) :
    abstract.now ≤ concrete.now := by
  obtain ⟨_, _, _, _, _, _, _, _, _, htime⟩ := h
  exact htime

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

theorem NodesRep.commit {cfg : Storage.Config} {store : Store}
    {nodes : List Addr} {states : List (Addr × Local)}
    {wires : List ConcreteMessage} {tokens : List AbstractMessage}
    {key : Ident} {promise : Promise}
    (h : NodesRep cfg store nodes states wires tokens) :
    NodesRep cfg (storeCommit store key promise) nodes states wires tokens := by
  induction h with
  | nil => exact .nil
  | cons hnode _ ih => exact .cons hnode.commit ih

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

theorem NodeRep.wire_endpoints {cfg : Storage.Config} {store : Store}
    {address : Addr} {running : Running Storage.Config Nat CMsg}
    {wire : Option ConcreteMessage} {tokens : List AbstractMessage}
    (h : NodeRep cfg store address running wire tokens)
    {message : ConcreteMessage} (hw : wire = some message) :
    (∃ m, message = (.proc address, .proc cfg.store, m)) ∨
    (∃ m, message = (.proc cfg.store, .proc address, m)) := by
  cases h with
  | idle => simp at hw
  | loadingGet =>
    simp only [Option.some.injEq] at hw
    subst message
    exact Or.inl ⟨_, rfl⟩
  | loadingGot =>
    simp only [Option.some.injEq] at hw
    subst message
    exact Or.inr ⟨_, rfl⟩
  | loadingDone =>
    simp only [Option.some.injEq] at hw
    subst message
    exact Or.inr ⟨_, rfl⟩
  | writingPut =>
    simp only [Option.some.injEq] at hw
    subst message
    exact Or.inl ⟨_, rfl⟩
  | writingConflict =>
    simp only [Option.some.injEq] at hw
    subst message
    exact Or.inr ⟨_, rfl⟩
  | writingServed =>
    simp only [Option.some.injEq] at hw
    subst message
    exact Or.inr ⟨_, rfl⟩
  | writingLost =>
    simp only [Option.some.injEq] at hw
    subst message
    exact Or.inr ⟨_, rfl⟩
  | writingShed =>
    simp only [Option.some.injEq] at hw
    subst message
    exact Or.inr ⟨_, rfl⟩

theorem NodesRep.no_wire_to {cfg : Storage.Config} {store : Store}
    {nodes : List Addr} {states : List (Addr × Local)}
    {wires : List ConcreteMessage} {tokens : List AbstractMessage}
    (h : NodesRep cfg store nodes states wires tokens)
    {address : Addr} (haddress : address ∉ nodes)
    (hstore : address ≠ cfg.store) {source : Network.Who} {message : CMsg} :
    (source, .proc address, message) ∉ wires := by
  induction h with
  | nil => simp
  | @cons head tail running tailStates wire tailWires
      tailTokens nodeTokens hnode htail ih =>
    have hhead : address ≠ head :=
      fun heq => haddress (by simp [heq])
    have htail : address ∉ tail :=
      fun hm => haddress (by simp [hm])
    intro hm
    simp only [List.mem_append] at hm
    rcases hm with hm | hm
    · have hw : wire = some (source, .proc address, message) := by
        cases wire <;> simp [optionList] at hm ⊢
        exact hm.symm
      rcases hnode.wire_endpoints hw with ⟨m, heq⟩ | ⟨m, heq⟩
      · simp only [Prod.mk.injEq, Network.Who.proc.injEq] at heq
        exact hstore heq.2.1
      · simp only [Prod.mk.injEq, Network.Who.proc.injEq] at heq
        exact hhead heq.2.1
    · exact ih htail hm

theorem NodesRep.no_wire_from {cfg : Storage.Config} {store : Store}
    {nodes : List Addr} {states : List (Addr × Local)}
    {wires : List ConcreteMessage} {tokens : List AbstractMessage}
    (h : NodesRep cfg store nodes states wires tokens)
    {address : Addr} (haddress : address ∉ nodes)
    (hstore : address ≠ cfg.store) {dest : Network.Who} {message : CMsg} :
    (.proc address, dest, message) ∉ wires := by
  induction h with
  | nil => simp
  | @cons head tail running tailStates wire tailWires
      tailTokens nodeTokens hnode htail ih =>
    have hhead : address ≠ head :=
      fun heq => haddress (by simp [heq])
    have htail : address ∉ tail :=
      fun hm => haddress (by simp [hm])
    intro hm
    simp only [List.mem_append] at hm
    rcases hm with hm | hm
    · have hw : wire = some (.proc address, dest, message) := by
        cases wire <;> simp [optionList] at hm ⊢
        exact hm.symm
      rcases hnode.wire_endpoints hw with ⟨m, heq⟩ | ⟨m, heq⟩
      · simp only [Prod.mk.injEq, Network.Who.proc.injEq] at heq
        exact hhead heq.1
      · simp only [Prod.mk.injEq, Network.Who.proc.injEq] at heq
        exact hstore heq.1
    · exact ih htail hm

theorem NodesRep.outbound_source_mem {cfg : Storage.Config} {store : Store}
    {nodes : List Addr} {states : List (Addr × Local)}
    {wires : List ConcreteMessage} {tokens : List AbstractMessage}
    (h : NodesRep cfg store nodes states wires tokens)
    (hphysical : cfg.store ∉ nodes)
    {source : Addr} {message : CMsg}
    (hm : (.proc source, .proc cfg.store, message) ∈ wires) :
    source ∈ nodes := by
  induction h with
  | nil => simp at hm
  | @cons head tail running tailStates wire tailWires
      tailTokens nodeTokens hnode htail ih =>
    simp only [List.mem_append] at hm
    rcases hm with hm | hm
    · have hw : wire =
          some (.proc source, .proc cfg.store, message) := by
        cases wire <;> simp [optionList] at hm ⊢
        exact hm.symm
      rcases hnode.wire_endpoints hw with ⟨m, heq⟩ | ⟨m, heq⟩
      · simp only [Prod.mk.injEq, Network.Who.proc.injEq] at heq
        simp [heq.1]
      · simp only [Prod.mk.injEq, Network.Who.proc.injEq] at heq
        have hhead : head = cfg.store := heq.2.1.symm
        exact (hphysical (by simp [hhead])).elim
    · have htailPhysical : cfg.store ∉ tail :=
        fun hmem => hphysical (by simp [hmem])
      exact List.mem_cons_of_mem _ (ih htailPhysical hm)

def StoreRequest : CMsg → Prop
  | .get _ _ | .put _ _ _ _ => True
  | _ => False

theorem NodesRep.wire_to_store_is_request
    {cfg : Storage.Config} {store : Store}
    {nodes : List Addr} {states : List (Addr × Local)}
    {wires : List ConcreteMessage} {tokens : List AbstractMessage}
    (h : NodesRep cfg store nodes states wires tokens)
    (hstoreAddr : cfg.store = "s3")
    (hphysical : "s3" ∉ nodes)
    {source : Network.Who} {message : CMsg}
    (hm : (source, .proc "s3", message) ∈ wires) :
    StoreRequest message := by
  induction h with
  | nil => simp at hm
  | @cons head tail running tailStates wire tailWires
      tailTokens nodeTokens hnode htail ih =>
    have hhead : head ≠ "s3" := by
      intro heq
      exact hphysical (by simp [heq])
    have htailPhysical : "s3" ∉ tail :=
      fun hmem => hphysical (by simp [hmem])
    simp only [List.mem_append] at hm
    rcases hm with hm | hm
    · have hw : wire = some (source, .proc "s3", message) := by
        cases wire <;> simp [optionList] at hm ⊢
        exact hm.symm
      cases hnode <;> simp [hstoreAddr, hhead] at hw
      all_goals rcases hw with ⟨_, rfl⟩ <;> trivial
    · exact ih htailPhysical hm

theorem route_map_update
    (states : List (Addr × Local)) (address destination : Addr)
    (state : Local) :
    (⟨[], states, 0⟩ : Network.Conf system).route destination =
      (⟨[], states.map (fun x =>
        if x.1 == address then (x.1, state) else x), 0⟩ :
        Network.Conf system).route destination := by
  suffices states.any (·.1 == destination) =
      (states.map (fun x =>
        if x.1 == address then (x.1, state) else x)).any
          (·.1 == destination) by
    simp only [Network.Conf.route, Network.Conf.isProc, this]
  induction states with
  | nil => rfl
  | cons head tail ih =>
    obtain ⟨headAddress, headState⟩ := head
    simp only [List.map_cons, List.any_cons]
    by_cases h : headAddress = address <;> simp [h, ih]

theorem nodup_middle_not_mem {before after : List α} {value : α}
    (h : (before ++ value :: after).Nodup) :
    value ∉ before ∧ value ∉ after := by
  induction before with
  | nil =>
    simp only [List.nil_append, List.nodup_cons] at h
    exact ⟨by simp, h.1⟩
  | cons head tail ih =>
    simp only [List.cons_append, List.nodup_cons] at h
    obtain ⟨hhead, hrest⟩ := h
    obtain ⟨hbefore, hafter⟩ := ih hrest
    constructor
    · simp only [List.mem_cons, not_or]
      exact ⟨fun heq => hhead (by simp [heq]), hbefore⟩
    · exact hafter

theorem NodesRep.Focus.wire_to
    {cfg : Storage.Config} {store : Store}
    {nodes : List Addr} {states : List (Addr × Local)}
    {wires : List ConcreteMessage} {tokens : List AbstractMessage}
    {address : Addr}
    (focus : NodesRep.Focus cfg store nodes states wires tokens address)
    (hnodup : nodes.Nodup) (hstoreAddr : cfg.store = "s3")
    (hphysical : "s3" ∉ nodes)
    {source : Network.Who} {message : CMsg}
    (hm : (source, .proc address, message) ∈ wires) :
    focus.wire = some (source, .proc address, message) := by
  have hmember : address ∈ nodes := by
    rw [focus.nodes_eq]
    simp
  have hneStore : address ≠ cfg.store := by
    rw [hstoreAddr]
    exact fun heq => hphysical (heq ▸ hmember)
  have hsplit : address ∉ focus.beforeNodes ∧
      address ∉ focus.afterNodes := by
    apply nodup_middle_not_mem
    simpa [focus.nodes_eq] using hnodup
  rw [focus.wires_eq] at hm
  simp only [List.mem_append] at hm
  rcases hm with (hm | hm) | hm
  · exact (focus.before.no_wire_to hsplit.1 hneStore hm).elim
  · cases hwire : focus.wire with
    | none => simp [optionList, hwire] at hm
    | some wire =>
      simp [optionList, hwire] at hm
      simpa [hwire, hm]
  · exact (focus.after.no_wire_to hsplit.2 hneStore hm).elim

theorem NodesRep.Focus.wire_from
    {cfg : Storage.Config} {store : Store}
    {nodes : List Addr} {states : List (Addr × Local)}
    {wires : List ConcreteMessage} {tokens : List AbstractMessage}
    {address : Addr}
    (focus : NodesRep.Focus cfg store nodes states wires tokens address)
    (hnodup : nodes.Nodup) (hstoreAddr : cfg.store = "s3")
    (hphysical : "s3" ∉ nodes)
    {dest : Network.Who} {message : CMsg}
    (hm : (.proc address, dest, message) ∈ wires) :
    focus.wire = some (.proc address, dest, message) := by
  have hmember : address ∈ nodes := by
    rw [focus.nodes_eq]
    simp
  have hneStore : address ≠ cfg.store := by
    rw [hstoreAddr]
    exact fun heq => hphysical (heq ▸ hmember)
  have hsplit : address ∉ focus.beforeNodes ∧
      address ∉ focus.afterNodes := by
    apply nodup_middle_not_mem
    simpa [focus.nodes_eq] using hnodup
  rw [focus.wires_eq] at hm
  simp only [List.mem_append] at hm
  rcases hm with (hm | hm) | hm
  · exact (focus.before.no_wire_from hsplit.1 hneStore hm).elim
  · cases hwire : focus.wire with
    | none => simp [optionList, hwire] at hm
    | some wire =>
      simp [optionList, hwire] at hm
      simpa [hwire, hm]
  · exact (focus.after.no_wire_from hsplit.2 hneStore hm).elim

theorem NodesRep.protocol_is_between_procs
    {cfg : Storage.Config} {store : Store}
    {nodes : List Addr} {states : List (Addr × Local)}
    {wires : List ConcreteMessage} {tokens : List AbstractMessage}
    (h : NodesRep cfg store nodes states wires tokens)
    {message : ConcreteMessage} (hm : message ∈ wires) :
    ∃ source dest m, message = (.proc source, .proc dest, m) := by
  induction h with
  | nil => simp at hm
  | @cons address addresses running states wire restWires
      restTokens nodeTokens hnode hrest ih =>
    simp only [List.mem_append] at hm
    rcases hm with hm | hm
    · have hw : wire = some message := by
        cases wire <;> simp [optionList] at hm ⊢
        exact hm.symm
      exact hnode.wire_is_protocol hw
    · exact ih hm

theorem NodesRep.find_state_none {cfg : Storage.Config} {store : Store}
    {nodes : List Addr} {states : List (Addr × Local)}
    {wires : List ConcreteMessage} {tokens : List AbstractMessage}
    (h : NodesRep cfg store nodes states wires tokens)
    {address : Addr} (hm : address ∉ nodes) :
    states.find? (·.1 == address) = none := by
  induction h with
  | nil => rfl
  | @cons head tail running tailStates wire tailWires
      tailTokens nodeTokens hnode htail ih =>
    have hne : head ≠ address := by
      intro heq
      exact hm (by simp [heq])
    have htail : address ∉ tail :=
      fun hmem => hm (by simp [hmem])
    simp [List.find?_cons, beq_eq_false_iff_ne.mpr hne, ih htail]

theorem NodesRep.map_update_miss {cfg : Storage.Config} {store : Store}
    {nodes : List Addr} {states : List (Addr × Local)}
    {wires : List ConcreteMessage} {tokens : List AbstractMessage}
    (h : NodesRep cfg store nodes states wires tokens)
    {address : Addr} (hm : address ∉ nodes) (value : Local) :
    states.map (fun (a, state) => if a == address then (a, value) else (a, state)) =
      states := by
  induction h with
  | nil => rfl
  | @cons head tail running tailStates wire tailWires
      tailTokens nodeTokens hnode htail ih =>
    have hne : head ≠ address := by
      intro heq
      exact hm (by simp [heq])
    have htail : address ∉ tail :=
      fun hmem => hm (by simp [hmem])
    simp only [List.map_cons]
    rw [show (head == address) = false from beq_eq_false_iff_ne.mpr hne]
    simp only [Bool.false_eq_true, if_false]
    rw [ih htail]

theorem NodesRep.map_update_store {cfg : Storage.Config} {store : Store}
    {nodes : List Addr} {states : List (Addr × Local)}
    {wires : List ConcreteMessage} {tokens : List AbstractMessage}
    (h : NodesRep cfg store nodes states wires tokens)
    (hphysical : "s3" ∉ nodes) (nextStore : Store) :
    (states ++ [("s3", Local.store store)]).map
        (fun x : Addr × Local =>
          if x.1 == "s3" then (x.1, Local.store nextStore) else x) =
      states ++ [("s3", Local.store nextStore)] := by
  simp only [List.map_append, List.map_cons, List.map_nil]
  rw [h.map_update_miss hphysical (Local.store nextStore)]
  simp

theorem NodesRep.Focus.state_at
    {cfg : Storage.Config} {store : Store}
    {nodes : List Addr} {states : List (Addr × Local)}
    {wires : List ConcreteMessage} {tokens : List AbstractMessage}
    {address : Addr}
    (focus : NodesRep.Focus cfg store nodes states wires tokens address)
    (hnodup : nodes.Nodup) :
    (states.find? (·.1 == address)).map (·.2) = some (.node focus.running) := by
  have hsplit := nodup_middle_not_mem
    (by simpa [focus.nodes_eq] using hnodup)
  have heq := congrArg
    (fun xs : List (Addr × Local) =>
      (xs.find? (fun x => x.1 == address)).map (fun x => x.2))
    focus.states_eq
  rw [heq]
  rw [List.find?_append, focus.before.find_state_none hsplit.1]
  simp

theorem NodesRep.Focus.state_at_with_store
    {cfg : Storage.Config} {store : Store}
    {nodes : List Addr} {states : List (Addr × Local)}
    {wires : List ConcreteMessage} {tokens : List AbstractMessage}
    {address : Addr}
    (focus : NodesRep.Focus cfg store nodes states wires tokens address)
    (hnodup : nodes.Nodup) :
    ((states ++ [("s3", Local.store store)]).find?
      (fun x : Addr × Local => x.1 == address)).map
        (fun x : Addr × Local => x.2) =
      some (Local.node focus.running) := by
  have h := focus.state_at hnodup
  change Option.map (fun x : Addr × Local => x.2)
      (List.find? (fun x : Addr × Local => x.1 == address)
        (states ++ [("s3", Local.store store)])) =
    some (Local.node focus.running)
  rw [List.find?_append]
  cases hfind : states.find? (·.1 == address) with
  | none => simp [hfind] at h
  | some value =>
    simp only [hfind, Option.map_some, Option.some.injEq] at h
    simp [hfind, h]

theorem NodesRep.Focus.map_update
    {cfg : Storage.Config} {store : Store}
    {nodes : List Addr} {states : List (Addr × Local)}
    {wires : List ConcreteMessage} {tokens : List AbstractMessage}
    {address : Addr}
    (focus : NodesRep.Focus cfg store nodes states wires tokens address)
    (hnodup : nodes.Nodup) (hphysical : "s3" ∉ nodes)
    (running : Running Storage.Config Nat CMsg) :
    (states ++ [("s3", Local.store store)]).map
        (fun x : Addr × Local =>
          if x.1 == address then (x.1, Local.node running) else x) =
      (focus.beforeStates ++
        (address, Local.node running) :: focus.afterStates) ++
        [("s3", Local.store store)] := by
  have hsplit := nodup_middle_not_mem
    (by simpa [focus.nodes_eq] using hnodup)
  have hmember : address ∈ nodes := by
    rw [focus.nodes_eq]
    simp
  have hneStore : "s3" ≠ address := by
    intro heq
    exact hphysical (heq ▸ hmember)
  have heq := congrArg
    (fun xs : List (Addr × Local) =>
      (xs ++ [("s3", Local.store store)]).map
        (fun x : Addr × Local =>
          if x.1 == address then (x.1, Local.node running) else x))
    focus.states_eq
  rw [heq]
  simp only [List.map_append, List.map_cons, List.map_nil]
  rw [focus.before.map_update_miss hsplit.1,
    focus.after.map_update_miss hsplit.2]
  simp [beq_eq_false_iff_ne.mpr hneStore]

theorem initial_store_rep :
    StoreRep ({} : Store) ({} : Experiment.State) := by
  intro key
  simp [storePromiseAt, storeLookup, Experiment.promiseAt]

theorem initial_nodesRep (cfg : Storage.Config) (nodes : List Addr) :
    NodesRep cfg ({} : Store) nodes
      (nodes.map (fun address => (address, .node ⟨0, [], node⟩))) [] [] := by
  induction nodes with
  | nil => exact .nil
  | cons address rest ih =>
    have hidle : NodeRep cfg ({} : Store) address
        ⟨0, [], node⟩ none [] := by
      exact NodeRep.idle (by simp [AppOnly]) rfl
    exact NodesRep.cons hidle ih

theorem initial_normalRel (nodes : List Addr) (cfg : Storage.Config) :
    NormalRel nodes cfg
      (Network.initial (world nodes)) (Experiment.initial {}) := by
  refine ⟨nodes.map (fun address => (address, .node ⟨0, [], node⟩)),
    {}, [], [], ?_, initial_nodesRep cfg nodes, ?_, ?_,
    initial_store_rep, Nat.le_refl 0⟩
  · rfl
  · exact .nil
  · exact ⟨[], .nil⟩

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

theorem NormalRel.clientRequest {nodes : List Addr}
    {cfg : Storage.Config}
    {c : Network.Conf system} {a : Experiment.Conf promises}
    (hrel : NormalRel nodes cfg c a)
    (client to : Addr) (t : Time) (m : Msg) :
    NormalRel nodes cfg
      ⟨c.net ++ [(.client client, .proc to, .app m)], c.states, t⟩
      ⟨a.net ++ [(.client client, .server, m)], a.state, t⟩ := by
  obtain ⟨states, store, wires, tokens, hstates, hnodes,
    hprotocol, hcover, hstore, htime⟩ := hrel
  refine ⟨states, store, wires, tokens, hstates, hnodes, ?_, ?_,
    hstore, Nat.le_refl t⟩
  · simpa [protocolMessages] using hprotocol
  · simpa [appTokens, appToken, List.append_assoc] using
      (Covers.insert_both
        (left := appTokens c.net) (right := tokens)
        (added := [((.client client, .server, m) : AbstractMessage)])
        hcover)

theorem NormalRel.clientReceive {nodes : List Addr}
    {cfg : Storage.Config}
    {c : Network.Conf system} {a : Experiment.Conf promises}
    (hrel : NormalRel nodes cfg c a)
    (sender : Network.Who) (client : Addr) (t : Time) (m : Msg)
    (pre post : List ConcreteMessage)
    (hnet : c.net = pre ++ (sender, .client client, .app m) :: post) :
    ∃ apre apost,
      a.net = apre ++ (.server, .client client, m) :: apost ∧
      NormalRel nodes cfg
        ⟨pre ++ post, c.states, t⟩
        ⟨apre ++ apost, a.state, t⟩ := by
  obtain ⟨states, store, wires, tokens, hstates, hnodes,
    hprotocol, hcover, hstore, htime⟩ := hrel
  rw [hnet] at hprotocol hcover
  have hc : Covers
      (appTokens pre ++
        (.server, .client client, m) :: (appTokens post ++ tokens)) a.net := by
    simpa [appTokens, appToken, List.append_assoc] using hcover
  obtain ⟨apre, apost, hanet, hc'⟩ := Covers.consume hc
  refine ⟨apre, apost, hanet, states, store, wires, tokens,
    hstates, hnodes, ?_, ?_, hstore, Nat.le_refl t⟩
  · simpa [protocolMessages, List.append_assoc] using hprotocol
  · simpa [appTokens, List.append_assoc] using hc'

theorem NormalRel.storeApp {nodes : List Addr}
    {cfg : Storage.Config}
    {c : Network.Conf system} {t : Time}
    {a : Experiment.Conf promises}
    (hrel : NormalRel nodes cfg c a)
    (source : Network.Who) (message : Msg) (hstepTime : c.now ≤ t)
    (pre post : List ConcreteMessage)
    (hnet : c.net = pre ++ (source, .proc "s3", .app message) :: post) :
    NormalRel nodes cfg
      ⟨pre ++ post, c.states, t⟩ a := by
  obtain ⟨nodeStates, store, wires, tokens,
    hstates, hnodes, hprotocol, hcover, hstore, htime⟩ := hrel
  refine ⟨nodeStates, store, wires, tokens, hstates, hnodes, ?_, ?_, hstore,
    Nat.le_trans htime hstepTime⟩
  · rw [hnet] at hprotocol
    simpa [protocolMessages, List.append_assoc] using hprotocol
  · rw [hnet] at hcover
    cases source with
    | client client =>
      have hc : Covers
          (appTokens pre ++
            (.client client, .server, message) ::
              (appTokens post ++ tokens)) a.net := by
        simpa [appTokens, appToken, List.append_assoc] using hcover
      simpa [appTokens, List.append_assoc] using Covers.drop_middle hc
    | proc sender =>
      cases message with
      | req id requestNow request =>
        have hc : Covers
            (appTokens pre ++
              (.client sender, .server, .req id requestNow request) ::
                (appTokens post ++ tokens)) a.net := by
          simpa [appTokens, appToken, List.append_assoc] using hcover
        simpa [appTokens, List.append_assoc] using Covers.drop_middle hc
      | res id response =>
        have hc : Covers
            (appTokens pre ++
              (.server, .client "s3", .res id response) ::
                (appTokens post ++ tokens)) a.net := by
          simpa [appTokens, appToken, List.append_assoc] using hcover
        simpa [appTokens, List.append_assoc] using Covers.drop_middle hc
      | notify promise =>
        have hc : Covers
            (appTokens pre ++
              (.server, .client "s3", .notify promise) ::
                (appTokens post ++ tokens)) a.net := by
          simpa [appTokens, appToken, List.append_assoc] using hcover
        simpa [appTokens, List.append_assoc] using Covers.drop_middle hc

theorem normalRel_nonrequest {nodes : List Addr}
    {cfg : Storage.Config} {store : Store}
    {nodeStates : List (Addr × Local)}
    {wires : List ConcreteMessage} {tokens : List AbstractMessage}
    {address : Addr}
    (focus : NodesRep.Focus cfg store nodes nodeStates wires tokens address)
    {net : List ConcreteMessage} {now t : Time}
    {a : Experiment.Conf promises}
    (hprotocol : (protocolMessages net).Perm wires)
    (hcover : Covers (appTokens net ++ tokens) a.net)
    (hstore : StoreRep store a.state) (htime : a.now ≤ now)
    (source : Network.Who) (message : Msg)
    (hstepTime : now ≤ t)
    (hm : isRequest source.addr (.app message) = false)
    (pre post : List ConcreteMessage)
    (hnet : net = pre ++ (source, .proc address, .app message) :: post) :
    ∃ running',
      (toStep node 64 source.addr (.app message) t cfg focus.running).val =
        [((), running', [])] ∧
      NormalRel nodes cfg
        ⟨pre ++ post,
          (focus.beforeStates ++
            (address, .node running') :: focus.afterStates) ++
              [("s3", .store store)],
          t⟩ a := by
  obtain ⟨running', hrun, hselected⟩ :=
    focus.selected.receive_app_nonrequest message t hm
  have hnodes := focus.replace hselected
  refine ⟨running', hrun, _, store,
    focus.beforeWires ++ optionList focus.wire ++ focus.afterWires,
    focus.beforeTokens ++ focus.nodeTokens ++ focus.afterTokens,
    rfl, hnodes, ?_, ?_, hstore, Nat.le_trans htime hstepTime⟩
  · rw [hnet] at hprotocol
    simpa [focus.wires_eq, protocolMessages, List.append_assoc] using hprotocol
  · rw [hnet] at hcover
    cases source with
    | client client =>
      have hc : Covers
          (appTokens pre ++
            (.client client, .server, message) ::
              (appTokens post ++ tokens)) a.net := by
        simpa [appTokens, appToken, List.append_assoc] using hcover
      simpa [focus.tokens_eq, appTokens, List.append_assoc] using
        Covers.drop_middle hc
    | proc sender =>
      cases message with
      | req id now request => simp [isRequest] at hm
      | res id response =>
        have hc : Covers
            (appTokens pre ++
              (.server, .client address, .res id response) ::
                (appTokens post ++ tokens)) a.net := by
          simpa [appTokens, appToken, List.append_assoc] using hcover
        simpa [focus.tokens_eq, appTokens, List.append_assoc] using
          Covers.drop_middle hc
      | notify promise =>
        have hc : Covers
            (appTokens pre ++
              (.server, .client address, .notify promise) ::
                (appTokens post ++ tokens)) a.net := by
          simpa [appTokens, appToken, List.append_assoc] using hcover
        simpa [focus.tokens_eq, appTokens, List.append_assoc] using
          Covers.drop_middle hc

theorem normalRel_request_busy {nodes : List Addr}
    {cfg : Storage.Config} {store : Store}
    {nodeStates : List (Addr × Local)}
    {wires : List ConcreteMessage} {tokens : List AbstractMessage}
    {address : Addr}
    (focus : NodesRep.Focus cfg store nodes nodeStates wires tokens address)
    (hbusy : focus.wire ≠ none)
    {net : List ConcreteMessage} {now t : Time}
    {a : Experiment.Conf promises}
    (hprotocol : (protocolMessages net).Perm wires)
    (hcover : Covers (appTokens net ++ tokens) a.net)
    (hstore : StoreRep store a.state) (htime : a.now ≤ now)
    (source : Network.Who) (id : CallId) (requestNow : Time)
    (request : Request) (hstepTime : now ≤ t)
    (pre post : List ConcreteMessage)
    (hnet : net =
      pre ++ (source, .proc address, .app (.req id requestNow request)) :: post) :
    ∃ running',
      (toStep node 64 source.addr (.app (.req id requestNow request)) t cfg
        focus.running).val = [((), running', [])] ∧
      NormalRel nodes cfg
        ⟨pre ++ post,
          (focus.beforeStates ++
            (address, .node running') :: focus.afterStates) ++
              [("s3", .store store)],
          t⟩ a := by
  obtain ⟨running', nodeTokens', hrun, hselected, htokens⟩ :=
    focus.selected.receive_app_request_busy id requestNow t request hbusy
  have hnodes := focus.replace hselected
  refine ⟨running', hrun, _, store,
    focus.beforeWires ++ optionList focus.wire ++ focus.afterWires,
    focus.beforeTokens ++ nodeTokens' ++ focus.afterTokens,
    rfl, hnodes, ?_, ?_, hstore, Nat.le_trans htime hstepTime⟩
  · rw [hnet] at hprotocol
    simpa [focus.wires_eq, protocolMessages, List.append_assoc] using hprotocol
  · rw [hnet] at hcover
    let token : AbstractMessage :=
      Call.token ⟨source.addr, id, request, requestNow⟩
    have happ :
        appToken
          (source, .proc address, .app (.req id requestNow request)) =
            some token := by
      cases source <;> rfl
    have hc : Covers
        (appTokens pre ++ token ::
          (appTokens post ++ focus.beforeTokens ++
            focus.nodeTokens ++ focus.afterTokens)) a.net := by
      simpa [focus.tokens_eq, appTokens, happ, List.append_assoc] using hcover
    apply Covers.of_perm _ hc
    have hmove :
        (appTokens pre ++ token ::
          (appTokens post ++ focus.beforeTokens ++
            focus.nodeTokens ++ focus.afterTokens)).Perm
        (appTokens pre ++ appTokens post ++ focus.beforeTokens ++
          (focus.nodeTokens ++ [token]) ++ focus.afterTokens) := by
      simpa [List.append_assoc, List.cons_append] using
        (List.Perm.append_left (appTokens pre)
          (perm_append_cons_head
            (appTokens post ++ focus.beforeTokens ++ focus.nodeTokens)
            focus.afterTokens token).symm)
    have hreplace :
        (appTokens pre ++ appTokens post ++ focus.beforeTokens ++
          (focus.nodeTokens ++ [token]) ++ focus.afterTokens).Perm
        (appTokens pre ++ appTokens post ++ focus.beforeTokens ++
          nodeTokens' ++ focus.afterTokens) := by
      simpa [List.append_assoc] using
        (List.Perm.append_right focus.afterTokens
          (List.Perm.append_left
            (appTokens pre ++ appTokens post ++ focus.beforeTokens)
            htokens.symm))
    simpa [appTokens, List.append_assoc] using hmove.trans hreplace

theorem normalRel_request_idle
    {cfg : Storage.Config} {store : Store} {address : Addr}
    {beforeNodes afterNodes : List Addr}
    {beforeStates afterStates : List (Addr × Local)}
    {beforeWires afterWires : List ConcreteMessage}
    {beforeTokens afterTokens : List AbstractMessage}
    (hbefore : NodesRep cfg store beforeNodes beforeStates
      beforeWires beforeTokens)
    (hafter : NodesRep cfg store afterNodes afterStates
      afterWires afterTokens)
    {next : Nat} {mailbox : List (Addr × CMsg)}
    (happ : AppOnly mailbox) (hn : take? isRequest mailbox = none)
    (hstoreAddr : cfg.store = "s3")
    {net : List ConcreteMessage} {now t : Time}
    {a : Experiment.Conf promises}
    (hprotocol : (protocolMessages net).Perm
      (beforeWires ++ afterWires))
    (hcover : Covers
      (appTokens net ++ beforeTokens ++ mailboxTokens mailbox ++ afterTokens)
      a.net)
    (hstore : StoreRep store a.state) (htime : a.now ≤ now)
    (source : Network.Who) (id : CallId) (requestNow : Time)
    (request : Request) (hstepTime : now ≤ t)
    (pre post : List ConcreteMessage)
    (hnet : net =
      pre ++ (source, .proc address, .app (.req id requestNow request)) :: post) :
    let nextNode : Running Storage.Config Nat CMsg :=
      ⟨next + 1, mailbox,
        loadK cfg.retries
          (Call.retry ⟨source.addr, id, request, requestNow⟩ cfg.retries)
          source.addr id request requestNow next⟩
    let wire : ConcreteMessage :=
      (.proc address, .proc "s3", .get next request.key)
    (toStep node 64 source.addr (.app (.req id requestNow request)) t cfg
      ⟨next, mailbox, node⟩).val =
        [((), nextNode, [.send "s3" (.get next request.key)])] ∧
    NormalRel (beforeNodes ++ address :: afterNodes) cfg
      ⟨pre ++ post ++ [wire],
        (beforeStates ++ (address, .node nextNode) :: afterStates) ++
          [("s3", .store store)],
        t⟩ a := by
  dsimp
  constructor
  · simpa [hstoreAddr] using
      (idle_request_run (cfg := cfg) happ hn next source.addr id
        requestNow t request)
  · let call : Call := ⟨source.addr, id, request, requestNow⟩
    let wire : ConcreteMessage :=
      (.proc address, .proc "s3", .get next request.key)
    have hselected : NodeRep cfg store address
        ⟨next + 1, mailbox,
          loadK cfg.retries (call.retry cfg.retries)
            call.client call.id call.req call.now next⟩
        (some wire) (mailboxTokens mailbox ++ [call.token]) := by
      simpa [wire, call, hstoreAddr] using
        (NodeRep.loadingGet
          (cfg := cfg) (store := store) (address := address)
          (call := call) (tries := cfg.retries) happ rfl
          (answers_none_of_appOnly mailbox next happ))
    have hnodes :
        NodesRep cfg store (beforeNodes ++ address :: afterNodes)
          (beforeStates ++
            (address, .node
              ⟨next + 1, mailbox,
                loadK cfg.retries (call.retry cfg.retries)
                  call.client call.id call.req call.now next⟩) ::
              afterStates)
          (beforeWires ++ [wire] ++ afterWires)
          (beforeTokens ++
            (mailboxTokens mailbox ++ [call.token]) ++ afterTokens) := by
      simpa [wire, optionList, List.append_assoc] using
        hbefore.append (NodesRep.cons hselected hafter)
    refine ⟨_, store, _, _, rfl, hnodes, ?_, ?_, hstore,
      Nat.le_trans htime hstepTime⟩
    · rw [hnet] at hprotocol
      have hp := hprotocol.append_right [wire]
      have hswap :
          ((beforeWires ++ afterWires) ++ [wire]).Perm
            (beforeWires ++ [wire] ++ afterWires) := by
        simpa [List.append_assoc] using
          (List.Perm.append_left beforeWires
            (List.perm_append_comm :
              (afterWires ++ [wire]).Perm ([wire] ++ afterWires)))
      simpa [wire, protocolMessages, optionList, List.append_assoc] using
        hp.trans hswap
    · rw [hnet] at hcover
      have hat :
          appToken
            (source, .proc address, .app (.req id requestNow request)) =
              some call.token := by
        cases source <;> rfl
      have hwire :
          appToken
            ((.proc address, .proc "s3", .get next request.key) :
              ConcreteMessage) = none := rfl
      apply Covers.of_perm _ hcover
      simp only [appTokens, List.filterMap_append, List.filterMap_cons,
        hat, hwire, List.filterMap_nil, List.append_nil]
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using
        (List.Perm.append_left (List.filterMap appToken pre)
          (perm_append_cons_head
            (List.filterMap appToken post ++ beforeTokens ++
              mailboxTokens mailbox)
            afterTokens call.token).symm)

theorem normalRel_conflict_retry
    {cfg : Storage.Config} {store : Store} {address : Addr}
    {beforeNodes afterNodes : List Addr}
    {beforeStates afterStates : List (Addr × Local)}
    {beforeWires afterWires : List ConcreteMessage}
    {beforeTokens afterTokens : List AbstractMessage}
    (hbefore : NodesRep cfg store beforeNodes beforeStates
      beforeWires beforeTokens)
    (hafter : NodesRep cfg store afterNodes afterStates
      afterWires afterTokens)
    {candidate : Candidate} {op next k : Nat}
    {mailbox : List (Addr × CMsg)}
    (happ : AppOnly mailbox) (hnone : take? (answers op) mailbox = none)
    (hvalid : candidate.Valid cfg)
    (hsnapshot : Snapshot store candidate.req.key candidate.doc)
    (htries : candidate.tries = k + 1)
    (hstoreAddr : cfg.store = "s3")
    {net : List ConcreteMessage} {now t : Time}
    {a : Experiment.Conf promises}
    (hprotocol : (protocolMessages net).Perm
      (beforeWires ++
        [((.proc "s3", .proc address, .conflict op) : ConcreteMessage)] ++
        afterWires))
    (hcover : Covers
      (appTokens net ++ beforeTokens ++
        (mailboxTokens mailbox ++ candidate.stageTokens .pending) ++
        afterTokens) a.net)
    (hstore : StoreRep store a.state) (htime : a.now ≤ now)
    (hstepTime : now ≤ t) (source : Network.Who)
    (pre post : List ConcreteMessage)
    (hnet : net = pre ++
      ((.proc "s3", .proc address, .conflict op) : ConcreteMessage) :: post) :
    let running : Running Storage.Config Nat CMsg :=
      ⟨next + 1, mailbox,
        loadK k (candidate.call.retry k)
          candidate.client candidate.id candidate.req candidate.now next⟩
    let wire : ConcreteMessage :=
      (.proc address, .proc "s3", .get next candidate.req.key)
    (toStep node 64 source.addr (.conflict op) t cfg
      (⟨next, mailbox,
        writeK candidate.tries (candidate.call.retry candidate.tries)
          candidate op⟩ : Running Storage.Config Nat CMsg)).val =
      [((), running, [.send "s3" (.get next candidate.req.key)])] ∧
    NormalRel (beforeNodes ++ address :: afterNodes) cfg
      ⟨pre ++ post ++ [wire],
        (beforeStates ++ (address, .node running) :: afterStates) ++
          [("s3", .store store)],
        t⟩ a := by
  dsimp
  constructor
  · simpa [hstoreAddr] using
      (writing_conflict_retry_run (cfg := cfg) (cand := candidate)
        (next := next) happ hnone htries source.addr t)
  · let wire : ConcreteMessage :=
      (.proc address, .proc "s3", .get next candidate.req.key)
    have hselected : NodeRep cfg store address
        ⟨next + 1, mailbox,
          loadK k (candidate.call.retry k)
            candidate.client candidate.id candidate.req candidate.now next⟩
        (some wire) (mailboxTokens mailbox ++ [candidate.call.token]) := by
      simpa [wire, hstoreAddr, Candidate.call] using
        (NodeRep.loadingGet
          (cfg := cfg) (store := store) (address := address)
          (call := candidate.call) (tries := k)
          happ rfl (answers_none_of_appOnly mailbox next happ))
    have hnodes := hbefore.append (NodesRep.cons hselected hafter)
    refine ⟨_, store,
      beforeWires ++ [wire] ++ afterWires,
      beforeTokens ++ (mailboxTokens mailbox ++ [candidate.call.token]) ++
        afterTokens,
      rfl, ?_, ?_, ?_, hstore, Nat.le_trans htime hstepTime⟩
    · simpa [wire, optionList, List.append_assoc] using hnodes
    · rw [hnet] at hprotocol
      have hbase :
          (protocolMessages pre ++ protocolMessages post).Perm
            (beforeWires ++ afterWires) := by
        apply perm_cancel_middle
          (value := ((.proc "s3", .proc address, .conflict op) :
            ConcreteMessage))
        simpa [protocolMessages, List.append_assoc] using hprotocol
      have hp := hbase.append_right [wire]
      have hinsert :
          ((beforeWires ++ afterWires) ++ [wire]).Perm
            (beforeWires ++ [wire] ++ afterWires) := by
        simpa [List.append_assoc] using
          (List.Perm.append_left beforeWires
            (List.perm_append_comm :
              (afterWires ++ [wire]).Perm ([wire] ++ afterWires)))
      simpa [wire, protocolMessages, List.append_assoc] using hp.trans hinsert
    · rw [hnet] at hcover
      simpa [wire, appTokens, appToken, Candidate.stageTokens,
        List.append_assoc] using hcover

theorem normalRel_got_changed
    {cfg : Storage.Config} {store : Store} {address : Addr}
    {beforeNodes afterNodes : List Addr}
    {beforeStates afterStates : List (Addr × Local)}
    {beforeWires afterWires : List ConcreteMessage}
    {beforeTokens afterTokens : List AbstractMessage}
    (hbefore : NodesRep cfg store beforeNodes beforeStates
      beforeWires beforeTokens)
    (hafter : NodesRep cfg store afterNodes afterStates
      afterWires afterTokens)
    {call : Call} {tries op next : Nat} {mailbox : List (Addr × CMsg)}
    {doc : Option (Promise × Version)}
    {res : Response} {after : Experiment.State} {outs : List (Out Msg)}
    {promise : Promise}
    (happ : AppOnly mailbox) (hnone : take? (answers op) mailbox = none)
    (hpick :
      pick ((Experiment.dispatch call.req call.now).run
        { cfg.app with unreliable := true }
        { promises := doc.toList.map (·.1) }) 0 = (res, after, outs))
    (hchanged : (after == { promises := doc.toList.map (·.1) }) = false)
    (hpromise : after.promises.find? (·.id == call.req.key) = some promise)
    (hsnapshot : Snapshot store call.req.key doc)
    (hdoc : DocAtKey call.req.key doc)
    (hstoreAddr : cfg.store = "s3")
    {net : List ConcreteMessage} {now t : Time}
    {a : Experiment.Conf promises}
    (hprotocol : (protocolMessages net).Perm
      (beforeWires ++
        [((.proc "s3", .proc address, .got op doc) : ConcreteMessage)] ++
        afterWires))
    (hcover : Covers
      (appTokens net ++ beforeTokens ++
        (mailboxTokens mailbox ++ [call.token]) ++ afterTokens) a.net)
    (hstore : StoreRep store a.state) (htime : a.now ≤ now)
    (hstepTime : now ≤ t) (source : Network.Who)
    (pre post : List ConcreteMessage)
    (hnet : net = pre ++
      ((.proc "s3", .proc address, .got op doc) : ConcreteMessage) :: post) :
    let candidate : Candidate :=
      ⟨call.client, call.id, call.req, call.now, tries, doc,
        res, after, outs, promise⟩
    let running : Running Storage.Config Nat CMsg :=
      ⟨next + 1, mailbox, writeK tries (call.retry tries) candidate next⟩
    let wire : ConcreteMessage :=
      (.proc address, .proc "s3",
        .put next call.req.key promise (doc.map (·.2)))
    (toStep node 64 source.addr (.got op doc) t cfg
      (⟨next, mailbox,
        loadK tries (call.retry tries)
          call.client call.id call.req call.now op⟩ :
        Running Storage.Config Nat CMsg)).val =
      [((), running, notes outs ++
        [.send "s3" (.put next call.req.key promise (doc.map (·.2)))])] ∧
    NormalRel (beforeNodes ++ address :: afterNodes) cfg
      ⟨pre ++ post ++ [wire],
        (beforeStates ++ (address, .node running) :: afterStates) ++
          [("s3", .store store)],
        t⟩ a := by
  dsimp
  constructor
  · simpa [hstoreAddr] using
      (loading_got_changed_run happ hnone hpick hchanged hpromise source.addr t)
  · let candidate : Candidate :=
      ⟨call.client, call.id, call.req, call.now, tries, doc,
        res, after, outs, promise⟩
    let wire : ConcreteMessage :=
      (.proc address, .proc "s3",
        .put next call.req.key promise (doc.map (·.2)))
    have hselected : NodeRep cfg store address
        ⟨next + 1, mailbox, writeK tries (call.retry tries) candidate next⟩
        (some wire) (mailboxTokens mailbox ++ candidate.stageTokens .pending) := by
      simpa [wire, candidate, Candidate.call, hstoreAddr] using
        (NodeRep.writingPut
          (cfg := cfg) (store := store) (address := address)
          (candidate := candidate) happ rfl
          (answers_none_of_appOnly mailbox next happ)
          (changed_candidate_valid hpick hdoc hpromise) hsnapshot)
    have hnodes := hbefore.append (NodesRep.cons hselected hafter)
    refine ⟨_, store, beforeWires ++ [wire] ++ afterWires,
      beforeTokens ++
        (mailboxTokens mailbox ++ candidate.stageTokens .pending) ++
        afterTokens,
      rfl, ?_, ?_, ?_, hstore, Nat.le_trans htime hstepTime⟩
    · simpa [wire, optionList, List.append_assoc] using hnodes
    · rw [hnet] at hprotocol
      have hbase :
          (protocolMessages pre ++ protocolMessages post).Perm
            (beforeWires ++ afterWires) := by
        apply perm_cancel_middle
          (value := ((.proc "s3", .proc address, .got op doc) :
            ConcreteMessage))
        simpa [protocolMessages, List.append_assoc] using hprotocol
      have hp := hbase.append_right [wire]
      have hinsert :
          ((beforeWires ++ afterWires) ++ [wire]).Perm
            (beforeWires ++ [wire] ++ afterWires) := by
        simpa [List.append_assoc] using
          (List.Perm.append_left beforeWires
            (List.perm_append_comm :
              (afterWires ++ [wire]).Perm ([wire] ++ afterWires)))
      simpa [wire, protocolMessages, List.append_assoc] using hp.trans hinsert
    · rw [hnet] at hcover
      simpa [wire, candidate, Candidate.call, Candidate.stageTokens,
        appTokens, appToken,
        List.append_assoc] using hcover

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

theorem normalRel_store_get_changed
    {cfg : Storage.Config} {store : Store} {address : Addr}
    {beforeNodes afterNodes : List Addr}
    {beforeStates afterStates : List (Addr × Local)}
    {beforeWires afterWires : List ConcreteMessage}
    {beforeTokens afterTokens : List AbstractMessage}
    (hbefore : NodesRep cfg store beforeNodes beforeStates
      beforeWires beforeTokens)
    (hafter : NodesRep cfg store afterNodes afterStates
      afterWires afterTokens)
    {call : Call} {tries op next : Nat} {mailbox : List (Addr × CMsg)}
    (happ : AppOnly mailbox) (hnext : next = op + 1)
    (hnone : take? (answers op) mailbox = none)
    {res : Response} {after : Experiment.State} {outs : List (Out Msg)}
    (hpick :
      pick ((Experiment.dispatch call.req call.now).run
        { cfg.app with unreliable := true }
        { promises := (storeLookup store call.req.key).toList.map (·.1) }) 0 =
          (res, after, outs))
    (hchanged :
      after ≠ { promises :=
        (storeLookup store call.req.key).toList.map (·.1) })
    (hstoreAddr : cfg.store = "s3")
    {net : List ConcreteMessage} {now t : Time}
    {a : Experiment.Conf promises}
    (hprotocol : (protocolMessages net).Perm
      (beforeWires ++
        [((.proc address, .proc "s3", .get op call.req.key) :
          ConcreteMessage)] ++ afterWires))
    (hcover : Covers
      (appTokens net ++ beforeTokens ++
        (mailboxTokens mailbox ++ [call.token]) ++ afterTokens) a.net)
    (hstore : StoreRep store a.state) (htime : a.now ≤ now)
    (hstepTime : now ≤ t) (pre post : List ConcreteMessage)
    (hnet : net = pre ++
      ((.proc address, .proc "s3", .get op call.req.key) :
        ConcreteMessage) :: post) :
    let doc := storeLookup store call.req.key
    let reply : ConcreteMessage := (.proc "s3", .proc address, .got op doc)
    ((storeReceive address (.get op call.req.key)).run cfg store).val =
      [((), store, [.send address (.got op doc)])] ∧
    NormalRel (beforeNodes ++ address :: afterNodes) cfg
      ⟨pre ++ post ++ [reply],
        (beforeStates ++
          (address, .node ⟨next, mailbox,
            loadK tries (call.retry tries)
              call.client call.id call.req call.now op⟩) :: afterStates) ++
          [("s3", .store store)],
        t⟩ a := by
  dsimp
  constructor
  · exact store_get_run cfg store address op call.req.key
  · let reply : ConcreteMessage :=
      (.proc "s3", .proc address, .got op (storeLookup store call.req.key))
    have hselected : NodeRep cfg store address
        ⟨next, mailbox,
          loadK tries (call.retry tries)
            call.client call.id call.req call.now op⟩
        (some reply) (mailboxTokens mailbox ++ [call.token]) := by
      simpa [reply, hstoreAddr] using
        (NodeRep.loadingGot
          (cfg := cfg) (store := store) (address := address)
          (call := call) (tries := tries)
          happ hnext hnone ⟨res, after, outs, hpick, hchanged⟩
          (Snapshot.of_lookup rfl)
          (docAtKey_of_rep_lookup hstore rfl))
    have hnodes := hbefore.append (NodesRep.cons hselected hafter)
    refine ⟨_, store, beforeWires ++ [reply] ++ afterWires,
      beforeTokens ++ (mailboxTokens mailbox ++ [call.token]) ++ afterTokens,
      rfl, ?_, ?_, ?_, hstore, Nat.le_trans htime hstepTime⟩
    · simpa [reply, optionList, List.append_assoc] using hnodes
    · rw [hnet] at hprotocol
      have hbase :
          (protocolMessages pre ++ protocolMessages post).Perm
            (beforeWires ++ afterWires) := by
        apply perm_cancel_middle
          (value := ((.proc address, .proc "s3", .get op call.req.key) :
            ConcreteMessage))
        simpa [protocolMessages, List.append_assoc] using hprotocol
      have hp := hbase.append_right [reply]
      have hinsert :
          ((beforeWires ++ afterWires) ++ [reply]).Perm
            (beforeWires ++ [reply] ++ afterWires) := by
        simpa [List.append_assoc] using
          (List.Perm.append_left beforeWires
            (List.perm_append_comm :
              (afterWires ++ [reply]).Perm ([reply] ++ afterWires)))
      simpa [reply, protocolMessages, List.append_assoc] using hp.trans hinsert
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

theorem normalRel_store_conflict
    {cfg : Storage.Config} {store : Store} {address : Addr}
    {beforeNodes afterNodes : List Addr}
    {beforeStates afterStates : List (Addr × Local)}
    {beforeWires afterWires : List ConcreteMessage}
    {beforeTokens afterTokens : List AbstractMessage}
    (hbefore : NodesRep cfg store beforeNodes beforeStates
      beforeWires beforeTokens)
    (hafter : NodesRep cfg store afterNodes afterStates
      afterWires afterTokens)
    {candidate : Candidate} {op next : Nat} {mailbox : List (Addr × CMsg)}
    (happ : AppOnly mailbox) (hnext : next = op + 1)
    (hnone : take? (answers op) mailbox = none)
    (hvalid : candidate.Valid cfg)
    (hsnapshot : Snapshot store candidate.req.key candidate.doc)
    (hstoreAddr : cfg.store = "s3")
    {net : List ConcreteMessage} {now t : Time}
    {a : Experiment.Conf promises}
    (hprotocol : (protocolMessages net).Perm
      (beforeWires ++
        [((.proc address, .proc "s3",
          .put op candidate.req.key candidate.promise
            (candidate.doc.map (·.2))) : ConcreteMessage)] ++
        afterWires))
    (hcover : Covers
      (appTokens net ++ beforeTokens ++
        (mailboxTokens mailbox ++ candidate.stageTokens .pending) ++
        afterTokens) a.net)
    (hstore : StoreRep store a.state) (htime : a.now ≤ now)
    (hstepTime : now ≤ t) (pre post : List ConcreteMessage)
    (hnet : net = pre ++
      ((.proc address, .proc "s3",
        .put op candidate.req.key candidate.promise
          (candidate.doc.map (·.2))) : ConcreteMessage) :: post) :
    let reply : ConcreteMessage := (.proc "s3", .proc address, .conflict op)
    NormalRel (beforeNodes ++ address :: afterNodes) cfg
      ⟨pre ++ post ++ [reply],
        (beforeStates ++
          (address, .node ⟨next, mailbox,
            writeK candidate.tries (candidate.call.retry candidate.tries)
              candidate op⟩) :: afterStates) ++
          [("s3", .store store)],
        t⟩ a := by
  dsimp
  let reply : ConcreteMessage := (.proc "s3", .proc address, .conflict op)
  have hselected : NodeRep cfg store address
      ⟨next, mailbox,
        writeK candidate.tries (candidate.call.retry candidate.tries)
          candidate op⟩
      (some reply)
      (mailboxTokens mailbox ++ candidate.stageTokens .pending) := by
    simpa [reply, hstoreAddr] using
      (NodeRep.writingConflict
        (cfg := cfg) (store := store) (address := address)
        (candidate := candidate) happ hnext hnone hvalid hsnapshot)
  have hnodes := hbefore.append (NodesRep.cons hselected hafter)
  refine ⟨_, store, beforeWires ++ [reply] ++ afterWires,
    beforeTokens ++
      (mailboxTokens mailbox ++ candidate.stageTokens .pending) ++
      afterTokens,
    rfl, ?_, ?_, ?_, hstore, Nat.le_trans htime hstepTime⟩
  · simpa [reply, optionList, List.append_assoc] using hnodes
  · rw [hnet] at hprotocol
    have hbase :
        (protocolMessages pre ++ protocolMessages post).Perm
          (beforeWires ++ afterWires) := by
      apply perm_cancel_middle
        (value := ((.proc address, .proc "s3",
          .put op candidate.req.key candidate.promise
            (candidate.doc.map (·.2))) : ConcreteMessage))
      simpa [protocolMessages, List.append_assoc] using hprotocol
    have hp := hbase.append_right [reply]
    have hinsert :
        ((beforeWires ++ afterWires) ++ [reply]).Perm
          (beforeWires ++ [reply] ++ afterWires) := by
      simpa [List.append_assoc] using
        (List.Perm.append_left beforeWires
          (List.perm_append_comm :
            (afterWires ++ [reply]).Perm ([reply] ++ afterWires)))
    simpa [reply, protocolMessages, List.append_assoc] using hp.trans hinsert
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

theorem route_store_for_split_states
    {cfg : Storage.Config} (hstoreAddr : cfg.store = "s3")
    (before after : List (Addr × Local)) (address : Addr)
    (running : Running Storage.Config Nat CMsg) (store : Store) :
    (⟨[], (before ++ (address, .node running) :: after) ++
      [("s3", .store store)], 0⟩ : Network.Conf system).route cfg.store =
        .proc cfg.store := by
  simp [Network.Conf.route, Network.Conf.isProc, hstoreAddr]

theorem normalRel_store_get_done
    {cfg : Storage.Config} {store : Store} {address : Addr}
    {beforeNodes afterNodes : List Addr}
    {beforeStates afterStates : List (Addr × Local)}
    {beforeWires afterWires : List ConcreteMessage}
    {beforeTokens afterTokens : List AbstractMessage}
    (hbefore : NodesRep cfg store beforeNodes beforeStates
      beforeWires beforeTokens)
    (hafter : NodesRep cfg store afterNodes afterStates
      afterWires afterTokens)
    {call : Call} {tries op next : Nat} {mailbox : List (Addr × CMsg)}
    {doc : Option (Promise × Version)} {res : Response}
    {after : Experiment.State} {outs : List (Out Msg)}
    (happ : AppOnly mailbox) (hnext : next = op + 1)
    (hnone : take? (answers op) mailbox = none)
    (hpick :
      pick ((Experiment.dispatch call.req call.now).run
        { cfg.app with unreliable := true }
        { promises := doc.toList.map (·.1) }) 0 = (res, after, outs))
    (hunchanged : after = { promises := doc.toList.map (·.1) })
    (hstoreAddr : cfg.store = "s3")
    {net : List ConcreteMessage} {now t : Time}
    {a : Experiment.Conf promises}
    (hprotocol : (protocolMessages net).Perm
      (beforeWires ++
        [((.proc address, .proc "s3", .get op call.req.key) :
          ConcreteMessage)] ++ afterWires))
    (hcover : Covers
      (appTokens net ++ beforeTokens ++
        (mailboxTokens mailbox ++ [call.token]) ++ afterTokens) a.net)
    (hstore : StoreRep store a.state) (htime : a.now ≤ now)
    (hstepTime : now ≤ t) (pre post : List ConcreteMessage)
    (hnet : net = pre ++
      ((.proc address, .proc "s3", .get op call.req.key) :
        ConcreteMessage) :: post)
    (hdocValue : doc = storeLookup store call.req.key) :
    let reply : ConcreteMessage := (.proc "s3", .proc address, .got op doc)
    ∃ a',
      Network.Matches { cfg.app with unreliable := true } clientView a
        (.proc "s3", t, .receive (.proc address)
          (CMsg.get op call.req.key)) a' ∧
      NormalRel (beforeNodes ++ address :: afterNodes) cfg
        ⟨pre ++ post ++ [reply],
          (beforeStates ++
            (address, .node ⟨next, mailbox,
              loadK tries (call.retry tries)
                call.client call.id call.req call.now op⟩) :: afterStates) ++
            [("s3", .store store)], t⟩ a' := by
  dsimp
  rw [hnet] at hcover
  have hcCall : Covers
      ((appTokens pre ++ appTokens post ++ beforeTokens ++
        mailboxTokens mailbox) ++ call.token :: afterTokens) a.net := by
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
  · let reply : ConcreteMessage := (.proc "s3", .proc address, .got op doc)
    have hselected : NodeRep cfg store address
        ⟨next, mailbox,
          loadK tries (call.retry tries)
            call.client call.id call.req call.now op⟩
        (some reply)
        (mailboxTokens mailbox ++ outputTokens outs ++
          [responseToken call.client call.id res]) := by
      simpa [reply, hstoreAddr] using
        (NodeRep.loadingDone
          (cfg := cfg) (store := store) (address := address)
          (call := call) (tries := tries) (doc := doc)
          happ hnext hnone hpick hunchanged
          (Snapshot.of_lookup hdocValue.symm)
          (docAtKey_of_rep_lookup hstore hdocValue.symm))
    have hnodes := hbefore.append (NodesRep.cons hselected hafter)
    refine ⟨_, store, beforeWires ++ [reply] ++ afterWires,
      beforeTokens ++
        (mailboxTokens mailbox ++ outputTokens outs ++
          [responseToken call.client call.id res]) ++ afterTokens,
      rfl, ?_, ?_, ?_, hstore', Nat.le_trans htime hstepTime⟩
    · simpa [reply, optionList, List.append_assoc] using hnodes
    · rw [hnet] at hprotocol
      have hbase :
          (protocolMessages pre ++ protocolMessages post).Perm
            (beforeWires ++ afterWires) := by
        apply perm_cancel_middle
          (value := ((.proc address, .proc "s3", .get op call.req.key) :
            ConcreteMessage))
        simpa [protocolMessages, List.append_assoc] using hprotocol
      simpa [reply, protocolMessages, List.append_assoc] using
        (perm_append_insert_middle hbase (added := [reply]))
    · have hcAdded := Covers.insert_both
        (left := appTokens pre ++ appTokens post ++ beforeTokens ++
          mailboxTokens mailbox)
        (right := afterTokens) (added := emitted) hcRest
      simpa [a', emitted, reply, appTokens, appToken,
        List.append_assoc] using hcAdded

theorem normalRel_store_written
    {cfg : Storage.Config} {store : Store} {address : Addr}
    {beforeNodes afterNodes : List Addr}
    {beforeStates afterStates : List (Addr × Local)}
    {beforeWires afterWires : List ConcreteMessage}
    {beforeTokens afterTokens : List AbstractMessage}
    (hbefore : NodesRep cfg store beforeNodes beforeStates
      beforeWires beforeTokens)
    (hafter : NodesRep cfg store afterNodes afterStates
      afterWires afterTokens)
    {candidate : Candidate} {op next : Nat} {mailbox : List (Addr × CMsg)}
    (happ : AppOnly mailbox) (hnext : next = op + 1)
    (hnone : take? (answers op) mailbox = none)
    (hvalid : candidate.Valid cfg)
    (hsnapshot : Snapshot store candidate.req.key candidate.doc)
    (hmatch : candidate.doc.map (·.2) =
      (storeLookup store candidate.req.key).map (·.2))
    (hstoreAddr : cfg.store = "s3")
    {net : List ConcreteMessage} {now t : Time}
    {a : Experiment.Conf promises}
    (hprotocol : (protocolMessages net).Perm
      (beforeWires ++
        [((.proc address, .proc "s3",
          .put op candidate.req.key candidate.promise
            (candidate.doc.map (·.2))) : ConcreteMessage)] ++
        afterWires))
    (hcover : Covers
      (appTokens net ++ beforeTokens ++
        (mailboxTokens mailbox ++ candidate.stageTokens .pending) ++
        afterTokens) a.net)
    (hstore : StoreRep store a.state) (htime : a.now ≤ now)
    (hstepTime : now ≤ t) (pre post : List ConcreteMessage)
    (hnet : net = pre ++
      ((.proc address, .proc "s3",
        .put op candidate.req.key candidate.promise
          (candidate.doc.map (·.2))) : ConcreteMessage) :: post) :
    let committed := storeCommit store candidate.req.key candidate.promise
    let reply : ConcreteMessage := (.proc "s3", .proc address, .written op)
    ∃ a',
      Network.Matches { cfg.app with unreliable := true } clientView a
        (.proc "s3", t, .receive (.proc address)
          (CMsg.put op candidate.req.key candidate.promise
            (candidate.doc.map (·.2)))) a' ∧
      NormalRel (beforeNodes ++ address :: afterNodes) cfg
        ⟨pre ++ post ++ [reply],
          (beforeStates ++
            (address, .node ⟨next, mailbox,
              writeK candidate.tries (candidate.call.retry candidate.tries)
                candidate op⟩) :: afterStates) ++
            [("s3", .store committed)], t⟩ a' := by
  dsimp
  rw [hnet] at hcover
  have hcCall : Covers
      ((appTokens pre ++ appTokens post ++ beforeTokens ++
        mailboxTokens mailbox) ++ candidate.call.token :: afterTokens) a.net := by
    simpa [appTokens, appToken, Candidate.stageTokens,
      List.append_assoc] using hcover
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
  · let reply : ConcreteMessage := (.proc "s3", .proc address, .written op)
    let committed := storeCommit store candidate.req.key candidate.promise
    have hselected : NodeRep cfg committed address
        ⟨next, mailbox,
          writeK candidate.tries (candidate.call.retry candidate.tries)
            candidate op⟩
        (some reply)
        (mailboxTokens mailbox ++ candidate.stageTokens .served) := by
      simpa [committed, reply, hstoreAddr] using
        (NodeRep.writingServed
          (cfg := cfg) (store := committed) (address := address)
          (candidate := candidate) happ hnext hnone hvalid)
    have hnodes :=
      hbefore.commit.append (NodesRep.cons hselected hafter.commit)
    refine ⟨_, committed, beforeWires ++ [reply] ++ afterWires,
      beforeTokens ++
        (mailboxTokens mailbox ++ candidate.stageTokens .served) ++
        afterTokens, rfl, ?_, ?_, ?_, hstore',
      Nat.le_trans htime hstepTime⟩
    · simpa [reply, optionList, List.append_assoc] using hnodes
    · rw [hnet] at hprotocol
      have hbase :
          (protocolMessages pre ++ protocolMessages post).Perm
            (beforeWires ++ afterWires) := by
        apply perm_cancel_middle
          (value := ((.proc address, .proc "s3",
            .put op candidate.req.key candidate.promise
              (candidate.doc.map (·.2))) : ConcreteMessage))
        simpa [protocolMessages, List.append_assoc] using hprotocol
      simpa [reply, protocolMessages, List.append_assoc] using
        (perm_append_insert_middle hbase (added := [reply]))
    · have hcAdded := Covers.insert_both
        (left := appTokens pre ++ appTokens post ++ beforeTokens ++
          mailboxTokens mailbox)
        (right := afterTokens) (added := emitted) hcRest
      simpa [a', emitted, appTokens, appToken, List.append_assoc] using hcAdded

theorem normalRel_store_landedFailed
    {cfg : Storage.Config} {store : Store} {address : Addr}
    {beforeNodes afterNodes : List Addr}
    {beforeStates afterStates : List (Addr × Local)}
    {beforeWires afterWires : List ConcreteMessage}
    {beforeTokens afterTokens : List AbstractMessage}
    (hbefore : NodesRep cfg store beforeNodes beforeStates
      beforeWires beforeTokens)
    (hafter : NodesRep cfg store afterNodes afterStates
      afterWires afterTokens)
    {candidate : Candidate} {op next : Nat} {mailbox : List (Addr × CMsg)}
    (happ : AppOnly mailbox) (hnext : next = op + 1)
    (hnone : take? (answers op) mailbox = none)
    (hvalid : candidate.Valid cfg)
    (hsnapshot : Snapshot store candidate.req.key candidate.doc)
    (hmatch : candidate.doc.map (·.2) =
      (storeLookup store candidate.req.key).map (·.2))
    (hstoreAddr : cfg.store = "s3")
    {net : List ConcreteMessage} {now t : Time}
    {a : Experiment.Conf promises}
    (hprotocol : (protocolMessages net).Perm
      (beforeWires ++
        [((.proc address, .proc "s3",
          .put op candidate.req.key candidate.promise
            (candidate.doc.map (·.2))) : ConcreteMessage)] ++
        afterWires))
    (hcover : Covers
      (appTokens net ++ beforeTokens ++
        (mailboxTokens mailbox ++ candidate.stageTokens .pending) ++
        afterTokens) a.net)
    (hstore : StoreRep store a.state) (htime : a.now ≤ now)
    (hstepTime : now ≤ t) (pre post : List ConcreteMessage)
    (hnet : net = pre ++
      ((.proc address, .proc "s3",
        .put op candidate.req.key candidate.promise
          (candidate.doc.map (·.2))) : ConcreteMessage) :: post) :
    let committed := storeCommit store candidate.req.key candidate.promise
    let reply : ConcreteMessage := (.proc "s3", .proc address, .failed op)
    ∃ a',
      Network.Matches { cfg.app with unreliable := true } clientView a
        (.proc "s3", t, .receive (.proc address)
          (CMsg.put op candidate.req.key candidate.promise
            (candidate.doc.map (·.2)))) a' ∧
      NormalRel (beforeNodes ++ address :: afterNodes) cfg
        ⟨pre ++ post ++ [reply],
          (beforeStates ++
            (address, .node ⟨next, mailbox,
              writeK candidate.tries (candidate.call.retry candidate.tries)
                candidate op⟩) :: afterStates) ++
            [("s3", .store committed)], t⟩ a' := by
  dsimp
  rw [hnet] at hcover
  have hcCall : Covers
      ((appTokens pre ++ appTokens post ++ beforeTokens ++
        mailboxTokens mailbox) ++ candidate.call.token :: afterTokens) a.net := by
    simpa [appTokens, appToken, Candidate.stageTokens,
      List.append_assoc] using hcover
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
  · let reply : ConcreteMessage := (.proc "s3", .proc address, .failed op)
    let committed := storeCommit store candidate.req.key candidate.promise
    have hselected : NodeRep cfg committed address
        ⟨next, mailbox,
          writeK candidate.tries (candidate.call.retry candidate.tries)
            candidate op⟩
        (some reply)
        (mailboxTokens mailbox ++ candidate.stageTokens .lost) := by
      simpa [committed, reply, hstoreAddr] using
        (NodeRep.writingLost
          (cfg := cfg) (store := committed) (address := address)
          (candidate := candidate) happ hnext hnone hvalid)
    have hnodes :=
      hbefore.commit.append (NodesRep.cons hselected hafter.commit)
    refine ⟨_, committed, beforeWires ++ [reply] ++ afterWires,
      beforeTokens ++
        (mailboxTokens mailbox ++ candidate.stageTokens .lost) ++ afterTokens,
      rfl, ?_, ?_, ?_, hstore', Nat.le_trans htime hstepTime⟩
    · simpa [reply, optionList, List.append_assoc] using hnodes
    · rw [hnet] at hprotocol
      have hbase :
          (protocolMessages pre ++ protocolMessages post).Perm
            (beforeWires ++ afterWires) := by
        apply perm_cancel_middle
          (value := ((.proc address, .proc "s3",
            .put op candidate.req.key candidate.promise
              (candidate.doc.map (·.2))) : ConcreteMessage))
        simpa [protocolMessages, List.append_assoc] using hprotocol
      simpa [reply, protocolMessages, List.append_assoc] using
        (perm_append_insert_middle hbase (added := [reply]))
    · have hcAdded := Covers.insert_both
        (left := appTokens pre ++ appTokens post ++ beforeTokens ++
          mailboxTokens mailbox)
        (right := afterTokens) (added := emitted) hcRest
      simpa [a', emitted, appTokens, appToken, List.append_assoc] using hcAdded

theorem normalRel_store_failed
    {cfg : Storage.Config} {store : Store} {address : Addr}
    {beforeNodes afterNodes : List Addr}
    {beforeStates afterStates : List (Addr × Local)}
    {beforeWires afterWires : List ConcreteMessage}
    {beforeTokens afterTokens : List AbstractMessage}
    (hbefore : NodesRep cfg store beforeNodes beforeStates
      beforeWires beforeTokens)
    (hafter : NodesRep cfg store afterNodes afterStates
      afterWires afterTokens)
    {candidate : Candidate} {op next : Nat} {mailbox : List (Addr × CMsg)}
    (happ : AppOnly mailbox) (hnext : next = op + 1)
    (hnone : take? (answers op) mailbox = none)
    (hvalid : candidate.Valid cfg)
    (hsnapshot : Snapshot store candidate.req.key candidate.doc)
    (hstoreAddr : cfg.store = "s3")
    {net : List ConcreteMessage} {now t : Time}
    {a : Experiment.Conf promises}
    (hprotocol : (protocolMessages net).Perm
      (beforeWires ++
        [((.proc address, .proc "s3",
          .put op candidate.req.key candidate.promise
            (candidate.doc.map (·.2))) : ConcreteMessage)] ++
        afterWires))
    (hcover : Covers
      (appTokens net ++ beforeTokens ++
        (mailboxTokens mailbox ++ candidate.stageTokens .pending) ++
        afterTokens) a.net)
    (hstore : StoreRep store a.state) (htime : a.now ≤ now)
    (hstepTime : now ≤ t) (pre post : List ConcreteMessage)
    (hnet : net = pre ++
      ((.proc address, .proc "s3",
        .put op candidate.req.key candidate.promise
          (candidate.doc.map (·.2))) : ConcreteMessage) :: post) :
    let reply : ConcreteMessage := (.proc "s3", .proc address, .failed op)
    ∃ a',
      Network.Matches { cfg.app with unreliable := true } clientView a
        (.proc "s3", t, .receive (.proc address)
          (CMsg.put op candidate.req.key candidate.promise
            (candidate.doc.map (·.2)))) a' ∧
      NormalRel (beforeNodes ++ address :: afterNodes) cfg
        ⟨pre ++ post ++ [reply],
          (beforeStates ++
            (address, .node ⟨next, mailbox,
              writeK candidate.tries (candidate.call.retry candidate.tries)
                candidate op⟩) :: afterStates) ++
            [("s3", .store store)], t⟩ a' := by
  dsimp
  rw [hnet] at hcover
  have hcCall : Covers
      ((appTokens pre ++ appTokens post ++ beforeTokens ++
        mailboxTokens mailbox) ++ candidate.call.token :: afterTokens) a.net := by
    simpa [appTokens, appToken, Candidate.stageTokens,
      List.append_assoc] using hcover
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
  · let reply : ConcreteMessage := (.proc "s3", .proc address, .failed op)
    have hselected : NodeRep cfg store address
        ⟨next, mailbox,
          writeK candidate.tries (candidate.call.retry candidate.tries)
            candidate op⟩
        (some reply)
        (mailboxTokens mailbox ++ candidate.stageTokens .shed) := by
      simpa [reply, hstoreAddr] using
        (NodeRep.writingShed
          (cfg := cfg) (store := store) (address := address)
          (candidate := candidate) happ hnext hnone hvalid hsnapshot)
    have hnodes := hbefore.append (NodesRep.cons hselected hafter)
    refine ⟨_, store, beforeWires ++ [reply] ++ afterWires,
      beforeTokens ++
        (mailboxTokens mailbox ++ candidate.stageTokens .shed) ++ afterTokens,
      rfl, ?_, ?_, ?_, ?_, Nat.le_trans htime hstepTime⟩
    · simpa [reply, optionList, List.append_assoc] using hnodes
    · rw [hnet] at hprotocol
      have hbase :
          (protocolMessages pre ++ protocolMessages post).Perm
            (beforeWires ++ afterWires) := by
        apply perm_cancel_middle
          (value := ((.proc address, .proc "s3",
            .put op candidate.req.key candidate.promise
              (candidate.doc.map (·.2))) : ConcreteMessage))
        simpa [protocolMessages, List.append_assoc] using hprotocol
      simpa [reply, protocolMessages, List.append_assoc] using
        (perm_append_insert_middle hbase (added := [reply]))
    · have hcAdded := Covers.insert_both
        (left := appTokens pre ++ appTokens post ++ beforeTokens ++
          mailboxTokens mailbox)
        (right := afterTokens) (added := [response]) hcRest
      simpa [a', response, responseToken, Candidate.stageTokens,
        appTokens, appToken, List.append_assoc] using hcAdded
    · simpa [a', haeq] using hstore'

theorem normalRel_written
    {cfg : Storage.Config} {store : Store} {address : Addr}
    {beforeNodes afterNodes : List Addr}
    {beforeStates afterStates : List (Addr × Local)}
    {beforeWires afterWires : List ConcreteMessage}
    {beforeTokens afterTokens : List AbstractMessage}
    (hbefore : NodesRep cfg store beforeNodes beforeStates
      beforeWires beforeTokens)
    (hafter : NodesRep cfg store afterNodes afterStates
      afterWires afterTokens)
    {candidate : Candidate} {op next : Nat}
    {mailbox : List (Addr × CMsg)}
    (happ : AppOnly mailbox) (hnext : next = op + 1)
    (hnone : take? (answers op) mailbox = none)
    (hvalid : candidate.Valid cfg)
    (hstoreAddr : cfg.store = "s3")
    {net : List ConcreteMessage} {now t : Time}
    {a : Experiment.Conf promises}
    (hprotocol : (protocolMessages net).Perm
      (beforeWires ++
        [((.proc "s3", .proc address, .written op) : ConcreteMessage)] ++
        afterWires))
    (hcover : Covers
      (appTokens net ++ beforeTokens ++
        (mailboxTokens mailbox ++ candidate.stageTokens .served) ++
        afterTokens) a.net)
    (hstore : StoreRep store a.state) (htime : a.now ≤ now)
    (hstepTime : now ≤ t) (source : Network.Who)
    (pre post : List ConcreteMessage)
    (hnet : net = pre ++
      ((.proc "s3", .proc address, .written op) : ConcreteMessage) :: post) :
    ∃ running rest wire tokens,
      let states : List (Addr × Local) :=
        (beforeStates ++ (address, .node running) :: afterStates) ++
          [("s3", .store store)]
      let emitted : List (Out CMsg) :=
        .send candidate.client (.app (.res candidate.id candidate.res)) ::
          (sends candidate.outs).map
            (fun (destination, message) => .send destination (.app message)) ++
          rest
      (toStep node 64 source.addr (.written op) t cfg
        (⟨next, mailbox,
          writeK candidate.tries (candidate.call.retry candidate.tries)
            candidate op⟩ : Running Storage.Config Nat CMsg)).val =
          [((), running, emitted)] ∧
      RestartRep cfg store address running rest wire tokens ∧
      NormalRel (beforeNodes ++ address :: afterNodes) cfg
        ⟨pre ++ post ++ routedOuts states address emitted, states, t⟩ a := by
  obtain ⟨running, rest, wire, tokens, hrun, hrestart, htokens⟩ :=
    writing_written_restart (cfg := cfg) (store := store) (address := address)
      happ hnone source.addr t
  let states : List (Addr × Local) :=
    (beforeStates ++ (address, .node running) :: afterStates) ++
      [("s3", .store store)]
  let emittedPrefix : List (Out CMsg) :=
    [.send candidate.client (.app (.res candidate.id candidate.res))] ++
      (sends candidate.outs).map
        (fun (destination, message) => .send destination (.app message))
  let emitted : List (Out CMsg) := emittedPrefix ++ rest
  have hprefixProtocol :
      protocolMessages (routedOuts states address emittedPrefix) = [] := by
    rw [show emittedPrefix =
      [.send candidate.client (.app (.res candidate.id candidate.res))] ++
        (sends candidate.outs).map
          (fun (destination, message) => .send destination (.app message)) from rfl]
    rw [routedOuts_append, protocolMessages_append,
      protocolMessages_routedResponse, protocolMessages_routedOutputs]
    rfl
  have hprefixApp :
      appTokens (routedOuts states address emittedPrefix) =
        [responseToken candidate.client candidate.id candidate.res] ++
          outputTokens candidate.outs := by
    rw [show emittedPrefix =
      [.send candidate.client (.app (.res candidate.id candidate.res))] ++
        (sends candidate.outs).map
          (fun (destination, message) => .send destination (.app message)) from rfl]
    rw [routedOuts_append, appTokens_append, appTokens_routedResponse,
      appTokens_routedOutputs states address candidate.outs
        (Candidate.onlyNotifies (candidate := candidate) hvalid)]
  have hrouteStore :
      (⟨[], states, 0⟩ : Network.Conf system).route cfg.store =
        .proc cfg.store := by
    exact route_store_for_split_states hstoreAddr beforeStates afterStates
      address running store
  have hrouteProtocol :
      protocolMessages (routedOuts states address emitted) =
        optionList wire := by
    rw [show emitted = emittedPrefix ++ rest from rfl, routedOuts_append,
      protocolMessages_append, hprefixProtocol, List.nil_append]
    cases hrestart with
    | idle => rfl
    | loading =>
      simp [routedOuts, routedMessages, sends, protocolMessages,
        optionList, hrouteStore]
  have hrouteApp :
      appTokens (routedOuts states address emitted) =
        [responseToken candidate.client candidate.id candidate.res] ++
          outputTokens candidate.outs := by
    rw [show emitted = emittedPrefix ++ rest from rfl, routedOuts_append,
      appTokens_append, hprefixApp]
    cases hrestart <;>
      simp [routedOuts, routedMessages, sends, appTokens, appToken,
        hrouteStore]
  rw [hnet] at hprotocol hcover
  have hbase :
      (protocolMessages pre ++ protocolMessages post).Perm
        (beforeWires ++ afterWires) := by
    apply perm_cancel_middle
      (value := ((.proc "s3", .proc address, .written op) :
        ConcreteMessage))
    simpa [protocolMessages, List.append_assoc] using hprotocol
  have hprotocolFinal :
      (protocolMessages
        (pre ++ post ++ routedOuts states address emitted)).Perm
        (beforeWires ++ optionList wire ++ afterWires) := by
    rw [protocolMessages_append, protocolMessages_append, hrouteProtocol]
    exact perm_append_insert_middle hbase
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
      (appTokens pre ++ appTokens post ++ beforeTokens ++
        (mailboxTokens mailbox ++ candidate.stageTokens .served) ++
        afterTokens) a.net := by
    simpa [appTokens, appToken, List.append_assoc] using hcover
  have hcoverFinal : Covers
      (appTokens (pre ++ post ++ routedOuts states address emitted) ++
        beforeTokens ++ tokens ++ afterTokens) a.net := by
    rw [appTokens_append, appTokens_append, hrouteApp]
    apply Covers.of_perm _ hold
    exact perm_replace_middle_to_front hlocal
  have hnodes := hbefore.append (NodesRep.cons hrestart.nodeRep hafter)
  refine ⟨running, rest, wire, tokens, ?_, hrestart, ?_⟩
  · simpa [emitted, emittedPrefix, List.append_assoc] using hrun
  · refine ⟨beforeStates ++ (address, .node running) :: afterStates, store,
      beforeWires ++ optionList wire ++ afterWires,
      beforeTokens ++ tokens ++ afterTokens, rfl, ?_, ?_, ?_, hstore,
      Nat.le_trans htime hstepTime⟩
    · simpa [List.append_assoc] using hnodes
    · simpa [states, emitted, emittedPrefix, List.append_assoc] using
        hprotocolFinal
    · simpa [states, emitted, emittedPrefix, List.append_assoc] using
        hcoverFinal

theorem normalRel_failed
    {cfg : Storage.Config} {store : Store} {address : Addr}
    {beforeNodes afterNodes : List Addr}
    {beforeStates afterStates : List (Addr × Local)}
    {beforeWires afterWires : List ConcreteMessage}
    {beforeTokens afterTokens : List AbstractMessage}
    (hbefore : NodesRep cfg store beforeNodes beforeStates
      beforeWires beforeTokens)
    (hafter : NodesRep cfg store afterNodes afterStates
      afterWires afterTokens)
    {candidate : Candidate} {op next : Nat}
    {mailbox : List (Addr × CMsg)} {stage : WriteStage}
    (happ : AppOnly mailbox) (hnext : next = op + 1)
    (hnone : take? (answers op) mailbox = none)
    (hstage : stage = .shed ∨ stage = .lost)
    (hstoreAddr : cfg.store = "s3")
    {net : List ConcreteMessage} {now t : Time}
    {a : Experiment.Conf promises}
    (hprotocol : (protocolMessages net).Perm
      (beforeWires ++
        [((.proc "s3", .proc address, .failed op) : ConcreteMessage)] ++
        afterWires))
    (hcover : Covers
      (appTokens net ++ beforeTokens ++
        (mailboxTokens mailbox ++ candidate.stageTokens stage) ++
        afterTokens) a.net)
    (hstore : StoreRep store a.state) (htime : a.now ≤ now)
    (hstepTime : now ≤ t) (source : Network.Who)
    (pre post : List ConcreteMessage)
    (hnet : net = pre ++
      ((.proc "s3", .proc address, .failed op) : ConcreteMessage) :: post) :
    ∃ running rest wire tokens,
      let states : List (Addr × Local) :=
        (beforeStates ++ (address, .node running) :: afterStates) ++
          [("s3", .store store)]
      let emitted : List (Out CMsg) :=
        .send candidate.client (.app (.res candidate.id ⟨503, none⟩)) :: rest
      (toStep node 64 source.addr (.failed op) t cfg
        (⟨next, mailbox,
          writeK candidate.tries (candidate.call.retry candidate.tries)
            candidate op⟩ : Running Storage.Config Nat CMsg)).val =
          [((), running, emitted)] ∧
      RestartRep cfg store address running rest wire tokens ∧
      NormalRel (beforeNodes ++ address :: afterNodes) cfg
        ⟨pre ++ post ++ routedOuts states address emitted, states, t⟩ a := by
  obtain ⟨running, rest, wire, tokens, hrun, hrestart, htokens⟩ :=
    writing_failed_restart (cfg := cfg) (store := store) (address := address)
      happ hnone source.addr t
  let states : List (Addr × Local) :=
    (beforeStates ++ (address, .node running) :: afterStates) ++
      [("s3", .store store)]
  let emitted : List (Out CMsg) :=
    .send candidate.client (.app (.res candidate.id ⟨503, none⟩)) :: rest
  have hrouteStore :
      (⟨[], states, 0⟩ : Network.Conf system).route cfg.store =
        .proc cfg.store := by
    exact route_store_for_split_states hstoreAddr beforeStates afterStates
      address running store
  obtain ⟨hrouteProtocol, hrouteApp⟩ :=
    hrestart.routedResponse hrouteStore
      (client := candidate.client) (id := candidate.id)
      (response := ⟨503, none⟩)
  rw [hnet] at hprotocol hcover
  have hbase :
      (protocolMessages pre ++ protocolMessages post).Perm
        (beforeWires ++ afterWires) := by
    apply perm_cancel_middle
      (value := ((.proc "s3", .proc address, .failed op) :
        ConcreteMessage))
    simpa [protocolMessages, List.append_assoc] using hprotocol
  have hprotocolFinal :
      (protocolMessages
        (pre ++ post ++ routedOuts states address emitted)).Perm
        (beforeWires ++ optionList wire ++ afterWires) := by
    rw [protocolMessages_append, protocolMessages_append, hrouteProtocol]
    exact perm_append_insert_middle hbase
  have hold : Covers
      (appTokens pre ++ appTokens post ++ beforeTokens ++
        (mailboxTokens mailbox ++ candidate.stageTokens stage) ++
        afterTokens) a.net := by
    simpa [appTokens, appToken, List.append_assoc] using hcover
  have hcoverFinal : Covers
      (appTokens (pre ++ post ++ routedOuts states address emitted) ++
        beforeTokens ++ tokens ++ afterTokens) a.net := by
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
      apply Covers.of_perm _ hold
      simpa [Candidate.stageTokens, List.append_assoc] using
        (perm_replace_middle_to_front
          (base := appTokens pre ++ appTokens post)
          (before := beforeTokens)
          (old := mailboxTokens mailbox ++
            [responseToken candidate.client candidate.id ⟨503, none⟩])
          (after := afterTokens)
          (added :=
            [responseToken candidate.client candidate.id ⟨503, none⟩])
          (new := tokens) hlocal)
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
      have hplaced := perm_replace_middle_to_front
        (base := appTokens pre ++ appTokens post)
        (before := beforeTokens)
        (old := mailboxTokens mailbox ++ outputTokens candidate.outs ++
          [responseToken candidate.client candidate.id ⟨503, none⟩])
        (after := afterTokens)
        (added :=
          [responseToken candidate.client candidate.id ⟨503, none⟩])
        (new := tokens ++ outputTokens candidate.outs) hlocal
      have hmove :
          (appTokens pre ++ appTokens post ++
              [responseToken candidate.client candidate.id ⟨503, none⟩] ++
              beforeTokens ++ tokens ++ outputTokens candidate.outs ++
              afterTokens).Perm
            ((appTokens pre ++ appTokens post ++
              [responseToken candidate.client candidate.id ⟨503, none⟩] ++
              beforeTokens ++ tokens ++ afterTokens) ++
              outputTokens candidate.outs) := by
        simpa [List.append_assoc] using
          (List.Perm.append_left
            (appTokens pre ++ appTokens post ++
              [responseToken candidate.client candidate.id ⟨503, none⟩] ++
              beforeTokens ++ tokens)
            (List.perm_append_comm :
              (outputTokens candidate.outs ++ afterTokens).Perm
                (afterTokens ++ outputTokens candidate.outs)))
      have hmove' :
          (appTokens pre ++ appTokens post ++
              [responseToken candidate.client candidate.id ⟨503, none⟩] ++
              beforeTokens ++ (tokens ++ outputTokens candidate.outs) ++
              afterTokens).Perm
            ((appTokens pre ++ appTokens post ++
              [responseToken candidate.client candidate.id ⟨503, none⟩] ++
              beforeTokens ++ tokens ++ afterTokens) ++
              outputTokens candidate.outs) := by
        simpa [List.append_assoc] using hmove
      apply Covers.weaken (extra := outputTokens candidate.outs)
      apply Covers.of_perm _ hold
      simpa [Candidate.stageTokens, List.append_assoc] using
        hplaced.trans hmove'
  have hnodes := hbefore.append (NodesRep.cons hrestart.nodeRep hafter)
  refine ⟨running, rest, wire, tokens, ?_, hrestart, ?_⟩
  · simpa [emitted] using hrun
  · refine ⟨beforeStates ++ (address, .node running) :: afterStates, store,
      beforeWires ++ optionList wire ++ afterWires,
      beforeTokens ++ tokens ++ afterTokens, rfl, ?_, ?_, ?_, hstore,
      Nat.le_trans htime hstepTime⟩
    · simpa [List.append_assoc] using hnodes
    · simpa [states, emitted, List.append_assoc] using hprotocolFinal
    · simpa [states, emitted, List.append_assoc] using hcoverFinal

theorem normalRel_conflict_exhausted
    {cfg : Storage.Config} {store : Store} {address : Addr}
    {beforeNodes afterNodes : List Addr}
    {beforeStates afterStates : List (Addr × Local)}
    {beforeWires afterWires : List ConcreteMessage}
    {beforeTokens afterTokens : List AbstractMessage}
    (hbefore : NodesRep cfg store beforeNodes beforeStates
      beforeWires beforeTokens)
    (hafter : NodesRep cfg store afterNodes afterStates
      afterWires afterTokens)
    {candidate : Candidate} {op next : Nat}
    {mailbox : List (Addr × CMsg)}
    (happ : AppOnly mailbox) (hnext : next = op + 1)
    (hnone : take? (answers op) mailbox = none)
    (htries : candidate.tries = 0)
    (hstoreAddr : cfg.store = "s3")
    {net : List ConcreteMessage} {now t : Time}
    {a : Experiment.Conf promises}
    (hprotocol : (protocolMessages net).Perm
      (beforeWires ++
        [((.proc "s3", .proc address, .conflict op) : ConcreteMessage)] ++
        afterWires))
    (hcover : Covers
      (appTokens net ++ beforeTokens ++
        (mailboxTokens mailbox ++ candidate.stageTokens .pending) ++
        afterTokens) a.net)
    (hstore : StoreRep store a.state) (htime : a.now ≤ now)
    (hstepTime : now ≤ t) (source : Network.Who)
    (pre post : List ConcreteMessage)
    (hnet : net = pre ++
      ((.proc "s3", .proc address, .conflict op) : ConcreteMessage) :: post) :
    ∃ a' running rest wire tokens,
      let states : List (Addr × Local) :=
        (beforeStates ++ (address, .node running) :: afterStates) ++
          [("s3", .store store)]
      let emitted : List (Out CMsg) :=
        .send candidate.client (.app (.res candidate.id ⟨503, none⟩)) :: rest
      Network.Matches { cfg.app with unreliable := true } clientView a
        (.proc address, t, .receive source (CMsg.conflict op)) a' ∧
      (toStep node 64 source.addr (.conflict op) t cfg
        (⟨next, mailbox,
          writeK candidate.tries (candidate.call.retry candidate.tries)
            candidate op⟩ : Running Storage.Config Nat CMsg)).val =
          [((), running, emitted)] ∧
      RestartRep cfg store address running rest wire tokens ∧
      NormalRel (beforeNodes ++ address :: afterNodes) cfg
        ⟨pre ++ post ++ routedOuts states address emitted, states, t⟩ a' := by
  rw [hnet] at hcover
  have hcCall : Covers
      ((appTokens pre ++ appTokens post ++ beforeTokens ++
          mailboxTokens mailbox) ++ candidate.call.token :: afterTokens)
      a.net := by
    simpa [appTokens, appToken, Candidate.stageTokens,
      List.append_assoc] using hcover
  obtain ⟨apre, apost, hanet, hcRest⟩ := Covers.consume hcCall
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
      (cfg := cfg) (store := store) (address := address)
      happ hnone htries source.addr t
  let states : List (Addr × Local) :=
    (beforeStates ++ (address, .node running) :: afterStates) ++
      [("s3", .store store)]
  let emitted : List (Out CMsg) :=
    .send candidate.client (.app (.res candidate.id ⟨503, none⟩)) :: rest
  have hrouteStore :
      (⟨[], states, 0⟩ : Network.Conf system).route cfg.store =
        .proc cfg.store := by
    exact route_store_for_split_states hstoreAddr beforeStates afterStates
      address running store
  obtain ⟨hrouteProtocol, hrouteApp⟩ :=
    hrestart.routedResponse hrouteStore
      (client := candidate.client) (id := candidate.id)
      (response := ⟨503, none⟩)
  rw [hnet] at hprotocol
  have hbase :
      (protocolMessages pre ++ protocolMessages post).Perm
        (beforeWires ++ afterWires) := by
    apply perm_cancel_middle
      (value := ((.proc "s3", .proc address, .conflict op) :
        ConcreteMessage))
    simpa [protocolMessages, List.append_assoc] using hprotocol
  have hprotocolFinal :
      (protocolMessages
        (pre ++ post ++ routedOuts states address emitted)).Perm
        (beforeWires ++ optionList wire ++ afterWires) := by
    rw [protocolMessages_append, protocolMessages_append, hrouteProtocol]
    exact perm_append_insert_middle hbase
  have hcAdded := Covers.insert_both
    (left := appTokens pre ++ appTokens post ++ beforeTokens ++
      mailboxTokens mailbox)
    (right := afterTokens) (added := [response]) hcRest
  have hcoverFinal : Covers
      (appTokens (pre ++ post ++ routedOuts states address emitted) ++
        beforeTokens ++ tokens ++ afterTokens) a'.net := by
    rw [appTokens_append, appTokens_append, hrouteApp]
    apply Covers.of_perm _ hcAdded
    have hlocal :
        (mailboxTokens mailbox ++ [response]).Perm
          ([response] ++ tokens) :=
      List.perm_append_comm.trans
        (List.Perm.append_left [response] htokens.symm)
    simpa [a', List.append_assoc] using
      (perm_replace_middle_to_front
        (base := appTokens pre ++ appTokens post)
        (before := beforeTokens)
        (old := mailboxTokens mailbox ++ [response])
        (after := afterTokens) (added := [response]) (new := tokens) hlocal)
  have hnodes := hbefore.append (NodesRep.cons hrestart.nodeRep hafter)
  refine ⟨a', running, rest, wire, tokens, ?_, ?_, hrestart, ?_⟩
  · refine ⟨[((.server, a.now,
      .receive (.client candidate.client)
        (Msg.req candidate.id candidate.now candidate.req)),
      [.send candidate.client (Msg.res candidate.id ⟨503, none⟩)], a')],
      ?_, hobs, rfl⟩
    simpa [haeq] using hlegal
  · simpa [emitted] using hrun
  · refine ⟨beforeStates ++ (address, .node running) :: afterStates, store,
      beforeWires ++ optionList wire ++ afterWires,
      beforeTokens ++ tokens ++ afterTokens, rfl, ?_, ?_, ?_, ?_,
      Nat.le_trans htime hstepTime⟩
    · simpa [List.append_assoc] using hnodes
    · simpa [states, emitted, List.append_assoc] using hprotocolFinal
    · simpa [states, emitted, List.append_assoc] using hcoverFinal
    · simpa [a', haeq] using hstore'

theorem normalRel_got_done
    {cfg : Storage.Config} {store : Store} {address : Addr}
    {beforeNodes afterNodes : List Addr}
    {beforeStates afterStates : List (Addr × Local)}
    {beforeWires afterWires : List ConcreteMessage}
    {beforeTokens afterTokens : List AbstractMessage}
    (hbefore : NodesRep cfg store beforeNodes beforeStates
      beforeWires beforeTokens)
    (hafter : NodesRep cfg store afterNodes afterStates
      afterWires afterTokens)
    {call : Call} {tries op next : Nat} {mailbox : List (Addr × CMsg)}
    {doc : Option (Promise × Version)} {res : Response}
    {after : Experiment.State} {outs : List (Out Msg)}
    (happ : AppOnly mailbox) (hnext : next = op + 1)
    (hnone : take? (answers op) mailbox = none)
    (hpick :
      pick ((Experiment.dispatch call.req call.now).run
        { cfg.app with unreliable := true }
        { promises := doc.toList.map (·.1) }) 0 = (res, after, outs))
    (hunchanged : after = { promises := doc.toList.map (·.1) })
    (hstoreAddr : cfg.store = "s3")
    {net : List ConcreteMessage} {now t : Time}
    {a : Experiment.Conf promises}
    (hprotocol : (protocolMessages net).Perm
      (beforeWires ++
        [((.proc "s3", .proc address, .got op doc) : ConcreteMessage)] ++
        afterWires))
    (hcover : Covers
      (appTokens net ++ beforeTokens ++
        (mailboxTokens mailbox ++ outputTokens outs ++
          [responseToken call.client call.id res]) ++ afterTokens) a.net)
    (hstore : StoreRep store a.state) (htime : a.now ≤ now)
    (hstepTime : now ≤ t) (source : Network.Who)
    (pre post : List ConcreteMessage)
    (hnet : net = pre ++
      ((.proc "s3", .proc address, .got op doc) : ConcreteMessage) :: post) :
    ∃ running rest wire tokens,
      let states : List (Addr × Local) :=
        (beforeStates ++ (address, .node running) :: afterStates) ++
          [("s3", .store store)]
      let emitted : List (Out CMsg) :=
        notes outs ++
          .send call.client (.app (.res call.id res)) ::
            (sends outs).map (fun (destination, message) =>
              .send destination (.app message)) ++ rest
      (toStep node 64 source.addr (.got op doc) t cfg
        (⟨next, mailbox,
          loadK tries (call.retry tries)
            call.client call.id call.req call.now op⟩ :
          Running Storage.Config Nat CMsg)).val =
          [((), running, emitted)] ∧
      RestartRep cfg store address running rest wire tokens ∧
      NormalRel (beforeNodes ++ address :: afterNodes) cfg
        ⟨pre ++ post ++ routedOuts states address emitted, states, t⟩ a := by
  obtain ⟨running, rest, wire, tokens, hrun, hrestart, htokens⟩ :=
    loading_got_unchanged_restart
      (cfg := cfg) (store := store) (address := address)
      happ hnone hpick hunchanged source.addr t
  let states : List (Addr × Local) :=
    (beforeStates ++ (address, .node running) :: afterStates) ++
      [("s3", .store store)]
  let emittedPrefix : List (Out CMsg) :=
    [.send call.client (.app (.res call.id res))] ++
      (sends outs).map
        (fun (destination, message) => .send destination (.app message))
  let emitted : List (Out CMsg) := notes outs ++ emittedPrefix ++ rest
  have hprefixProtocol :
      protocolMessages (routedOuts states address emittedPrefix) = [] := by
    rw [show emittedPrefix =
      [.send call.client (.app (.res call.id res))] ++
        (sends outs).map
          (fun (destination, message) => .send destination (.app message)) from rfl]
    rw [routedOuts_append, protocolMessages_append,
      protocolMessages_routedResponse, protocolMessages_routedOutputs]
    rfl
  have hprefixApp :
      appTokens (routedOuts states address emittedPrefix) =
        [responseToken call.client call.id res] ++ outputTokens outs := by
    rw [show emittedPrefix =
      [.send call.client (.app (.res call.id res))] ++
        (sends outs).map
          (fun (destination, message) => .send destination (.app message)) from rfl]
    rw [routedOuts_append, appTokens_append, appTokens_routedResponse,
      appTokens_routedOutputs states address outs
        (dispatch_onlyNotifies (cfg := cfg) hpick)]
  have hrouteStore :
      (⟨[], states, 0⟩ : Network.Conf system).route cfg.store =
        .proc cfg.store := by
    exact route_store_for_split_states hstoreAddr beforeStates afterStates
      address running store
  have hrouteProtocol :
      protocolMessages (routedOuts states address emitted) =
        optionList wire := by
    rw [show emitted = notes outs ++ (emittedPrefix ++ rest) by
          simp [emitted, List.append_assoc],
      routedOuts_append, routedOuts_notes, List.nil_append,
      routedOuts_append, protocolMessages_append, hprefixProtocol,
      List.nil_append]
    cases hrestart with
    | idle => rfl
    | loading =>
      simp [routedOuts, routedMessages, sends, protocolMessages,
        optionList, hrouteStore]
  have hrouteApp :
      appTokens (routedOuts states address emitted) =
        [responseToken call.client call.id res] ++ outputTokens outs := by
    rw [show emitted = notes outs ++ (emittedPrefix ++ rest) by
          simp [emitted, List.append_assoc],
      routedOuts_append, routedOuts_notes, List.nil_append,
      routedOuts_append, appTokens_append, hprefixApp]
    cases hrestart <;>
      simp [routedOuts, routedMessages, sends, appTokens, appToken,
        hrouteStore]
  rw [hnet] at hprotocol hcover
  have hbase :
      (protocolMessages pre ++ protocolMessages post).Perm
        (beforeWires ++ afterWires) := by
    apply perm_cancel_middle
      (value := ((.proc "s3", .proc address, .got op doc) :
        ConcreteMessage))
    simpa [protocolMessages, List.append_assoc] using hprotocol
  have hprotocolFinal :
      (protocolMessages
        (pre ++ post ++ routedOuts states address emitted)).Perm
        (beforeWires ++ optionList wire ++ afterWires) := by
    rw [protocolMessages_append, protocolMessages_append, hrouteProtocol]
    exact perm_append_insert_middle hbase
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
      (appTokens pre ++ appTokens post ++ beforeTokens ++
        (mailboxTokens mailbox ++ outputTokens outs ++
          [responseToken call.client call.id res]) ++ afterTokens) a.net := by
    simpa [appTokens, appToken, List.append_assoc] using hcover
  have hcoverFinal : Covers
      (appTokens (pre ++ post ++ routedOuts states address emitted) ++
        beforeTokens ++ tokens ++ afterTokens) a.net := by
    rw [appTokens_append, appTokens_append, hrouteApp]
    apply Covers.of_perm _ hold
    exact perm_replace_middle_to_front
      (base := appTokens pre ++ appTokens post)
      (before := beforeTokens)
      (old := mailboxTokens mailbox ++ outputTokens outs ++
        [responseToken call.client call.id res])
      (after := afterTokens)
      (added := [responseToken call.client call.id res] ++ outputTokens outs)
      (new := tokens) hlocal
  have hnodes := hbefore.append (NodesRep.cons hrestart.nodeRep hafter)
  refine ⟨running, rest, wire, tokens, ?_, hrestart, ?_⟩
  · simpa [emitted, emittedPrefix, List.append_assoc] using hrun
  · refine ⟨beforeStates ++ (address, .node running) :: afterStates, store,
      beforeWires ++ optionList wire ++ afterWires,
      beforeTokens ++ tokens ++ afterTokens, rfl, ?_, ?_, ?_, hstore,
      Nat.le_trans htime hstepTime⟩
    · simpa [List.append_assoc] using hnodes
    · simpa [states, emitted, emittedPrefix, List.append_assoc] using
        hprotocolFinal
    · simpa [states, emitted, emittedPrefix, List.append_assoc] using
        hcoverFinal

attribute [local simp] Network.Conf.route Network.Conf.isProc

set_option maxHeartbeats 3000000 in
theorem storage_simulationOn {nodes : List Addr} {cfg : Storage.Config}
    (hnodup : nodes.Nodup) (hphysical : "s3" ∉ nodes)
    (hconditional : cfg.conditional = true) (hstoreAddr : cfg.store = "s3") :
    Network.SimulationOn cfg { cfg.app with unreliable := true }
      clientView DriveSafe (NormalRel nodes cfg) := by
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
        let a' : Experiment.Conf promises :=
          ⟨a.net ++ [(.client client, .server, message)], a.state, t⟩
        refine ⟨a', matches_client_request
          (Nat.le_trans hrel.time hstepTime), ?_⟩
        exact hrel.clientRequest client to t message
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
            (Nat.le_trans hrel.time hstepTime) hanet, ?_⟩
          simpa [a', herase] using hrel'
        | get op key =>
          obtain ⟨nodeStates, store, wires, tokens, hstates, hnodes,
            hprotocol, hcover, hstore, htime⟩ := hrel
          have hm : (from_, .client client, CMsg.get op key) ∈
              protocolMessages c.net := by
            rw [hnet]
            simp [protocolMessages]
          have hwm := (hprotocol.mem_iff).1 hm
          obtain ⟨source, dest, m, heq⟩ :=
            hnodes.protocol_is_between_procs hwm
          cases heq
        | put op key promise ifMatch =>
          obtain ⟨nodeStates, store, wires, tokens, hstates, hnodes,
            hprotocol, hcover, hstore, htime⟩ := hrel
          have hm : (from_, .client client, CMsg.put op key promise ifMatch) ∈
              protocolMessages c.net := by
            rw [hnet]
            simp [protocolMessages]
          have hwm := (hprotocol.mem_iff).1 hm
          obtain ⟨source, dest, m, heq⟩ :=
            hnodes.protocol_is_between_procs hwm
          cases heq
        | got op doc =>
          obtain ⟨nodeStates, store, wires, tokens, hstates, hnodes,
            hprotocol, hcover, hstore, htime⟩ := hrel
          have hm : (from_, .client client, CMsg.got op doc) ∈
              protocolMessages c.net := by
            rw [hnet]
            simp [protocolMessages]
          have hwm := (hprotocol.mem_iff).1 hm
          obtain ⟨source, dest, m, heq⟩ :=
            hnodes.protocol_is_between_procs hwm
          cases heq
        | written op =>
          obtain ⟨nodeStates, store, wires, tokens, hstates, hnodes,
            hprotocol, hcover, hstore, htime⟩ := hrel
          have hm : (from_, .client client, CMsg.written op) ∈
              protocolMessages c.net := by
            rw [hnet]
            simp [protocolMessages]
          have hwm := (hprotocol.mem_iff).1 hm
          obtain ⟨source, dest, m, heq⟩ :=
            hnodes.protocol_is_between_procs hwm
          cases heq
        | conflict op =>
          obtain ⟨nodeStates, store, wires, tokens, hstates, hnodes,
            hprotocol, hcover, hstore, htime⟩ := hrel
          have hm : (from_, .client client, CMsg.conflict op) ∈
              protocolMessages c.net := by
            rw [hnet]
            simp [protocolMessages]
          have hwm := (hprotocol.mem_iff).1 hm
          obtain ⟨source, dest, m, heq⟩ :=
            hnodes.protocol_is_between_procs hwm
          cases heq
        | failed op =>
          obtain ⟨nodeStates, store, wires, tokens, hstates, hnodes,
            hprotocol, hcover, hstore, htime⟩ := hrel
          have hm : (from_, .client client, CMsg.failed op) ∈
              protocolMessages c.net := by
            rw [hnet]
            simp [protocolMessages]
          have hwm := (hprotocol.mem_iff).1 hm
          obtain ⟨source, dest, m, heq⟩ :=
            hnodes.protocol_is_between_procs hwm
          cases heq
      next from_ proc message hmessage =>
        obtain ⟨nodeStates, store, wires, tokens, hstates, hnodes,
          hprotocol, hcover, hstore, htime⟩ := hrel
        obtain ⟨pre, post, hnet, herase⟩ :=
          split_of_get?_eq_some hmessage
        by_cases hproc : proc ∈ nodes
        · let focus := hnodes.focus hproc
          have hcstate : c.state? proc = some (.node focus.running) := by
            rw [Network.Conf.state?, hstates]
            exact focus.state_at_with_store hnodup
          have hroute (running : Running Storage.Config Nat CMsg)
              (destination : Addr) :
              c.route destination =
                (⟨[],
                  (focus.beforeStates ++
                    (proc, .node running) :: focus.afterStates) ++
                    [("s3", .store store)], 0⟩ :
                  Network.Conf system).route destination := by
            change
              (⟨[], c.states, 0⟩ : Network.Conf system).route destination =
                _
            rw [hstates, ← focus.map_update hnodup hphysical running]
            exact route_map_update _ proc destination (.node running)
          have finishNode {running : Running Storage.Config Nat CMsg}
              {outs : List (Out CMsg)}
              (hrun :
                system.step cfg (.node focus.running) t
                    (.msg from_.addr message) =
                  Some.one (.node running, outs)) :
              c.run cfg proc t (.msg from_.addr message) choice
                  (c.net.eraseIdx index) =
                some (outs,
                  ⟨pre ++ post ++ routedOuts
                      ((focus.beforeStates ++
                        (proc, .node running) :: focus.afterStates) ++
                        [("s3", .store store)]) proc outs,
                    (focus.beforeStates ++
                      (proc, .node running) :: focus.afterStates) ++
                      [("s3", .store store)], t⟩) := by
            have hmap := focus.map_update hnodup hphysical running
            have hrouted :
                (sends outs).map (fun x =>
                  (.proc proc, c.route x.1, x.2)) =
                  routedOuts
                    ((focus.beforeStates ++
                      (proc, .node running) :: focus.afterStates) ++
                      [("s3", .store store)]) proc outs := by
              unfold routedOuts routedMessages
              apply List.map_congr_left
              intro output _
              obtain ⟨destination, payload⟩ := output
              congr 2
              change c.route destination = _
              exact hroute running destination
            unfold Network.Conf.run
            rw [hcstate]
            simp only [Option.map_some]
            rw [show pick
                (system.step cfg (.node focus.running) t
                  (.msg from_.addr message)) choice =
                (.node running, outs) by
              rw [hrun]
              simp [Experiment.pick, Some.one]]
            rw [herase, hstates, hmap]
            rw [hrouted]
          have selected := focus.selected
          generalize hrunning : focus.running = representedRunning at selected
          generalize hwire : focus.wire = representedWire at selected
          generalize htokens : focus.nodeTokens = representedTokens at selected
          cases message with
          | app message =>
            cases message with
            | res id response =>
              obtain ⟨running, hrun, hrel'⟩ :=
                normalRel_nonrequest focus hprotocol hcover hstore htime
                  from_ (.res id response) hstepTime rfl pre post hnet
              have hservice := node_service_step_singleton hrun
              have hservice' :
                  system.step cfg (.node focus.running) t
                    (.msg from_.addr (.app (.res id response))) =
                    Some.one (.node running, []) := Subtype.ext hservice
              rw [finishNode hservice'] at htake
              simp only [Option.some.injEq, Prod.mk.injEq] at htake
              obtain ⟨rfl, rfl, rfl⟩ := htake
              refine ⟨a, matches_hidden rfl, ?_⟩
              simpa [routedOuts, routedMessages, List.append_assoc,
                sends_notes] using hrel'
            | notify promise =>
              obtain ⟨running, hrun, hrel'⟩ :=
                normalRel_nonrequest focus hprotocol hcover hstore htime
                  from_ (.notify promise) hstepTime rfl pre post hnet
              have hservice := node_service_step_singleton hrun
              have hservice' :
                  system.step cfg (.node focus.running) t
                    (.msg from_.addr (.app (.notify promise))) =
                    Some.one (.node running, []) := Subtype.ext hservice
              rw [finishNode hservice'] at htake
              simp only [Option.some.injEq, Prod.mk.injEq] at htake
              obtain ⟨rfl, rfl, rfl⟩ := htake
              refine ⟨a, matches_hidden rfl, ?_⟩
              simpa [routedOuts, routedMessages, List.append_assoc,
                sends_notes] using hrel'
            | req id requestNow request =>
              by_cases hbusy : focus.wire ≠ none
              · obtain ⟨running, hrun, hrel'⟩ :=
                  normalRel_request_busy focus hbusy hprotocol hcover
                    hstore htime from_ id requestNow request hstepTime
                    pre post hnet
                have hservice := node_service_step_singleton hrun
                have hservice' :
                    system.step cfg (.node focus.running) t
                      (.msg from_.addr (.app (.req id requestNow request))) =
                      Some.one (.node running, []) := Subtype.ext hservice
                rw [finishNode hservice'] at htake
                simp only [Option.some.injEq, Prod.mk.injEq] at htake
                obtain ⟨rfl, rfl, rfl⟩ := htake
                refine ⟨a, matches_hidden rfl, ?_⟩
                simpa [routedOuts, routedMessages, List.append_assoc,
                  sends_notes] using hrel'
              · have hw : focus.wire = none := Classical.not_not.mp hbusy
                cases selected with
                | @idle next mailbox happ hn =>
                  obtain ⟨hrun, hrel'⟩ :=
                    normalRel_request_idle focus.before focus.after
                      (next := next) happ hn hstoreAddr
                      (by simpa [focus.wires_eq, hw, hwire, optionList,
                        List.append_assoc] using hprotocol)
                      (by simpa [focus.tokens_eq, htokens,
                        List.append_assoc] using hcover)
                      hstore htime from_ id requestNow request hstepTime
                      pre post hnet
                  have hservice := node_service_step_singleton hrun
                  have hservice' :
                      system.step cfg (.node focus.running) t
                        (.msg from_.addr (.app (.req id requestNow request))) =
                        Some.one
                          (.node ⟨next + 1, mailbox,
                            loadK cfg.retries
                              (Call.retry
                                ⟨from_.addr, id, request, requestNow⟩
                                cfg.retries)
                              from_.addr id request requestNow next⟩,
                            [.send "s3" (.get next request.key)]) := by
                    apply Subtype.eq
                    rw [hrunning]
                    exact hservice
                  rw [finishNode hservice'] at htake
                  simp only [Option.some.injEq, Prod.mk.injEq] at htake
                  obtain ⟨rfl, rfl, rfl⟩ := htake
                  refine ⟨a, matches_hidden rfl, ?_⟩
                  simpa [focus.nodes_eq, routedOuts, routedMessages, sends,
                    Network.Conf.route, Network.Conf.isProc,
                    List.append_assoc] using hrel'
                | loadingGet => simp [hw] at hwire
                | loadingGot => simp [hw] at hwire
                | loadingDone => simp [hw] at hwire
                | writingPut => simp [hw] at hwire
                | writingConflict => simp [hw] at hwire
                | writingServed => simp [hw] at hwire
                | writingLost => simp [hw] at hwire
                | writingShed => simp [hw] at hwire
          | get op key =>
            have hm : (from_, .proc proc, CMsg.get op key) ∈
                protocolMessages c.net := by rw [hnet]; simp [protocolMessages]
            have hw := focus.wire_to hnodup hstoreAddr hphysical
              ((hprotocol.mem_iff).1 hm)
            cases selected <;>
              simp_all [hstoreAddr]
          | put op key promise ifMatch =>
            have hm : (from_, .proc proc, CMsg.put op key promise ifMatch) ∈
                protocolMessages c.net := by rw [hnet]; simp [protocolMessages]
            have hw := focus.wire_to hnodup hstoreAddr hphysical
              ((hprotocol.mem_iff).1 hm)
            cases selected <;>
              simp_all [hstoreAddr]
          | got op doc =>
            have hm : (from_, .proc proc, CMsg.got op doc) ∈
                protocolMessages c.net := by rw [hnet]; simp [protocolMessages]
            have hw := focus.wire_to hnodup hstoreAddr hphysical
              ((hprotocol.mem_iff).1 hm)
            cases selected with
            | idle => simp [hw] at hwire
            | loadingGet => simp [hw, hstoreAddr] at hwire
            | @loadingGot call tries loadedOp next mailbox loadedDoc
                happ hnext hn hchanged hs hd =>
              have hw' := hwire.symm.trans hw
              have hfrom := source_eq_s3_of_inbound_wire hstoreAddr hw'
              subst from_
              have hmsg := congrArg (fun x : ConcreteMessage => x.2.2)
                (Option.some.inj hw')
              injection hmsg with hop hdoc
              subst op
              subst doc
              obtain ⟨res, after, outs, hpick, hchanged⟩ := hchanged
              obtain ⟨promise, hpromise⟩ :=
                dispatch_changed_has_promise hd hpick hchanged
              obtain ⟨hrun, hrel'⟩ :=
                normalRel_got_changed focus.before focus.after happ hn
                  hpick (beq_eq_false_iff_ne.mpr hchanged) hpromise hs hd
                  hstoreAddr
                  (by simpa [focus.wires_eq, hwire, hstoreAddr, optionList,
                    List.append_assoc] using hprotocol)
                  (by simpa [focus.tokens_eq, htokens,
                    List.append_assoc] using hcover)
                  hstore htime hstepTime (.proc "s3") pre post hnet
              have hservice := node_service_step_singleton hrun
              have hservice' := some_eq_one_of_val_eq hservice
              rw [← hrunning] at hservice'
              rw [finishNode hservice'] at htake
              simp only [Option.some.injEq, Prod.mk.injEq] at htake
              obtain ⟨rfl, rfl, rfl⟩ := htake
              refine ⟨a, matches_hidden rfl, ?_⟩
              simpa [focus.nodes_eq, routedOuts, routedMessages,
                List.append_assoc, sends_notes] using hrel'
            | @loadingDone call tries loadedOp next mailbox loadedDoc
                res after outs happ hnext hn hpick hunchanged hs hd =>
              have hw' := hwire.symm.trans hw
              have hfrom := source_eq_s3_of_inbound_wire hstoreAddr hw'
              subst from_
              have hmsg := congrArg (fun x : ConcreteMessage => x.2.2)
                (Option.some.inj hw')
              injection hmsg with hop hdoc
              subst op
              subst doc
              obtain ⟨running, rest, wire, nodeTokens, hrun, hrestart, hrel'⟩ :=
                normalRel_got_done focus.before focus.after happ hnext hn
                  hpick hunchanged hstoreAddr
                  (by simpa [focus.wires_eq, hwire, hstoreAddr, optionList,
                    List.append_assoc] using hprotocol)
                  (by simpa [focus.tokens_eq, htokens,
                    List.append_assoc] using hcover)
                  hstore htime hstepTime (.proc "s3") pre post hnet
              have hservice := node_service_step_singleton hrun
              have hservice' := some_eq_one_of_val_eq hservice
              rw [← hrunning] at hservice'
              rw [finishNode hservice'] at htake
              simp only [Option.some.injEq, Prod.mk.injEq] at htake
              obtain ⟨rfl, rfl, rfl⟩ := htake
              refine ⟨a, matches_hidden rfl, ?_⟩
              simpa [focus.nodes_eq, List.append_assoc] using hrel'
            | writingPut => simp [hw, hstoreAddr] at hwire
            | writingConflict => simp [hw] at hwire
            | writingServed => simp [hw] at hwire
            | writingLost => simp [hw] at hwire
            | writingShed => simp [hw] at hwire
          | written op =>
            have hm : (from_, .proc proc, CMsg.written op) ∈
                protocolMessages c.net := by rw [hnet]; simp [protocolMessages]
            have hw := focus.wire_to hnodup hstoreAddr hphysical
              ((hprotocol.mem_iff).1 hm)
            cases selected with
            | @writingServed candidate loadedOp next mailbox
                happ hnext hn hvalid =>
              have hw' := hwire.symm.trans hw
              have hfrom := source_eq_s3_of_inbound_wire hstoreAddr hw'
              subst from_
              have hmsg := congrArg (fun x : ConcreteMessage => x.2.2)
                (Option.some.inj hw')
              injection hmsg with hop
              subst op
              obtain ⟨running, rest, wire, nodeTokens, hrun, hrestart, hrel'⟩ :=
                normalRel_written focus.before focus.after happ hnext hn
                  hvalid hstoreAddr
                  (by simpa [focus.wires_eq, hwire, hstoreAddr, optionList,
                    List.append_assoc] using hprotocol)
                  (by simpa [focus.tokens_eq, htokens,
                    List.append_assoc] using hcover)
                  hstore htime hstepTime (.proc "s3") pre post hnet
              have hservice := node_service_step_singleton hrun
              have hservice' := some_eq_one_of_val_eq hservice
              rw [← hrunning] at hservice'
              rw [finishNode hservice'] at htake
              simp only [Option.some.injEq, Prod.mk.injEq] at htake
              obtain ⟨rfl, rfl, rfl⟩ := htake
              refine ⟨a, matches_hidden rfl, ?_⟩
              simpa [focus.nodes_eq, List.append_assoc] using hrel'
            | idle => simp [hw] at hwire
            | loadingGet => simp [hw, hstoreAddr] at hwire
            | loadingGot => simp [hw] at hwire
            | loadingDone => simp [hw] at hwire
            | writingPut => simp [hw, hstoreAddr] at hwire
            | writingConflict => simp [hw] at hwire
            | writingLost => simp [hw] at hwire
            | writingShed => simp [hw] at hwire
          | conflict op =>
            have hm : (from_, .proc proc, CMsg.conflict op) ∈
                protocolMessages c.net := by rw [hnet]; simp [protocolMessages]
            have hw := focus.wire_to hnodup hstoreAddr hphysical
              ((hprotocol.mem_iff).1 hm)
            cases selected with
            | @writingConflict candidate loadedOp next mailbox
                happ hnext hn hvalid hs =>
              have hw' := hwire.symm.trans hw
              have hfrom := source_eq_s3_of_inbound_wire hstoreAddr hw'
              subst from_
              have hmsg := congrArg (fun x : ConcreteMessage => x.2.2)
                (Option.some.inj hw')
              injection hmsg with hop
              subst op
              cases htries : candidate.tries with
              | zero =>
                obtain ⟨a', running, rest, wire, nodeTokens,
                    hmatch, hrun, hrestart, hrel'⟩ :=
                  normalRel_conflict_exhausted focus.before focus.after
                    happ hnext hn htries hstoreAddr
                    (by simpa [focus.wires_eq, hwire, hstoreAddr, optionList,
                      List.append_assoc] using hprotocol)
                    (by simpa [focus.tokens_eq, htokens,
                      List.append_assoc] using hcover)
                    hstore htime hstepTime (.proc "s3") pre post hnet
                have hservice := node_service_step_singleton hrun
                have hservice' := some_eq_one_of_val_eq hservice
                rw [← hrunning] at hservice'
                rw [finishNode hservice'] at htake
                simp only [Option.some.injEq, Prod.mk.injEq] at htake
                obtain ⟨rfl, rfl, rfl⟩ := htake
                refine ⟨a', hmatch, ?_⟩
                simpa [focus.nodes_eq, List.append_assoc] using hrel'
              | succ k =>
                obtain ⟨hrun, hrel'⟩ :=
                  normalRel_conflict_retry focus.before focus.after
                    happ hn hvalid hs htries hstoreAddr
                    (by simpa [focus.wires_eq, hwire, hstoreAddr, optionList,
                      List.append_assoc] using hprotocol)
                    (by simpa [focus.tokens_eq, htokens,
                      List.append_assoc] using hcover)
                    hstore htime hstepTime (.proc "s3") pre post hnet
                have hservice := node_service_step_singleton hrun
                have hservice' := some_eq_one_of_val_eq hservice
                rw [← hrunning] at hservice'
                rw [finishNode hservice'] at htake
                simp only [Option.some.injEq, Prod.mk.injEq] at htake
                obtain ⟨rfl, rfl, rfl⟩ := htake
                refine ⟨a, matches_hidden rfl, ?_⟩
                simpa [focus.nodes_eq, routedOuts, routedMessages,
                  List.append_assoc, sends_notes] using hrel'
            | idle => simp [hw] at hwire
            | loadingGet => simp [hw, hstoreAddr] at hwire
            | loadingGot => simp [hw] at hwire
            | loadingDone => simp [hw] at hwire
            | writingPut => simp [hw, hstoreAddr] at hwire
            | writingServed => simp [hw] at hwire
            | writingLost => simp [hw] at hwire
            | writingShed => simp [hw] at hwire
          | failed op =>
            have hm : (from_, .proc proc, CMsg.failed op) ∈
                protocolMessages c.net := by rw [hnet]; simp [protocolMessages]
            have hw := focus.wire_to hnodup hstoreAddr hphysical
              ((hprotocol.mem_iff).1 hm)
            cases selected with
            | @writingLost candidate loadedOp next mailbox
                happ hnext hn hvalid =>
              have hw' := hwire.symm.trans hw
              have hfrom := source_eq_s3_of_inbound_wire hstoreAddr hw'
              subst from_
              have hmsg := congrArg (fun x : ConcreteMessage => x.2.2)
                (Option.some.inj hw')
              injection hmsg with hop
              subst op
              obtain ⟨running, rest, wire, nodeTokens, hrun, hrestart, hrel'⟩ :=
                normalRel_failed focus.before focus.after happ hnext hn
                  (Or.inr rfl) hstoreAddr
                  (by simpa [focus.wires_eq, hwire, hstoreAddr, optionList,
                    List.append_assoc] using hprotocol)
                  (by simpa [focus.tokens_eq, htokens,
                    List.append_assoc] using hcover)
                  hstore htime hstepTime (.proc "s3") pre post hnet
              have hservice := node_service_step_singleton hrun
              have hservice' := some_eq_one_of_val_eq hservice
              rw [← hrunning] at hservice'
              rw [finishNode hservice'] at htake
              simp only [Option.some.injEq, Prod.mk.injEq] at htake
              obtain ⟨rfl, rfl, rfl⟩ := htake
              refine ⟨a, matches_hidden rfl, ?_⟩
              simpa [focus.nodes_eq, List.append_assoc] using hrel'
            | @writingShed candidate loadedOp next mailbox
                happ hnext hn hvalid hs =>
              have hw' := hwire.symm.trans hw
              have hfrom := source_eq_s3_of_inbound_wire hstoreAddr hw'
              subst from_
              have hmsg := congrArg (fun x : ConcreteMessage => x.2.2)
                (Option.some.inj hw')
              injection hmsg with hop
              subst op
              obtain ⟨running, rest, wire, nodeTokens, hrun, hrestart, hrel'⟩ :=
                normalRel_failed focus.before focus.after happ hnext hn
                  (Or.inl rfl) hstoreAddr
                  (by simpa [focus.wires_eq, hwire, hstoreAddr, optionList,
                    List.append_assoc] using hprotocol)
                  (by simpa [focus.tokens_eq, htokens,
                    List.append_assoc] using hcover)
                  hstore htime hstepTime (.proc "s3") pre post hnet
              have hservice := node_service_step_singleton hrun
              have hservice' := some_eq_one_of_val_eq hservice
              rw [← hrunning] at hservice'
              rw [finishNode hservice'] at htake
              simp only [Option.some.injEq, Prod.mk.injEq] at htake
              obtain ⟨rfl, rfl, rfl⟩ := htake
              refine ⟨a, matches_hidden rfl, ?_⟩
              simpa [focus.nodes_eq, List.append_assoc] using hrel'
            | idle => simp [hw] at hwire
            | loadingGet => simp [hw, hstoreAddr] at hwire
            | loadingGot => simp [hw] at hwire
            | loadingDone => simp [hw] at hwire
            | writingPut => simp [hw, hstoreAddr] at hwire
            | writingConflict => simp [hw] at hwire
            | writingServed => simp [hw] at hwire
        · by_cases hs3 : proc = "s3"
          · subst proc
            have hcstate : c.state? "s3" = some (.store store) := by
              rw [Network.Conf.state?, hstates, List.find?_append,
                hnodes.find_state_none hphysical]
              simp
            cases message with
            | app message =>
              have hrel' := NormalRel.storeApp
                ⟨nodeStates, store, wires, tokens, hstates, hnodes,
                  hprotocol, hcover, hstore, htime⟩
                from_ message hstepTime pre post hnet
              have hraw :
                  ((storeReceive from_.addr (.app message)).run cfg store).val =
                    [((), store, [])] := by cases message <;> rfl
              have hservice := store_service_step_singleton (now := t) hraw
              have hservice' :
                  system.step cfg (.store store) t
                    (.msg from_.addr (.app message)) =
                    Some.one (.store store, []) := Subtype.ext hservice
              have hmap := hnodes.map_update_store hphysical store
              rw [herase] at htake
              unfold Network.Conf.run at htake
              rw [hcstate] at htake
              simp only [Option.map_some] at htake
              rw [show pick
                  (system.step cfg (.store store) t
                    (.msg from_.addr (.app message))) choice =
                    (.store store, []) by
                rw [hservice']
                simp [Experiment.pick, Some.one]] at htake
              rw [hstates, hmap] at htake
              obtain ⟨rfl, rfl, rfl⟩ := htake
              refine ⟨a, matches_hidden rfl, ?_⟩
              simpa [hstates, routedOuts, routedMessages, List.append_assoc,
                sends_notes] using hrel'
            | get op key =>
              have hm : (from_, .proc "s3", CMsg.get op key) ∈
                  protocolMessages c.net := by rw [hnet]; simp [protocolMessages]
              have hwm := (hprotocol.mem_iff).1 hm
              obtain ⟨source, dest, protocol, heq⟩ :=
                hnodes.protocol_is_between_procs hwm
              cases heq
              have hsource : source ∈ nodes := by
                apply hnodes.outbound_source_mem
                  (by simpa [hstoreAddr] using hphysical)
                simpa [hstoreAddr] using hwm
              let focus := hnodes.focus hsource
              have hw := focus.wire_from hnodup hstoreAddr hphysical hwm
              have selected := focus.selected
              generalize hrunning : focus.running = representedRunning at selected
              generalize hwire : focus.wire = representedWire at selected
              generalize htokens : focus.nodeTokens = representedTokens at selected
              cases selected with
              | @loadingGet call tries loadedOp next mailbox
                  happ hnext hn =>
                have hw' := hwire.symm.trans hw
                rw [hstoreAddr] at hw'
                simp only [Option.some.injEq, Prod.mk.injEq,
                  CMsg.get.injEq, true_and] at hw'
                obtain ⟨rfl, rfl⟩ := hw'
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
                    normalRel_store_get_done focus.before focus.after
                      happ hnext hn hpick hunchanged hstoreAddr
                      (by simpa [focus.wires_eq, hwire, hstoreAddr, optionList,
                        List.append_assoc] using hprotocol)
                      (by simpa [focus.tokens_eq, htokens,
                        List.append_assoc] using hcover)
                      hstore htime hstepTime pre post hnet rfl
                  have hraw := store_get_run cfg store source loadedOp call.req.key
                  have hservice := store_service_step_singleton (now := t) hraw
                  have hservice' :
                      system.step cfg (.store store) t
                        (.msg source (.get loadedOp call.req.key)) =
                        Some.one (.store store,
                          [.send source (.got loadedOp
                            (storeLookup store call.req.key))]) :=
                    Subtype.ext hservice
                  have hmap := hnodes.map_update_store hphysical store
                  rw [herase] at htake
                  simp only [Network.Who.addr] at htake
                  unfold Network.Conf.run at htake
                  rw [hcstate] at htake
                  simp only [Option.map_some] at htake
                  rw [show pick
                      (system.step cfg (.store store) t
                        (.msg source (.get loadedOp call.req.key))) choice =
                        (.store store,
                          [.send source (.got loadedOp
                            (storeLookup store call.req.key))]) by
                    rw [hservice']
                    simp [Experiment.pick, Some.one]] at htake
                  rw [hstates, hmap] at htake
                  obtain ⟨rfl, rfl, rfl⟩ := htake
                  refine ⟨a', hmatch, ?_⟩
                  simpa [focus.nodes_eq, focus.states_eq, hrunning, hstates,
                    routedOuts,
                    routedMessages, sends, Network.Conf.route,
                    Network.Conf.isProc, List.append_assoc] using hrel'
                · obtain ⟨hrun, hrel'⟩ :=
                    normalRel_store_get_changed focus.before focus.after
                      happ hnext hn hpick hunchanged hstoreAddr
                      (by simpa [focus.wires_eq, hwire, hstoreAddr, optionList,
                        List.append_assoc] using hprotocol)
                      (by simpa [focus.tokens_eq, htokens,
                        List.append_assoc] using hcover)
                      hstore htime hstepTime pre post hnet
                  have hservice := store_service_step_singleton (now := t) hrun
                  have hservice' :
                      system.step cfg (.store store) t
                        (.msg source (.get loadedOp call.req.key)) =
                        Some.one (.store store,
                          [.send source (.got loadedOp
                            (storeLookup store call.req.key))]) :=
                    Subtype.ext hservice
                  have hmap := hnodes.map_update_store hphysical store
                  rw [herase] at htake
                  simp only [Network.Who.addr] at htake
                  unfold Network.Conf.run at htake
                  rw [hcstate] at htake
                  simp only [Option.map_some] at htake
                  rw [show pick
                      (system.step cfg (.store store) t
                        (.msg source (.get loadedOp call.req.key))) choice =
                        (.store store,
                          [.send source (.got loadedOp
                            (storeLookup store call.req.key))]) by
                    rw [hservice']
                    simp [Experiment.pick, Some.one]] at htake
                  rw [hstates, hmap] at htake
                  obtain ⟨rfl, rfl, rfl⟩ := htake
                  refine ⟨a, matches_hidden rfl, ?_⟩
                  simpa [focus.nodes_eq, focus.states_eq, hrunning, hstates,
                    routedOuts,
                    routedMessages, sends, Network.Conf.route,
                    Network.Conf.isProc, List.append_assoc] using hrel'
              | idle => simp [hw] at hwire
              | loadingGot => simp [hw] at hwire
              | loadingDone => simp [hw] at hwire
              | writingPut => simp [hw] at hwire
              | writingConflict => simp [hw] at hwire
              | writingServed => simp [hw] at hwire
              | writingLost => simp [hw] at hwire
              | writingShed => simp [hw] at hwire
            | put op key promise ifMatch =>
              have hm : (from_, .proc "s3",
                  CMsg.put op key promise ifMatch) ∈
                  protocolMessages c.net := by rw [hnet]; simp [protocolMessages]
              have hwm := (hprotocol.mem_iff).1 hm
              obtain ⟨source, dest, protocol, heq⟩ :=
                hnodes.protocol_is_between_procs hwm
              cases heq
              have hsource : source ∈ nodes := by
                apply hnodes.outbound_source_mem
                  (by simpa [hstoreAddr] using hphysical)
                simpa [hstoreAddr] using hwm
              let focus := hnodes.focus hsource
              have hw := focus.wire_from hnodup hstoreAddr hphysical hwm
              have selected := focus.selected
              generalize hrunning : focus.running = representedRunning at selected
              generalize hwire : focus.wire = representedWire at selected
              generalize htokens : focus.nodeTokens = representedTokens at selected
              cases selected with
              | @writingPut candidate loadedOp next mailbox
                  happ hnext hn hvalid hs =>
                have hw' := hwire.symm.trans hw
                rw [hstoreAddr] at hw'
                simp only [Option.some.injEq, Prod.mk.injEq,
                  CMsg.put.injEq, true_and] at hw'
                obtain ⟨rfl, rfl, rfl, rfl⟩ := hw'
                let chosen := pick
                  ((storeReceive source
                    (.put loadedOp candidate.req.key candidate.promise
                      (candidate.doc.map (·.2)))).run cfg store) choice
                have hchosen :
                    pick ((storeReceive source
                      (.put loadedOp candidate.req.key candidate.promise
                        (candidate.doc.map (·.2)))).run cfg store) choice =
                      chosen := rfl
                obtain ⟨unit, afterStore, emitted⟩ := chosen
                cases unit
                have hout :
                    ((), afterStore, emitted) ∈
                      ((storeReceive source
                        (.put loadedOp candidate.req.key candidate.promise
                          (candidate.doc.map (·.2)))).run cfg store).val := by
                  rw [← hchosen]
                  exact pick_mem _ _
                have hservicePick :
                    pick (system.step cfg (.store store) t
                      (.msg source
                        (.put loadedOp candidate.req.key candidate.promise
                          (candidate.doc.map (·.2))))) choice =
                      (Local.store afterStore, emitted) :=
                  store_service_step_pick (now := t) hchosen
                have hrouteStore (destination : Addr) :
                    c.route destination =
                      (⟨[], nodeStates ++
                        [("s3", .store afterStore)], 0⟩ :
                        Network.Conf system).route destination := by
                  change
                    (⟨[], c.states, 0⟩ : Network.Conf system).route
                        destination = _
                  rw [hstates, ← hnodes.map_update_store
                    hphysical afterStore]
                  exact route_map_update _ "s3" destination
                    (.store afterStore)
                have finishStore :
                    c.run cfg "s3" t
                        (.msg source
                          (.put loadedOp candidate.req.key candidate.promise
                            (candidate.doc.map (·.2)))) choice
                        (c.net.eraseIdx index) =
                      some (emitted,
                        ⟨pre ++ post ++ routedOuts
                            (nodeStates ++ [("s3", .store afterStore)])
                            "s3" emitted,
                          nodeStates ++ [("s3", .store afterStore)], t⟩) := by
                  have hmap := hnodes.map_update_store hphysical afterStore
                  have hrouted :
                      (sends emitted).map (fun x =>
                        (.proc "s3", c.route x.1, x.2)) =
                        routedOuts
                          (nodeStates ++ [("s3", .store afterStore)])
                          "s3" emitted := by
                    unfold routedOuts routedMessages
                    apply List.map_congr_left
                    intro output _
                    obtain ⟨destination, payload⟩ := output
                    congr 2
                    change c.route destination = _
                    exact hrouteStore destination
                  unfold Network.Conf.run
                  rw [hcstate]
                  simp only [Option.map_some]
                  rw [hservicePick, herase, hstates, hmap]
                  rw [hrouted]
                simp only [Network.Who.addr] at htake
                cases store_put_classify hconditional hout with
                | conflict =>
                  have hrel' :=
                    normalRel_store_conflict focus.before focus.after
                      happ hnext hn hvalid hs hstoreAddr
                      (by simpa [focus.wires_eq, hwire, hstoreAddr, optionList,
                        List.append_assoc] using hprotocol)
                      (by simpa [focus.tokens_eq, htokens,
                        List.append_assoc] using hcover)
                      hstore htime hstepTime pre post hnet
                  rw [finishStore] at htake
                  simp only [Option.some.injEq, Prod.mk.injEq] at htake
                  obtain ⟨rfl, rfl, rfl⟩ := htake
                  refine ⟨a, matches_hidden rfl, ?_⟩
                  simpa [focus.nodes_eq, focus.states_eq, hrunning,
                    routedOuts,
                    routedMessages, sends, Network.Conf.route,
                    Network.Conf.isProc, List.append_assoc] using hrel'
                | written hmatch =>
                  obtain ⟨a', hmatchAbstract, hrel'⟩ :=
                    normalRel_store_written focus.before focus.after
                      happ hnext hn hvalid hs hmatch hstoreAddr
                      (by simpa [focus.wires_eq, hwire, hstoreAddr, optionList,
                        List.append_assoc] using hprotocol)
                      (by simpa [focus.tokens_eq, htokens,
                        List.append_assoc] using hcover)
                      hstore htime hstepTime pre post hnet
                  rw [finishStore] at htake
                  simp only [Option.some.injEq, Prod.mk.injEq] at htake
                  obtain ⟨rfl, rfl, rfl⟩ := htake
                  refine ⟨a', hmatchAbstract, ?_⟩
                  simpa [focus.nodes_eq, focus.states_eq, hrunning,
                    routedOuts,
                    routedMessages, sends, Network.Conf.route,
                    Network.Conf.isProc, List.append_assoc] using hrel'
                | landedFailed hmatch =>
                  obtain ⟨a', hmatchAbstract, hrel'⟩ :=
                    normalRel_store_landedFailed focus.before focus.after
                      happ hnext hn hvalid hs hmatch hstoreAddr
                      (by simpa [focus.wires_eq, hwire, hstoreAddr, optionList,
                        List.append_assoc] using hprotocol)
                      (by simpa [focus.tokens_eq, htokens,
                        List.append_assoc] using hcover)
                      hstore htime hstepTime pre post hnet
                  rw [finishStore] at htake
                  simp only [Option.some.injEq, Prod.mk.injEq] at htake
                  obtain ⟨rfl, rfl, rfl⟩ := htake
                  refine ⟨a', hmatchAbstract, ?_⟩
                  simpa [focus.nodes_eq, focus.states_eq, hrunning,
                    routedOuts,
                    routedMessages, sends, Network.Conf.route,
                    Network.Conf.isProc, List.append_assoc] using hrel'
                | failed =>
                  obtain ⟨a', hmatchAbstract, hrel'⟩ :=
                    normalRel_store_failed focus.before focus.after
                      happ hnext hn hvalid hs hstoreAddr
                      (by simpa [focus.wires_eq, hwire, hstoreAddr, optionList,
                        List.append_assoc] using hprotocol)
                      (by simpa [focus.tokens_eq, htokens,
                        List.append_assoc] using hcover)
                      hstore htime hstepTime pre post hnet
                  rw [finishStore] at htake
                  simp only [Option.some.injEq, Prod.mk.injEq] at htake
                  obtain ⟨rfl, rfl, rfl⟩ := htake
                  refine ⟨a', hmatchAbstract, ?_⟩
                  simpa [focus.nodes_eq, focus.states_eq, hrunning,
                    routedOuts,
                    routedMessages, sends, Network.Conf.route,
                    Network.Conf.isProc, List.append_assoc] using hrel'
              | idle => simp [hw] at hwire
              | loadingGet => simp [hw] at hwire
              | loadingGot => simp [hw] at hwire
              | loadingDone => simp [hw] at hwire
              | writingConflict => simp [hw] at hwire
              | writingServed => simp [hw] at hwire
              | writingLost => simp [hw] at hwire
              | writingShed => simp [hw] at hwire
            | got op doc =>
              have hm : (from_, .proc "s3", CMsg.got op doc) ∈
                  protocolMessages c.net := by rw [hnet]; simp [protocolMessages]
              have hwm := (hprotocol.mem_iff).1 hm
              exact (hnodes.wire_to_store_is_request
                hstoreAddr hphysical hwm).elim
            | written op =>
              have hm : (from_, .proc "s3", CMsg.written op) ∈
                  protocolMessages c.net := by rw [hnet]; simp [protocolMessages]
              have hwm := (hprotocol.mem_iff).1 hm
              exact (hnodes.wire_to_store_is_request
                hstoreAddr hphysical hwm).elim
            | conflict op =>
              have hm : (from_, .proc "s3", CMsg.conflict op) ∈
                  protocolMessages c.net := by rw [hnet]; simp [protocolMessages]
              have hwm := (hprotocol.mem_iff).1 hm
              exact (hnodes.wire_to_store_is_request
                hstoreAddr hphysical hwm).elim
            | failed op =>
              have hm : (from_, .proc "s3", CMsg.failed op) ∈
                  protocolMessages c.net := by rw [hnet]; simp [protocolMessages]
              have hwm := (hprotocol.mem_iff).1 hm
              exact (hnodes.wire_to_store_is_request
                hstoreAddr hphysical hwm).elim
          · have hs3' : "s3" ≠ proc := fun h => hs3 h.symm
            have hcstate : c.state? proc = none := by
              rw [Network.Conf.state?, hstates, List.find?_append,
                hnodes.find_state_none hproc]
              simp [hs3']
            rw [herase] at htake
            simp [Network.Conf.run, hcstate] at htake
  | tick address choice =>
    simp only [Network.Conf.take] at htake
    split at htake
    next hstepTime =>
      obtain ⟨nodeStates, store, wires, tokens, hstates, hnodes,
        hprotocol, hcover, hstore, htime⟩ := hrel
      have hrelTime : NormalRel nodes cfg
          ⟨c.net, nodeStates ++ [("s3", .store store)], t⟩ a :=
        ⟨nodeStates, store, wires, tokens, rfl, hnodes, hprotocol, hcover,
          hstore, Nat.le_trans htime hstepTime⟩
      by_cases haddress : address ∈ nodes
      · let focus := hnodes.focus haddress
        have hcstate : c.state? address = some (.node focus.running) := by
          rw [Network.Conf.state?, hstates]
          exact focus.state_at_with_store hnodup
        have hservice :
            system.step cfg (.node focus.running) t .tick =
              Some.one (.node focus.running, []) := by rfl
        have hmap := focus.map_update hnodup hphysical focus.running
        unfold Network.Conf.run at htake
        rw [hcstate] at htake
        simp only [Option.map_some] at htake
        rw [show pick
            (system.step cfg (.node focus.running) t .tick) choice =
              (.node focus.running, []) by
          rw [hservice]
          simp [Experiment.pick, Some.one]] at htake
        rw [hstates, hmap] at htake
        obtain ⟨rfl, rfl, rfl⟩ := htake
        refine ⟨a, matches_hidden rfl, ?_⟩
        simpa [focus.states_eq, List.append_assoc] using hrelTime
      · by_cases hs3 : address = "s3"
        · subst address
          have hcstate : c.state? "s3" = some (.store store) := by
            rw [Network.Conf.state?, hstates, List.find?_append,
              hnodes.find_state_none hphysical]
            simp
          have hservice :
              system.step cfg (.store store) t .tick =
                Some.one (.store store, []) := by rfl
          have hmap := hnodes.map_update_store hphysical store
          unfold Network.Conf.run at htake
          rw [hcstate] at htake
          simp only [Option.map_some] at htake
          rw [show pick
              (system.step cfg (.store store) t .tick) choice =
                (.store store, []) by
            rw [hservice]
            simp [Experiment.pick, Some.one]] at htake
          rw [hstates, hmap] at htake
          obtain ⟨rfl, rfl, rfl⟩ := htake
          exact ⟨a, matches_hidden rfl, by
            simpa [sends] using hrelTime⟩
        · have hs3' : "s3" ≠ address := fun h => hs3 h.symm
          have hcstate : c.state? address = none := by
            rw [Network.Conf.state?, hstates, List.find?_append,
              hnodes.find_state_none haddress]
            simp [hs3']
          simp [Network.Conf.run, hcstate] at htake
    next => contradiction

set_option maxHeartbeats 2000000 in
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

inductive RequestNodes (cfg : Storage.Config) :
    List Addr → List (Addr × Local) → Prop where
  | nil : RequestNodes cfg [] []
  | cons {address : Addr} {running : Running Storage.Config Nat CMsg}
      {nodes : List Addr} {states : List (Addr × Local)} :
      RequestNode cfg running →
      RequestNodes cfg nodes states →
      RequestNodes cfg (address :: nodes) ((address, .node running) :: states)

structure RequestNodes.Focus (cfg : Storage.Config)
    (nodes : List Addr) (states : List (Addr × Local)) (address : Addr) where
  beforeNodes : List Addr
  afterNodes : List Addr
  beforeStates : List (Addr × Local)
  afterStates : List (Addr × Local)
  running : Running Storage.Config Nat CMsg
  nodes_eq : nodes = beforeNodes ++ address :: afterNodes
  states_eq :
    states = beforeStates ++ (address, .node running) :: afterStates
  before : RequestNodes cfg beforeNodes beforeStates
  selected : RequestNode cfg running
  after : RequestNodes cfg afterNodes afterStates

theorem RequestNodes.exists_focus {cfg : Storage.Config}
    {nodes : List Addr} {states : List (Addr × Local)}
    (h : RequestNodes cfg nodes states) {address : Addr}
    (hm : address ∈ nodes) :
    ∃ focus : RequestNodes.Focus cfg nodes states address, True := by
  induction h with
  | nil => simp at hm
  | @cons head running tail tailStates hhead htail ih =>
    simp only [List.mem_cons] at hm
    rcases hm with rfl | hm
    · exact ⟨⟨[], tail, [], tailStates, running, rfl, rfl,
        .nil, hhead, htail⟩, trivial⟩
    · obtain ⟨focus, _⟩ := ih hm
      exact ⟨
        ⟨head :: focus.beforeNodes, focus.afterNodes,
          (head, .node running) :: focus.beforeStates, focus.afterStates,
          focus.running,
          by simp [focus.nodes_eq],
          by simp [focus.states_eq],
          .cons hhead focus.before, focus.selected, focus.after⟩, trivial⟩

noncomputable def RequestNodes.focus {cfg : Storage.Config}
    {nodes : List Addr} {states : List (Addr × Local)}
    (h : RequestNodes cfg nodes states) {address : Addr}
    (hm : address ∈ nodes) :
    RequestNodes.Focus cfg nodes states address :=
  (h.exists_focus hm).choose

theorem RequestNodes.append {cfg : Storage.Config}
    {leftNodes rightNodes : List Addr}
    {leftStates rightStates : List (Addr × Local)}
    (left : RequestNodes cfg leftNodes leftStates)
    (right : RequestNodes cfg rightNodes rightStates) :
    RequestNodes cfg (leftNodes ++ rightNodes) (leftStates ++ rightStates) := by
  induction left with
  | nil => exact right
  | cons hnode htail ih =>
    simpa [List.append_assoc] using RequestNodes.cons hnode ih

theorem RequestNodes.Focus.replace {cfg : Storage.Config}
    {nodes : List Addr} {states : List (Addr × Local)} {address : Addr}
    (focus : RequestNodes.Focus cfg nodes states address)
    {running : Running Storage.Config Nat CMsg}
    (selected : RequestNode cfg running) :
    RequestNodes cfg nodes
      (focus.beforeStates ++ (address, .node running) ::
        focus.afterStates) := by
  have hbuilt := focus.before.append
    (RequestNodes.cons (address := address) selected focus.after)
  simpa [focus.nodes_eq, List.append_assoc] using hbuilt

theorem RequestNodes.find_state_none {cfg : Storage.Config}
    {nodes : List Addr} {states : List (Addr × Local)}
    (h : RequestNodes cfg nodes states) {address : Addr}
    (hm : address ∉ nodes) :
    states.find? (·.1 == address) = none := by
  induction h with
  | nil => rfl
  | @cons head running tail tailStates hhead htail ih =>
    have hne : head ≠ address := by
      intro heq
      exact hm (by simp [heq])
    have htail : address ∉ tail :=
      fun hmem => hm (by simp [hmem])
    simp [beq_eq_false_iff_ne.mpr hne, ih htail]

theorem RequestNodes.map_update_miss {cfg : Storage.Config}
    {nodes : List Addr} {states : List (Addr × Local)}
    (h : RequestNodes cfg nodes states) {address : Addr}
    (hm : address ∉ nodes) (value : Local) :
    states.map (fun x =>
      if x.1 == address then (x.1, value) else x) = states := by
  induction h with
  | nil => rfl
  | @cons head running tail tailStates hhead htail ih =>
    have hne : head ≠ address := by
      intro heq
      exact hm (by simp [heq])
    have htail : address ∉ tail :=
      fun hmem => hm (by simp [hmem])
    simp only [List.map_cons]
    rw [show (head == address) = false from beq_eq_false_iff_ne.mpr hne]
    simp only [Bool.false_eq_true, if_false]
    rw [ih htail]

theorem RequestNodes.Focus.state_at_with_store
    {cfg : Storage.Config} {nodes : List Addr}
    {states : List (Addr × Local)} {address : Addr}
    (focus : RequestNodes.Focus cfg nodes states address)
    (hnodup : nodes.Nodup) (store : Store) :
    ((states ++ [("s3", Local.store store)]).find?
      (fun x : Addr × Local => x.1 == address)).map
        (fun x : Addr × Local => x.2) =
      some (Local.node focus.running) := by
  have hsplit := nodup_middle_not_mem
    (by simpa [focus.nodes_eq] using hnodup)
  have heq := congrArg
    (fun xs : List (Addr × Local) =>
      ((xs ++ [("s3", Local.store store)]).find?
        (fun x : Addr × Local => x.1 == address)).map
          (fun x : Addr × Local => x.2))
    focus.states_eq
  rw [heq]
  simp [List.find?_append,
    focus.before.find_state_none hsplit.1]

theorem RequestNodes.Focus.map_update
    {cfg : Storage.Config} {nodes : List Addr}
    {states : List (Addr × Local)} {address : Addr}
    (focus : RequestNodes.Focus cfg nodes states address)
    (hnodup : nodes.Nodup) (hphysical : "s3" ∉ nodes)
    (running : Running Storage.Config Nat CMsg) (store : Store) :
    (states ++ [("s3", Local.store store)]).map
      (fun x : Addr × Local =>
        if x.1 == address then (x.1, Local.node running) else x) =
      (focus.beforeStates ++
        (address, Local.node running) :: focus.afterStates) ++
        [("s3", Local.store store)] := by
  have hsplit := nodup_middle_not_mem
    (by simpa [focus.nodes_eq] using hnodup)
  have hmember : address ∈ nodes := by
    rw [focus.nodes_eq]
    simp
  have hneStore : "s3" ≠ address := by
    intro heq
    exact hphysical (heq ▸ hmember)
  have heq := congrArg
    (fun xs : List (Addr × Local) =>
      (xs ++ [("s3", Local.store store)]).map
        (fun x : Addr × Local =>
          if x.1 == address then (x.1, Local.node running) else x))
    focus.states_eq
  rw [heq]
  simp only [List.map_append, List.map_cons, List.map_nil]
  rw [focus.before.map_update_miss hsplit.1 (Local.node running),
    focus.after.map_update_miss hsplit.2 (Local.node running)]
  simp [beq_eq_false_iff_ne.mpr hneStore]

theorem RequestNodes.map_update_store
    {cfg : Storage.Config} {nodes : List Addr}
    {states : List (Addr × Local)}
    (h : RequestNodes cfg nodes states) (hphysical : "s3" ∉ nodes)
    (store nextStore : Store) :
    (states ++ [("s3", Local.store store)]).map
      (fun x : Addr × Local =>
        if x.1 == "s3" then (x.1, Local.store nextStore) else x) =
      states ++ [("s3", Local.store nextStore)] := by
  simp only [List.map_append, List.map_cons, List.map_nil]
  rw [h.map_update_miss hphysical (Local.store nextStore)]
  simp

def requestRoute (nodes : List Addr) (cfg : Storage.Config) :
    Network.Who :=
  (⟨[], world nodes, 0⟩ : Network.Conf system).route cfg.store

theorem RequestNodes.any_addresses {cfg : Storage.Config}
    {nodes : List Addr} {states : List (Addr × Local)}
    (h : RequestNodes cfg nodes states) (destination : Addr) :
    states.any (·.1 == destination) =
      (nodes.map fun address =>
        (address, Local.node ⟨0, [], node⟩)).any
        (·.1 == destination) := by
  induction h with
  | nil => rfl
  | @cons address running tail tailStates hhead htail ih =>
    simp only [List.any_cons, List.map_cons, Prod.fst]
    rw [ih]

theorem RequestNodes.route_eq {cfg : Storage.Config}
    {nodes : List Addr} {states : List (Addr × Local)}
    (h : RequestNodes cfg nodes states) (store : Store)
    (destination : Addr) :
    (⟨[], states ++ [("s3", Local.store store)], 0⟩ :
      Network.Conf system).route destination =
      (⟨[], world nodes, 0⟩ :
        Network.Conf system).route destination := by
  unfold world
  simp only [Network.Conf.route, Network.Conf.isProc, List.any_append]
  rw [h.any_addresses destination]
  simp

def RequestNet (nodes : List Addr) (cfg : Storage.Config)
    (net : List ConcreteMessage) : Prop :=
  ∀ source destination message, (source, destination, message) ∈ net →
    match message with
    | .app _ => ∃ address, destination = .proc address
    | .get _ _ =>
        ∃ address, address ∈ nodes ∧ source = .proc address ∧
          destination = requestRoute nodes cfg
    | _ => False

theorem RequestNet.request {nodes : List Addr} {cfg : Storage.Config}
    {net : List ConcreteMessage} (h : RequestNet nodes cfg net)
    (client to : Addr) (message : Msg) :
    RequestNet nodes cfg
      (net ++ [(.client client, .proc to, .app message)]) := by
  intro source destination concrete hm
  rw [List.mem_append] at hm
  rcases hm with hm | hm
  · exact h source destination concrete hm
  · simp only [List.mem_singleton, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl, rfl⟩ := hm
    exact ⟨to, rfl⟩

theorem RequestNet.remove {nodes : List Addr} {cfg : Storage.Config}
    {net : List ConcreteMessage} (h : RequestNet nodes cfg net)
    {message : ConcreteMessage} (pre post : List ConcreteMessage)
    (hnet : net = pre ++ message :: post) :
    RequestNet nodes cfg (pre ++ post) := by
  intro source destination concrete hm
  apply h source destination concrete
  rw [hnet]
  simp only [List.mem_append, List.mem_cons]
  rcases List.mem_append.mp hm with hm | hm
  · exact Or.inl hm
  · exact Or.inr (Or.inr hm)

theorem RequestNet.emitGet {nodes : List Addr}
    {cfg : Storage.Config} {net : List ConcreteMessage}
    (h : RequestNet nodes cfg net) (source : Addr)
    (hsource : source ∈ nodes) (op : Nat) (key : Ident) :
    RequestNet nodes cfg
      (net ++ [(.proc source, requestRoute nodes cfg, .get op key)]) := by
  intro from_ destination message hm
  rw [List.mem_append] at hm
  rcases hm with hm | hm
  · exact h from_ destination message hm
  · simp only [List.mem_singleton, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl, rfl⟩ := hm
    exact ⟨source, hsource, rfl, rfl⟩

theorem requestRoute_ne_s3 {nodes : List Addr} {cfg : Storage.Config}
    (hstore : cfg.store ≠ "s3") :
    requestRoute nodes cfg ≠ .proc "s3" := by
  intro heq
  unfold requestRoute Network.Conf.route at heq
  by_cases hp :
      (⟨[], world nodes, 0⟩ :
        Network.Conf system).isProc cfg.store = true
  · rw [if_pos hp] at heq
    exact hstore (Network.Who.proc.inj heq)
  · rw [if_neg hp] at heq
    cases heq

def RequestOnlyRel (nodes : List Addr) (cfg : Storage.Config)
    (concrete : Network.Conf system)
    (abstract : Experiment.Conf promises) : Prop :=
  ∃ states store,
    concrete.states = states ++ [("s3", .store store)] ∧
    RequestNodes cfg nodes states ∧
    RequestNet nodes cfg concrete.net ∧
    abstract.state = {} ∧
    abstract.now ≤ concrete.now

theorem initial_requestOnlyRel (nodes : List Addr)
    (cfg : Storage.Config) :
    RequestOnlyRel nodes cfg (Network.initial (world nodes))
      (Experiment.initial {}) := by
  refine ⟨nodes.map (fun address =>
      (address, .node ⟨0, [], node⟩)), {}, rfl, ?_, ?_, rfl,
    Nat.le_refl 0⟩
  · induction nodes with
    | nil => exact .nil
    | cons address tail ih =>
      exact .cons (.idle (by simp [RequestOnlyMailbox]) rfl) ih
  · intro source destination message hm
    simp [Network.initial] at hm

theorem storage_simulationOn_not_s3 {nodes : List Addr}
    {cfg : Storage.Config} (hnodup : nodes.Nodup)
    (hphysical : "s3" ∉ nodes) (hstoreAddr : cfg.store ≠ "s3") :
    Network.SimulationOn cfg { cfg.app with unreliable := true }
      clientView DriveSafe (RequestOnlyRel nodes cfg) := by
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
        obtain ⟨states, store, hstates, hnodes, hnet, hstate, htime⟩ :=
          hrel
        let a' : Experiment.Conf promises :=
          ⟨a.net ++ [(.client client, .server, message)], a.state, t⟩
        refine ⟨a', matches_client_request
          (Nat.le_trans htime hstepTime), states, store, hstates, hnodes,
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
        obtain ⟨states, store, hstates, hnodes, hsafe, hstate, htime⟩ :=
          hrel
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
          refine ⟨a, matches_hidden rfl, states, store, ?_, hnodes, ?_,
            hstate, Nat.le_trans htime hstepTime⟩
          · simpa [herase] using hstates
          · simpa [herase] using hsafe.remove pre post hnet
        | put op key promise ifMatch => contradiction
        | got op doc => contradiction
        | written op => contradiction
        | conflict op => contradiction
        | failed op => contradiction
      next from_ proc message hmessage =>
        obtain ⟨states, store, hstates, hnodes, hsafe, hstate, htime⟩ :=
          hrel
        obtain ⟨pre, post, hnet, herase⟩ :=
          split_of_get?_eq_some hmessage
        have hm : (from_, .proc proc, message) ∈ c.net := by
          rw [hnet]
          simp
        have hs := hsafe from_ (.proc proc) message hm
        have hbase := hsafe.remove pre post hnet
        by_cases hproc : proc ∈ nodes
        · let focus := hnodes.focus hproc
          have hcstate : c.state? proc = some (.node focus.running) := by
            rw [Network.Conf.state?, hstates]
            exact focus.state_at_with_store hnodup store
          have hmessageSafe : RequestOnlyMsg message := by
            cases message <;> simp_all [RequestOnlyMsg]
          obtain ⟨running, outs, hrun, hnode, hout⟩ :=
            focus.selected.receive from_.addr message t hmessageSafe
          have hservice := node_service_step_singleton hrun
          have hservice' := some_eq_one_of_val_eq hservice
          have hmap := focus.map_update hnodup hphysical running store
          have hroute (destination : Addr) :
              c.route destination =
                (⟨[],
                  (focus.beforeStates ++
                    (proc, .node running) :: focus.afterStates) ++
                    [("s3", .store store)], 0⟩ :
                  Network.Conf system).route destination := by
            change
              (⟨[], c.states, 0⟩ : Network.Conf system).route destination =
                _
            rw [hstates, ← hmap]
            exact route_map_update _ proc destination (.node running)
          have hrouted :
              (sends outs).map (fun x =>
                (.proc proc, c.route x.1, x.2)) =
                routedOuts
                  ((focus.beforeStates ++
                    (proc, .node running) :: focus.afterStates) ++
                    [("s3", .store store)]) proc outs := by
            unfold routedOuts routedMessages
            apply List.map_congr_left
            intro output _
            obtain ⟨destination, payload⟩ := output
            congr 2
            change c.route destination = _
            exact hroute destination
          have finishNode :
              c.run cfg proc t (.msg from_.addr message) choice
                  (c.net.eraseIdx index) =
                some (outs,
                  ⟨pre ++ post ++ routedOuts
                      ((focus.beforeStates ++
                        (proc, .node running) :: focus.afterStates) ++
                        [("s3", .store store)]) proc outs,
                    (focus.beforeStates ++
                      (proc, .node running) :: focus.afterStates) ++
                      [("s3", .store store)], t⟩) := by
            unfold Network.Conf.run
            rw [hcstate]
            simp only [Option.map_some]
            rw [show pick
                (system.step cfg (.node focus.running) t
                  (.msg from_.addr message)) choice =
                (.node running, outs) by
              rw [hservice']
              simp [Experiment.pick, Some.one]]
            rw [herase, hstates, hmap, hrouted]
          rw [finishNode] at htake
          simp only [Option.some.injEq, Prod.mk.injEq] at htake
          obtain ⟨rfl, rfl, rfl⟩ := htake
          have hnodes' := focus.replace hnode
          rcases hout with rfl | ⟨op, key, rfl⟩
          · exact ⟨a, matches_hidden rfl, _ , store, rfl, hnodes',
              by simpa [routedOuts, routedMessages, sends] using hbase,
              hstate, Nat.le_trans htime hstepTime⟩
          · refine ⟨a, matches_hidden rfl, _, store, rfl, hnodes', ?_,
              hstate, Nat.le_trans htime hstepTime⟩
            have hemit := hbase.emitGet proc hproc op key
            have hrouteReq :
                (⟨[],
                  (focus.beforeStates ++
                    (proc, .node running) :: focus.afterStates) ++
                    [("s3", .store store)], 0⟩ :
                  Network.Conf system).route cfg.store =
                  requestRoute nodes cfg := by
              exact hnodes'.route_eq store cfg.store
            change RequestNet nodes cfg
              (pre ++ post ++
                [(.proc proc,
                  (⟨[],
                    (focus.beforeStates ++
                      (proc, .node running) :: focus.afterStates) ++
                      [("s3", .store store)], 0⟩ :
                    Network.Conf system).route cfg.store,
                  .get op key)])
            rw [hrouteReq]
            simpa [List.append_assoc] using hemit
        · by_cases hs3 : proc = "s3"
          · subst proc
            have hcstate : c.state? "s3" = some (.store store) := by
              rw [Network.Conf.state?, hstates, List.find?_append,
                hnodes.find_state_none hphysical]
              simp
            cases message with
            | app message =>
              have hraw :
                  ((storeReceive from_.addr (.app message)).run cfg store).val =
                    [((), store, [])] := by cases message <;> rfl
              have hservice := store_service_step_singleton
                (now := t) hraw
              have hservice' :
                  system.step cfg (.store store) t
                    (.msg from_.addr (.app message)) =
                    Some.one (.store store, []) :=
                some_eq_one_of_val_eq hservice
              have hmap := hnodes.map_update_store
                hphysical store store
              rw [herase] at htake
              unfold Network.Conf.run at htake
              rw [hcstate] at htake
              simp only [Option.map_some] at htake
              rw [show pick
                  (system.step cfg (.store store) t
                    (.msg from_.addr (.app message))) choice =
                    (.store store, []) by
                rw [hservice']
                simp [Experiment.pick, Some.one]] at htake
              rw [hstates, hmap] at htake
              obtain ⟨rfl, rfl, rfl⟩ := htake
              exact ⟨a, matches_hidden rfl, states, store, rfl, hnodes,
                by simpa [routedOuts, routedMessages, sends] using hbase,
                hstate, Nat.le_trans htime hstepTime⟩
            | get op key =>
              obtain ⟨address, haddress, hsource, hdest⟩ := hs
              exact (requestRoute_ne_s3 hstoreAddr hdest.symm).elim
            | put op key promise ifMatch => contradiction
            | got op doc => contradiction
            | written op => contradiction
            | conflict op => contradiction
            | failed op => contradiction
          · have hs3' : "s3" ≠ proc := fun h => hs3 h.symm
            have hcstate : c.state? proc = none := by
              rw [Network.Conf.state?, hstates, List.find?_append,
                hnodes.find_state_none hproc]
              simp [hs3']
            rw [herase] at htake
            simp [Network.Conf.run, hcstate] at htake
  | tick address choice =>
    simp only [Network.Conf.take] at htake
    split at htake
    next hstepTime =>
      obtain ⟨states, store, hstates, hnodes, hsafe, hstate, htime⟩ :=
        hrel
      by_cases haddress : address ∈ nodes
      · let focus := hnodes.focus haddress
        have hcstate : c.state? address = some (.node focus.running) := by
          rw [Network.Conf.state?, hstates]
          exact focus.state_at_with_store hnodup store
        have hservice :
            system.step cfg (.node focus.running) t .tick =
              Some.one (.node focus.running, []) := by rfl
        have hmap := focus.map_update hnodup hphysical focus.running store
        unfold Network.Conf.run at htake
        rw [hcstate] at htake
        simp only [Option.map_some] at htake
        rw [show pick
            (system.step cfg (.node focus.running) t .tick) choice =
              (.node focus.running, []) by
          rw [hservice]
          simp [Experiment.pick, Some.one]] at htake
        rw [hstates, hmap] at htake
        obtain ⟨rfl, rfl, rfl⟩ := htake
        exact ⟨a, matches_hidden rfl, _, store, rfl,
          focus.replace focus.selected,
          by simpa [routedOuts, routedMessages, sends] using hsafe,
          hstate, Nat.le_trans htime hstepTime⟩
      · by_cases hs3 : address = "s3"
        · subst address
          have hcstate : c.state? "s3" = some (.store store) := by
            rw [Network.Conf.state?, hstates, List.find?_append,
              hnodes.find_state_none hphysical]
            simp
          have hservice :
              system.step cfg (.store store) t .tick =
                Some.one (.store store, []) := by rfl
          have hmap := hnodes.map_update_store hphysical store store
          unfold Network.Conf.run at htake
          rw [hcstate] at htake
          simp only [Option.map_some] at htake
          rw [show pick
              (system.step cfg (.store store) t .tick) choice =
                (.store store, []) by
            rw [hservice]
            simp [Experiment.pick, Some.one]] at htake
          rw [hstates, hmap] at htake
          obtain ⟨rfl, rfl, rfl⟩ := htake
          exact ⟨a, matches_hidden rfl, states, store, rfl, hnodes,
            by simpa [routedOuts, routedMessages, sends] using hsafe,
            hstate, Nat.le_trans htime hstepTime⟩
        · have hs3' : "s3" ≠ address := fun h => hs3 h.symm
          have hcstate : c.state? address = none := by
            rw [Network.Conf.state?, hstates, List.find?_append,
              hnodes.find_state_none haddress]
            simp [hs3']
          simp [Network.Conf.run, hcstate] at htake
    next => contradiction

theorem system_refines (nodes : List Addr) (hnodup : nodes.Nodup)
    (hphysical : "s3" ∉ nodes) (cfg : Storage.Config) :
    Refines nodes cfg := by
  intro hconditional script execution hdrive
  by_cases hstoreAddr : cfg.store = "s3"
  · exact drive_refines_of_simulationOn
      (storage_simulationOn hnodup hphysical hconditional hstoreAddr)
      (initial_normalRel nodes cfg) hdrive
  · exact drive_refines_of_simulationOn
      (storage_simulationOn_not_s3
        hnodup hphysical hstoreAddr)
      (initial_requestOnlyRel nodes cfg) hdrive

end Exp2
