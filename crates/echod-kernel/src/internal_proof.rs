//! The proofs of the internal steps: one `lemma_*_legal` per step, and the
//! frame and projection lemmas they share. Nothing here is executed.

use vstd::prelude::*;

use crate::external::*;
use crate::external_proof::*;
use crate::internal::*;
use crate::object::*;
use crate::object_proof::*;
use crate::properties::*;
use crate::properties_proof::*;
use crate::store::*;
use crate::tags::OType;
use crate::types::*;

verus! {

// ---------------------------------------------------------------------------
// Proofs
// ---------------------------------------------------------------------------

/// Nothing changed: the sweeper entries hold.
pub proof fn lemma_internal_noop(now: nat, a: AState)
    ensures
        internal_legal(now, a, a),
{
    assert forall|x: Seq<char>| #[trigger] internal_obj(now, a, a, x) by {}
    lemma_internal_pointwise(now, a, a);
}

/// Projecting objects is a sweeper step.
pub proof fn lemma_project_internal(now: nat, a: AState, b: AState, ids: spec_fn(Seq<char>) -> bool)
    requires
        forall|x: Seq<char>| #[trigger] ids(x) ==>
            a.objects.contains_key(x) && b.objects.contains_key(x) && b.objects[x] == a.objects[x].project(now),
        forall|x: Seq<char>| !ids(x) ==> #[trigger] crate::external::unchanged_at(a, b, x),
    ensures
        internal_legal(now, a, b),
{
    assert forall|x: Seq<char>| #[trigger] internal_obj(now, a, b, x) by {
        if ids(x) {
        } else {
            assert(crate::external::unchanged_at(a, b, x));
        }
    }
    lemma_internal_pointwise(now, a, b);
}

/// One object changed by an admissible sweeper edge, the rest untouched.
pub proof fn lemma_internal_one(now: nat, a: AState, b: AState, id: Seq<char>)
    requires
        a.objects.contains_key(id),
        b.objects.contains_key(id),
        forall|x: Seq<char>| x != id ==> #[trigger] crate::external::unchanged_at(a, b, x),
        consistent_task_state_edge_internal_admissible_at(now, b, id, a.objects[id]),
        consistent_promise_state_edge_internal_admissible_at(now, b, id, a.objects[id]),
    ensures
        internal_legal(now, a, b),
{
    assert forall|x: Seq<char>| #[trigger] internal_obj(now, a, b, x) by {
        if x != id {
            assert(crate::external::unchanged_at(a, b, x));
        }
    }
    lemma_internal_pointwise(now, a, b);
}

/// The retry dispatch: the task re-armed, an `execute` enqueued.
pub proof fn lemma_retry_legal(now: nat, a: AState, b: AState, id: Seq<char>, rt: nat)
    requires
        inv(now, a),
        0 < rt <= MAX_TIME as nat,
        a.objects.contains_key(id),
        a.objects[id].task is Some,
        a.objects[id].task.unwrap().state == TaskState::Pending,
        a.objects[id].task.unwrap().retry_timeout_at is Some,
        a.objects[id].task.unwrap().retry_timeout_at.unwrap() <= now,
        a.objects[id].state == PromiseState::Pending,
        a.objects[id].timeout_at > now,
        b.objects == a.objects.insert(id, a.objects[id].with_task(a.objects[id].task.unwrap().rearm(now, rt))),
        b.schedules == a.schedules,
        b.outbox == a.outbox.insert(OutboxKey::Execute(id), AOutboxEntry {
            address: target_or_empty(a.objects[id]),
            message: AMessage::Execute { task_id: id, version: a.objects[id].task.unwrap().version },
        }),
    ensures
        inv(now, b),
        legal(now, a, b),
{
    lemma_inv_pointwise(now, a);
    assert(inv_obj(now, a, id));
    let p = a.objects[id];
    let t = p.task.unwrap();
    let u = t.rearm(now, rt);
    let q = p.with_task(u);
    assert(b.objects[id] == q);
    assert forall|w: Seq<char>| #[trigger] a.objects.contains_key(w) implies
        b.objects.contains_key(w) && b.objects[w].tags == a.objects[w].tags
        && forall|z: Seq<char>| a.objects[w].callbacks.contains(z) ==> #[trigger] b.objects[w].callbacks.contains(z) by {
        if w != id {
            assert(b.objects.contains_key(w));
        }
    }
    lemma_task_edit_frame(now, a, b, id);
    assert(q.project_promise(now) == q);
    assert forall|i: int| 0 <= i < t.resumes.len() implies u.resumes.contains(#[trigger] t.resumes[i]) by {}
    assert(inv_obj(now, b, id));
    assert(trans_obj(now, a, b, id));
    // the outbox entry
    let k = OutboxKey::Execute(id);
    let e = b.outbox[k];
    assert(e.key() == k);
    assert(b.has_task(id));
    assert(b.task_of(id) == Some(u));
    assert(inv_out(now, b, k));
    assert(trans_out(now, a, b, k));
    assert forall|w: Seq<char>, z: Seq<char>| #[trigger] a.objects.contains_key(w)
        && #[trigger] a.objects[w].callbacks.contains(z)
        implies b.objects.contains_key(w) && b.objects[w].callbacks.contains(z) by {}
    assert forall|kk: OutboxKey| kk != k implies
        (a.outbox.contains_key(kk) <==> #[trigger] b.outbox.contains_key(kk))
        && (a.outbox.contains_key(kk) ==> a.outbox[kk] == b.outbox[kk]) by {}
    crate::properties_proof::lemma_step(now, a, b, |x: Seq<char>| x == id, |x: Seq<char>| false, |kk: OutboxKey| kk == k, |x: Seq<char>| false);
}

/// The listener drain: the promise was read, lost one listener, and the
/// listener's `unblock` was enqueued.
pub proof fn lemma_listener_legal(now: nat, a: AState, b: AState, id: Seq<char>, address: Seq<char>)
    requires
        inv(now, a),
        a.objects.contains_key(id),
        a.objects[id].project(now).state != PromiseState::Pending,
        a.objects[id].project(now).listeners.contains(address),
        b.objects == a.objects.insert(id, a.objects[id].project(now).remove_listener(address)),
        b.schedules == a.schedules,
        b.outbox == a.outbox.insert(OutboxKey::Notify(id, address), AOutboxEntry {
            address: address,
            message: AMessage::Unblock(a.objects[id].project(now).remove_listener(address).to_record()),
        }),
    ensures
        inv(now, b),
        legal(now, a, b),
{
    lemma_inv_pointwise(now, a);
    assert(inv_obj(now, a, id));
    let p = a.objects[id];
    let m = p.project(now);
    let q = m.remove_listener(address);
    assert(b.objects[id] == q);
    assert(q.callbacks == p.callbacks && q.tags == p.tags);
    assert(q.listeners == without(p.listeners, address));
    lemma_without_no_dups(p.listeners, address);
    assert forall|y: Seq<char>| #[trigger] q.listeners.contains(y) implies p.listeners.contains(y) && y != address by {
        lemma_without_contains(p.listeners, address, y);
    }
    assert(!q.listeners.contains(address)) by {
        lemma_without_contains(p.listeners, address, address);
    }
    assert forall|i: int| 0 <= i < q.listeners.len() implies p.listeners.contains(#[trigger] q.listeners[i]) by {
        assert(q.listeners.contains(q.listeners[i]));
    }
    assert forall|i: int| 0 <= i < p.callbacks.len() implies q.callbacks.contains(#[trigger] p.callbacks[i]) by {}
    assert forall|i: int| 0 <= i < q.callbacks.len() implies
        b.objects.contains_key(#[trigger] q.callbacks[i]) && b.objects[q.callbacks[i]].otype() == OType::Runnable by {
        assert(a.objects.contains_key(p.callbacks[i]) && a.objects[p.callbacks[i]].otype() == OType::Runnable);
    }
    // the settled promise's task is fulfilled, so no rung is owed
    assert(inv_obj(now, b, id));
    // the trans entries at id: the projection's, plus the listener consumed
    let k = OutboxKey::Notify(id, address);
    assert(b.outbox.contains_key(k));
    assert(b.outbox[k].key() == k);
    assert(one_unblock(b, id, address)) by {
        assert forall|kk: OutboxKey| #[trigger] b.outbox.contains_key(kk) && b.outbox[kk].address == address
            && (match b.outbox[kk].message { AMessage::Unblock(r) => r.id == id, AMessage::Execute { .. } => false })
            implies kk == k by {
            if kk != k {
                assert(a.outbox.contains_key(kk) && a.outbox[kk] == b.outbox[kk]);
                assert(inv_out(now, a, kk));
                assert(a.outbox[kk].key() == kk);
            }
        }
    }
    assert forall|i: int| 0 <= i < p.listeners.len() implies
        q.listeners.contains(#[trigger] p.listeners[i]) || one_unblock(b, id, p.listeners[i]) by {
        if p.listeners[i] != address {
            lemma_without_contains(p.listeners, address, p.listeners[i]);
        }
    }
    assert(trans_obj(now, a, b, id));
    // the outbox entry
    assert(inv_out(now, b, k));
    assert(trans_out(now, a, b, k));
    assert forall|w: Seq<char>, z: Seq<char>| #[trigger] a.objects.contains_key(w)
        && #[trigger] a.objects[w].callbacks.contains(z)
        implies b.objects.contains_key(w) && b.objects[w].callbacks.contains(z) by {}
    assert forall|kk: OutboxKey| kk != k implies
        (a.outbox.contains_key(kk) <==> #[trigger] b.outbox.contains_key(kk))
        && (a.outbox.contains_key(kk) ==> a.outbox[kk] == b.outbox[kk]) by {}
    crate::properties_proof::lemma_step(now, a, b, |x: Seq<char>| x == id, |x: Seq<char>| false, |kk: OutboxKey| kk == k, |x: Seq<char>| false);
}

/// The callback drain: the awaited promise, read and settled, lost the
/// awaiter's callback; the awaiter was read and resumed.
#[verifier::rlimit(120)]
pub proof fn lemma_callback_legal(now: nat, a: AState, b: AState, x: Seq<char>, y: Seq<char>, touched: bool)
    requires
        inv(now, a),
        x != y,
        a.objects.contains_key(x),
        a.objects[x].project(now).state != PromiseState::Pending,
        a.objects[x].project(now).callbacks.contains(y),
        b.objects.contains_key(x),
        b.objects[x] == a.objects[x].project(now).remove_callback(y),
        resumed_shape(now, a, b, x, y),
        forall|z: Seq<char>| z != x && z != y ==> #[trigger] crate::external::unchanged_at(a, b, z),
        b.schedules == a.schedules,
        b.outbox == a.outbox,
    ensures
        inv(now, b),
        legal(now, a, b),
        internal_legal(now, a, b),
{
    lemma_inv_pointwise(now, a);
    assert(inv_obj(now, a, x));
    let p = a.objects[x];
    let m = p.project(now);
    let q = m.remove_callback(y);
    assert(q.callbacks == without(p.callbacks, y));
    assert(q.listeners == p.listeners && q.tags == p.tags);
    lemma_without_no_dups(p.callbacks, y);
    assert forall|z: Seq<char>| #[trigger] q.callbacks.contains(z) implies p.callbacks.contains(z) && z != y by {
        lemma_without_contains(p.callbacks, y, z);
    }
    assert(!q.callbacks.contains(y)) by {
        lemma_without_contains(p.callbacks, y, y);
    }
    assert forall|z: Seq<char>| p.callbacks.contains(z) && z != y implies #[trigger] q.callbacks.contains(z) by {
        lemma_without_contains(p.callbacks, y, z);
    }
    // every object keeps its tags; callbacks other than `y`'s survive
    assert forall|w: Seq<char>| #[trigger] a.objects.contains_key(w) implies
        b.objects.contains_key(w) && b.objects[w].tags == a.objects[w].tags
        && forall|z: Seq<char>| a.objects[w].callbacks.contains(z) && z != y ==> #[trigger] b.objects[w].callbacks.contains(z) by {
        if w == x {
        } else if w == y {
            assert(resumed_shape(now, a, b, x, y));
        } else {
            assert(crate::external::unchanged_at(a, b, w));
        }
    }
    // --- the awaited object ---
    assert forall|i: int| 0 <= i < q.callbacks.len() implies
        b.objects.contains_key(#[trigger] q.callbacks[i]) && b.objects[q.callbacks[i]].otype() == OType::Runnable
        && crate::types::same_origin_spec(q.callbacks[i], x) by {
        assert(q.callbacks.contains(q.callbacks[i]));
        let z = q.callbacks[i];
        assert(p.callbacks.contains(z));
        let ii = choose|ii: int| 0 <= ii < p.callbacks.len() && p.callbacks[ii] == z;
        assert(a.objects.contains_key(z) && a.objects[z].otype() == OType::Runnable);
    }
    assert forall|i: int| 0 <= i < q.callbacks.len() implies p.callbacks.contains(#[trigger] q.callbacks[i]) by {
        assert(q.callbacks.contains(q.callbacks[i]));
    }
    assert forall|i: int| 0 <= i < p.listeners.len() implies q.listeners.contains(#[trigger] p.listeners[i]) by {}
    assert(inv_obj(now, b, x));
    // callback consumption resumes the awaiter
    assert forall|i: int| 0 <= i < p.callbacks.len() implies {
        let z = #[trigger] p.callbacks[i];
        q.callbacks.contains(z)
        || match b.task_of(z) {
            None => true,
            Some(u) => u.state == TaskState::Fulfilled || u.resumes.contains(x),
        }
    } by {
        let z = p.callbacks[i];
        if z == y {
            assert(resumed_shape(now, a, b, x, y));
            if a.objects.contains_key(y) {
                let py = a.objects[y];
                let my = py.project(now);
                if b.objects[y] == py && py.task is None {
                } else if b.objects[y] == my && (my.task is None || my.task.unwrap().state == TaskState::Fulfilled) {
                } else if my.task is Some && my.task.unwrap().state == TaskState::Suspended
                    && b.objects[y] == my.with_task(my.task.unwrap().wake(x, now)) {
                    assert(b.objects[y].task.unwrap().resumes == seq![x]);
                    assert(b.objects[y].task.unwrap().resumes[0] == x);
                } else {
                    let u = my.task.unwrap().buffer(x);
                    if my.task.unwrap().resumes.contains(x) {
                    } else {
                        assert(u.resumes[u.resumes.len() - 1] == x);
                    }
                }
            }
        } else {
            assert(p.callbacks.contains(z));
        }
    }
    assert(trans_obj(now, a, b, x));
    assert(internal_obj(now, a, b, x));
    // --- the awaiter ---
    if a.objects.contains_key(y) {
        assert(inv_obj(now, a, y));
        let py = a.objects[y];
        let my = py.project(now);
        assert(b.objects.contains_key(y));
        if b.objects[y] == py && py.task is None {
            assert(crate::external::unchanged_at(a, b, y));
            lemma_trans_obj_unchanged(now, a, b, y);
            lemma_callback_frame_obj(now, a, b, x, y, y);
        } else if b.objects[y] == my && (my.task is None || my.task.unwrap().state == TaskState::Fulfilled) {
            lemma_project_trans_obj(now, a, b, y);
            lemma_project_inv_obj_lost(now, a, b, y, y);
        } else if my.task is Some && my.task.unwrap().state == TaskState::Suspended
            && b.objects[y] == my.with_task(my.task.unwrap().wake(x, now)) {
            lemma_projected_task_identity(now, a, y);
            assert(my == py);
            let t = py.task.unwrap();
            let u = t.wake(x, now);
            let qy = py.with_task(u);
            assert(b.objects[y] == qy);
            assert(u.resumes == seq![x]);
            assert(u.resumes.len() == 1);
            assert(u.resumes[0] == x);
            assert(no_dups(u.resumes));
            assert(u.resumes.contains(x));
            lemma_callback_edit_frame(now, a, b, x, y);
            assert(qy.project_promise(now) == qy);
            assert(t.resumes.len() == 0);
            assert(inv_obj(now, b, y));
            // wake follows callback consumption: `x` is the witness
            assert(a.objects[x].callbacks.contains(y));
            assert(!b.objects[x].callbacks.contains(y));
            assert(trans_obj(now, a, b, y));
            assert(internal_obj(now, a, b, y));
        } else {
            lemma_projected_task_identity(now, a, y);
            assert(my == py);
            let t = py.task.unwrap();
            let u = t.buffer(x);
            let qy = py.with_task(u);
            assert(b.objects[y] == qy);
            if t.resumes.contains(x) {
                assert(u == t);
            } else {
                assert(u.resumes == t.resumes.push(x));
                assert(no_dups(u.resumes)) by {
                    assert forall|i: int, j: int| 0 <= i < u.resumes.len() && 0 <= j < u.resumes.len()
                        && u.resumes[i] == u.resumes[j] implies i == j by {
                        if i < t.resumes.len() && j < t.resumes.len() {
                        } else if i < t.resumes.len() {
                            assert(t.resumes[i] == x);
                        } else if j < t.resumes.len() {
                            assert(t.resumes[j] == x);
                        }
                    }
                }
            }
            assert forall|i: int| 0 <= i < t.resumes.len() implies u.resumes.contains(#[trigger] t.resumes[i]) by {
                if !t.resumes.contains(x) {
                    assert(u.resumes[i] == t.resumes[i]);
                }
            }
            lemma_callback_edit_frame(now, a, b, x, y);
            assert(qy.project_promise(now) == qy);
            // a suspended task is not buffered, so no rung moves
            assert(t.state != TaskState::Suspended);
            assert(inv_obj(now, b, y));
            assert(trans_obj(now, a, b, y));
            assert(internal_obj(now, a, b, y));
        }
    } else {
        assert(!b.objects.contains_key(y));
        assert(trans_obj(now, a, b, y));
        assert(internal_obj(now, a, b, y));
    }
    // --- the rest ---
    let changed = |z: Seq<char>| z == x || z == y;
    assert forall|z: Seq<char>| !changed(z) implies
        (a.objects.contains_key(z) <==> #[trigger] b.objects.contains_key(z))
        && (a.objects.contains_key(z) ==> a.objects[z] == b.objects[z]) by {
        assert(crate::external::unchanged_at(a, b, z));
    }
    assert forall|w: Seq<char>, z: Seq<char>| #[trigger] a.objects.contains_key(w)
        && #[trigger] a.objects[w].callbacks.contains(z) && z != y
        implies b.objects.contains_key(w) && b.objects[w].callbacks.contains(z) by {}
    assert forall|z: Seq<char>| #[trigger] changed(z) && b.objects.contains_key(z) implies inv_obj(now, b, z) by {}
    assert forall|z: Seq<char>| #[trigger] changed(z) implies trans_obj(now, a, b, z) by {}
    crate::properties_proof::lemma_step(now, a, b, changed, |z: Seq<char>| z == y, |k: OutboxKey| false, |z: Seq<char>| false);
    assert forall|z: Seq<char>| #[trigger] internal_obj(now, a, b, z) by {
        if !changed(z) {
            assert(crate::external::unchanged_at(a, b, z));
        }
    }
    lemma_internal_pointwise(now, a, b);
}

/// The awaiter's own pointers under the callback drain: it keeps its tags,
/// callbacks and listeners, and nothing it points at changed kind.
proof fn lemma_callback_edit_frame(now: nat, a: AState, b: AState, x: Seq<char>, y: Seq<char>)
    requires
        inv(now, a),
        x != y,
        a.objects.contains_key(y),
        b.objects.contains_key(y),
        b.objects[y].callbacks == a.objects[y].callbacks,
        b.objects[y].listeners == a.objects[y].listeners,
        b.objects[y].tags == a.objects[y].tags,
        forall|w: Seq<char>| #[trigger] a.objects.contains_key(w) ==>
            b.objects.contains_key(w) && b.objects[w].tags == a.objects[w].tags,
    ensures
        forall|i: int| 0 <= i < a.objects[y].callbacks.len() ==>
            b.objects[y].callbacks.contains(#[trigger] a.objects[y].callbacks[i]),
        forall|i: int| 0 <= i < a.objects[y].listeners.len() ==>
            b.objects[y].listeners.contains(#[trigger] a.objects[y].listeners[i]),
        consistent_callback_awaiter_is_targeted_at(now, b, b.objects[y]),
{
    lemma_inv_pointwise(now, a);
    assert(inv_obj(now, a, y));
    let p = a.objects[y];
    let q = b.objects[y];
    assert forall|i: int| 0 <= i < p.callbacks.len() implies q.callbacks.contains(#[trigger] p.callbacks[i]) by {}
    assert forall|i: int| 0 <= i < p.listeners.len() implies q.listeners.contains(#[trigger] p.listeners[i]) by {}
    assert forall|i: int| 0 <= i < q.callbacks.len() implies
        b.objects.contains_key(#[trigger] q.callbacks[i]) && b.objects[q.callbacks[i]].otype() == OType::Runnable by {
        assert(a.objects.contains_key(p.callbacks[i]) && a.objects[p.callbacks[i]].otype() == OType::Runnable);
        assert(b.objects[p.callbacks[i]].tags == a.objects[p.callbacks[i]].tags);
    }
}

/// An unchanged object whose task is not suspended, or whose rung is not
/// `lost`, still obeys the `.state` entries when only `lost`'s callbacks went.
proof fn lemma_callback_frame_obj(now: nat, a: AState, b: AState, x: Seq<char>, y: Seq<char>, z: Seq<char>)
    requires
        inv(now, a),
        a.objects.contains_key(z),
        b.objects.contains_key(z),
        a.objects[z] == b.objects[z],
        a.objects[z].task is None,
        forall|w: Seq<char>| #[trigger] a.objects.contains_key(w) ==>
            b.objects.contains_key(w) && b.objects[w].tags == a.objects[w].tags,
    ensures
        inv_obj(now, b, z),
{
    lemma_inv_pointwise(now, a);
    assert(inv_obj(now, a, z));
    let p = a.objects[z];
    assert forall|i: int| 0 <= i < p.callbacks.len() implies
        b.objects.contains_key(#[trigger] p.callbacks[i]) && b.objects[p.callbacks[i]].otype() == OType::Runnable by {
        assert(a.objects.contains_key(p.callbacks[i]) && a.objects[p.callbacks[i]].otype() == OType::Runnable);
        assert(b.objects[p.callbacks[i]].tags == a.objects[p.callbacks[i]].tags);
    }
}

/// A projected object whose task ends fulfilled or absent obeys the `.state`
/// entries, whatever happened to callbacks elsewhere.
proof fn lemma_project_inv_obj_lost(now: nat, a: AState, b: AState, id: Seq<char>, lost: Seq<char>)
    requires
        inv(now, a),
        a.objects.contains_key(id),
        b.objects.contains_key(id),
        b.objects[id] == a.objects[id].project(now),
        b.objects[id].task is None || b.objects[id].task.unwrap().state == TaskState::Fulfilled,
        forall|w: Seq<char>| #[trigger] a.objects.contains_key(w) ==>
            b.objects.contains_key(w) && b.objects[w].tags == a.objects[w].tags,
    ensures
        inv_obj(now, b, id),
{
    lemma_inv_pointwise(now, a);
    assert(inv_obj(now, a, id));
    let p = a.objects[id];
    let q = b.objects[id];
    assert forall|i: int| 0 <= i < q.callbacks.len() implies
        b.objects.contains_key(#[trigger] q.callbacks[i]) && b.objects[q.callbacks[i]].otype() == OType::Runnable by {
        assert(a.objects.contains_key(p.callbacks[i]) && a.objects[p.callbacks[i]].otype() == OType::Runnable);
        assert(b.objects[p.callbacks[i]].tags == a.objects[p.callbacks[i]].tags);
    }
}

/// Firing one occurrence on a fresh id is a legal step.
pub proof fn lemma_fire_birth_legal(now: nat, a: AState, b: AState, c: ASchedule, o: AOccurrence)
    requires
        inv(now, a),
        !a.objects.contains_key(o.promise_id),
        !crate::tags::timer_targeted(c.promise_tags),
        c.promise_timeout <= MAX_TIME as nat,
        o.at <= now,
        now <= MAX_TIME,
        b.objects == a.objects.insert(o.promise_id, spec_create(occ_req(c, o), birth_of(o, c, now))),
        b.schedules == a.schedules,
        b.outbox == a.outbox,
    ensures
        inv(now, b),
        legal(now, a, b),
        fire_shape(now, a, b, c, seq![o], o.promise_id),
{
    lemma_inv_pointwise(now, a);
    let req = occ_req(c, o);
    let t = birth_of(o, c, now);
    crate::tags_proof::lemma_stamp_timer(c.promise_tags, c.id, o.promise_id);
    assert(req.timeout_at <= 2 * (MAX_TIME as nat));
    assert(t <= now);
    assert(req.timeout_at <= t || req.timeout_at > now);
    lemma_born_obj(now, t, a, b, req);
    assert forall|w: Seq<char>, z: Seq<char>| #[trigger] a.objects.contains_key(w)
        && #[trigger] a.objects[w].callbacks.contains(z)
        implies b.objects.contains_key(w) && b.objects[w].callbacks.contains(z) by {}
    crate::properties_proof::lemma_step(now, a, b, |x: Seq<char>| x == o.promise_id, |x: Seq<char>| false, |k: OutboxKey| false, |x: Seq<char>| false);
    assert(seq![o][0] == o);
}

/// Projecting again an object the firing already touched leaves the shape.
pub proof fn lemma_fire_project_idem(now: nat, a: AState, s0: AState, b: AState, c: ASchedule, occs: Seq<AOccurrence>, x: Seq<char>)
    requires
        fire_shape(now, a, s0, c, occs, x),
        b.objects.contains_key(x),
        b.objects[x] == s0.objects[x].project(now),
    ensures
        fire_shape(now, a, b, c, occs, x),
{
    if a.objects.contains_key(x) {
        crate::external_proof::lemma_project_idem(a.objects[x], now);
    } else {
        let j = choose|j: int| 0 <= j < occs.len() && #[trigger] occs[j].promise_id == x
            && s0.objects[x] == spec_create(occ_req(c, occs[j]), birth_of(occs[j], c, now));
        let q = spec_create(occ_req(c, occs[j]), birth_of(occs[j], c, now));
        // a promise born live is ahead of `now`; one born dead is settled: both fixed by projection
        assert(q.project(now) == q);
    }
}

/// The first `k` occurrences fired: the catalogue holds, nothing else
/// moved, and each object touched has the firing's shape.
pub proof fn lemma_fire_fold(now: nat, a: AState, c: ASchedule, occs: Seq<AOccurrence>, k: int)
    requires
        inv(now, a),
        !crate::tags::timer_targeted(c.promise_tags),
        c.promise_timeout <= MAX_TIME as nat,
        forall|j: int| 0 <= j < occs.len() ==> #[trigger] occs[j].at <= now,
        now <= MAX_TIME,
        0 <= k <= occs.len(),
    ensures
        inv(now, fire_fold(now, a, c, occs, k)),
        fire_fold(now, a, c, occs, k).schedules == a.schedules,
        fire_fold(now, a, c, occs, k).outbox == a.outbox,
        forall|x: Seq<char>| !occ_touched(occs, k, x) ==> #[trigger] crate::external::unchanged_at(a, fire_fold(now, a, c, occs, k), x),
        forall|x: Seq<char>| #[trigger] occ_touched(occs, k, x) ==> fire_shape(now, a, fire_fold(now, a, c, occs, k), c, occs, x),
        a.objects.dom() <= fire_fold(now, a, c, occs, k).objects.dom(),
    decreases k,
{
    if k == 0 {
        assert forall|x: Seq<char>| !occ_touched(occs, 0, x) implies #[trigger] crate::external::unchanged_at(a, fire_fold(now, a, c, occs, 0), x) by {}
    } else {
        lemma_fire_fold(now, a, c, occs, k - 1);
        let s0 = fire_fold(now, a, c, occs, k - 1);
        let o = occs[k - 1];
        let x = o.promise_id;
        let b = fire_step(now, s0, c, o);
        if s0.objects.contains_key(x) {
            lemma_project_legal(now, s0, b, x);
            if !occ_touched(occs, k - 1, x) {
                assert(crate::external::unchanged_at(a, s0, x));
            }
        } else {
            if occ_touched(occs, k - 1, x) {
                assert(fire_shape(now, a, s0, c, occs, x));
                assert(false);
            }
            assert(crate::external::unchanged_at(a, s0, x));
            assert(!a.objects.contains_key(x));
            lemma_fire_birth_legal(now, s0, b, c, o);
        }
        assert forall|y: Seq<char>| #[trigger] occ_touched(occs, k, y) implies fire_shape(now, a, b, c, occs, y) by {
            if y == x {
                if s0.objects.contains_key(x) {
                    if occ_touched(occs, k - 1, x) {
                        lemma_fire_project_idem(now, a, s0, b, c, occs, x);
                    }
                } else {
                    assert(0 <= k - 1 < occs.len() && occs[k - 1].promise_id == x);
                }
            } else {
                let jj = choose|jj: int| 0 <= jj < k && #[trigger] occs[jj].promise_id == y;
                assert(jj < k - 1);
                assert(occ_touched(occs, k - 1, y));
                assert(fire_shape(now, a, s0, c, occs, y));
                assert(crate::external::unchanged_at(s0, b, y));
            }
        }
        assert forall|y: Seq<char>| !occ_touched(occs, k, y) implies #[trigger] crate::external::unchanged_at(a, b, y) by {
            assert(!occ_touched(occs, k - 1, y));
            assert(occs[k - 1].promise_id != y);
            assert(crate::external::unchanged_at(a, s0, y));
            assert(crate::external::unchanged_at(s0, b, y));
        }
    }
}

/// `spec_fire` keeps the catalogue and is an internal step.
pub proof fn lemma_spec_fire(now: nat, a: AState, sid: Seq<char>, occs: Seq<AOccurrence>, next: u64)
    requires
        inv(now, a),
        now <= MAX_TIME,
        forall|j: int| 0 <= j < occs.len() ==> #[trigger] occs[j].at <= now,
        forall|j: int, k: int| 0 <= j < k < occs.len() ==> #[trigger] occs[j].at < #[trigger] occs[k].at,
        occs.len() > 0 ==> next > occs[occs.len() - 1].at,
        a.schedules.contains_key(sid) && occs.len() > 0 ==> a.schedules[sid].next_run_at <= occs[0].at as nat,
    ensures
        inv(now, spec_fire(a, sid, occs, next, now)),
        legal(now, a, spec_fire(a, sid, occs, next, now)),
        internal_legal(now, a, spec_fire(a, sid, occs, next, now)),
        a.objects.dom() <= spec_fire(a, sid, occs, next, now).objects.dom(),
        a.schedules.contains_key(sid) ==> forall|j: int| 0 <= j < occs.len() ==> spec_fire(a, sid, occs, next, now).objects.contains_key(#[trigger] occs[j].promise_id),
        a.schedules.contains_key(sid) && occs.len() > 0 ==> spec_fire(a, sid, occs, next, now).schedules
            == a.schedules.insert(sid, ASchedule { last_run_at: Some(occs[occs.len() - 1].at), next_run_at: next, ..a.schedules[sid] }),
        !(a.schedules.contains_key(sid) && occs.len() > 0) ==> spec_fire(a, sid, occs, next, now) == a,
{
    if !a.schedules.contains_key(sid) || occs.len() == 0 {
        crate::properties_proof::lemma_noop(now, a);
        lemma_internal_noop(now, a);
    } else {
        let c = a.schedules[sid];
        lemma_inv_pointwise(now, a);
        assert(inv_sched(now, a, sid));
        lemma_fire_fold(now, a, c, occs, occs.len() as int);
        let a2 = fire_fold(now, a, c, occs, occs.len() as int);
        let b = spec_fire(a, sid, occs, next, now);
        lemma_fire_legal(now, a, a2, b, sid, occs, next);
        assert forall|j: int| 0 <= j < occs.len() implies b.objects.contains_key(#[trigger] occs[j].promise_id) by {
            assert(occ_touched(occs, occs.len() as int, occs[j].promise_id));
            assert(fire_shape(now, a, a2, c, occs, occs[j].promise_id));
        }
    }
}

/// `processSchedule` as one step: the objects fired, the schedule advanced.
pub proof fn lemma_fire_legal(now: nat, a: AState, a2: AState, b: AState, sid: Seq<char>, occs: Seq<AOccurrence>, next: u64)
    requires
        inv(now, a),
        inv(now, a2),
        a.schedules.contains_key(sid),
        occs.len() > 0,
        forall|j: int| 0 <= j < occs.len() ==> #[trigger] occs[j].at <= now,
        a.schedules[sid].next_run_at <= occs[0].at as nat,
        forall|j: int, k: int| 0 <= j < k < occs.len() ==> #[trigger] occs[j].at < #[trigger] occs[k].at,
        next > occs[occs.len() - 1].at,
        forall|x: Seq<char>| !occ_of(occs, x) ==> #[trigger] crate::external::unchanged_at(a, a2, x),
        forall|x: Seq<char>| #[trigger] occ_of(occs, x) ==> fire_shape(now, a, a2, a.schedules[sid], occs, x),
        a2.schedules == a.schedules,
        a2.outbox == a.outbox,
        b.objects == a2.objects,
        b.outbox == a2.outbox,
        b.schedules == a2.schedules.insert(sid, ASchedule {
            last_run_at: Some(occs[occs.len() - 1].at),
            next_run_at: next,
            ..a.schedules[sid]
        }),
    ensures
        inv(now, b),
        legal(now, a, b),
        internal_legal(now, a, b),
{
    lemma_inv_pointwise(now, a);
    lemma_inv_pointwise(now, a2);
    let c = a.schedules[sid];
    assert(inv_sched(now, a, sid));
    assert(c.created_at <= c.next_run_at);
    let last = occs[occs.len() - 1].at as nat;
    assert(occs[0].at <= occs[occs.len() - 1].at) by {
        if occs.len() > 1 {
            assert(occs[0].at < occs[occs.len() - 1].at);
        }
    }
    // the objects: a2 relative to a, pointwise
    assert forall|w: Seq<char>| #[trigger] a.objects.contains_key(w) implies
        b.objects.contains_key(w) && b.objects[w].callbacks == a.objects[w].callbacks
        && b.objects[w].tags == a.objects[w].tags by {
        if occ_of(occs, w) {
            assert(fire_shape(now, a, a2, c, occs, w));
        } else {
            assert(crate::external::unchanged_at(a, a2, w));
        }
    }
    assert forall|x: Seq<char>| #[trigger] occ_of(occs, x) implies inv_obj(now, b, x) && trans_obj(now, a, b, x) by {
        assert(fire_shape(now, a, a2, c, occs, x));
        if a.objects.contains_key(x) {
            lemma_project_inv_obj(now, a, b, x);
            lemma_project_trans_obj(now, a, b, x);
        } else {
            let j = choose|j: int| 0 <= j < occs.len() && #[trigger] occs[j].promise_id == x
                && a2.objects[x] == spec_create(occ_req(c, occs[j]), birth_of(occs[j], c, now));
            let req = occ_req(c, occs[j]);
            let t = birth_of(occs[j], c, now);
            assert(inv_sched(now, a, sid));
            assert(c.promise_timeout <= MAX_TIME as nat);
            crate::tags_proof::lemma_stamp_timer(c.promise_tags, c.id, occs[j].promise_id);
            assert(req.timeout_at <= 2 * (MAX_TIME as nat));
            lemma_born_obj(now, t, a, b, req);
        }
    }
    assert forall|x: Seq<char>| !occ_of(occs, x) implies
        (a.objects.contains_key(x) <==> #[trigger] b.objects.contains_key(x))
        && (a.objects.contains_key(x) ==> a.objects[x] == b.objects[x]) by {
        assert(crate::external::unchanged_at(a, a2, x));
    }
    assert forall|w: Seq<char>, z: Seq<char>| #[trigger] a.objects.contains_key(w)
        && #[trigger] a.objects[w].callbacks.contains(z)
        implies b.objects.contains_key(w) && b.objects[w].callbacks.contains(z) by {}
    // the schedule
    assert(inv_sched(now, b, sid));
    assert(trans_sched(now, a, b, sid));
    assert forall|x: Seq<char>| x != sid implies
        (a.schedules.contains_key(x) <==> #[trigger] b.schedules.contains_key(x))
        && (a.schedules.contains_key(x) ==> a.schedules[x] == b.schedules[x]) by {}
    crate::properties_proof::lemma_step(now, a, b, |x: Seq<char>| occ_of(occs, x), |x: Seq<char>| false, |k: OutboxKey| false, |x: Seq<char>| x == sid);
    // sweeper entries: births are vacuous, projections admissible
    assert forall|x: Seq<char>| #[trigger] internal_obj(now, a, b, x) by {
        if occ_of(occs, x) {
            assert(fire_shape(now, a, a2, c, occs, x));
        } else {
            assert(crate::external::unchanged_at(a, a2, x));
        }
    }
    lemma_internal_pointwise(now, a, b);
}

} // verus!
