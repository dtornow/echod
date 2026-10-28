//! Pure ghost semantics for the six Abstract Promise external actions.
//!
//! These definitions do not call an executable, kernel, or concrete handler.
//! Every read is evaluated against the same `AState`; effects are accumulated
//! in writer order and committed only by `spec_apply_all`.

use vstd::prelude::*;
use crate::state::*;
use crate::types::*;

verus! {

#[cfg(verus_keep_ghost)]
pub struct APromiseActionResult {
    pub response: APromiseRes,
    pub effects: Seq<AEffect>,
    pub next_state: AState,
}

#[cfg(verus_keep_ghost)]
pub struct APromiseSearchActionResult {
    pub response: APromiseSearchRes,
    pub effects: Seq<AEffect>,
    pub next_state: AState,
}

#[cfg(verus_keep_ghost)]
pub struct AReadResult {
    pub object: Option<AObject>,
    pub effects: Seq<AEffect>,
}

#[cfg(verus_keep_ghost)]
pub struct ACreated {
    pub object: AObject,
    pub effects: Seq<AEffect>,
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_promise_finish(
    state: AState,
    response: APromiseRes,
    effects: Seq<AEffect>,
) -> APromiseActionResult {
    APromiseActionResult {
        response,
        effects,
        next_state: spec_apply_all(state, effects),
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_promise_search_finish(
    state: AState,
    response: APromiseSearchRes,
    effects: Seq<AEffect>,
) -> APromiseSearchActionResult {
    APromiseSearchActionResult {
        response,
        effects,
        next_state: spec_apply_all(state, effects),
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_promise_error(status: u16) -> APromiseRes {
    APromiseRes { status, promise: None }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_value_empty() -> AValue {
    AValue { headers: Seq::empty(), data: None }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_promise_record(p: APromiseObject, id: AIdent) -> APromiseRecord {
    APromiseRecord {
        id,
        state: p.state,
        param: p.param,
        value: p.value,
        tags: p.tags,
        timeout_at: p.timeout_at,
        created_at: p.created_at,
        settled_at: p.settled_at,
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_settable(state: PromiseState) -> bool {
    state == PromiseState::Resolved
        || state == PromiseState::Rejected
        || state == PromiseState::RejectedCanceled
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_awaitable(otype: OType) -> bool {
    otype != OType::Internal
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_text_eq(a: AText, b: AText) -> bool {
    a == b
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_ident_eq(a: AIdent, b: AIdent) -> bool {
    a == b
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_same_origin(a: AIdent, b: AIdent) -> bool {
    a.origin == b.origin
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_key_prefix(key: AText) -> bool {
    key.chars.len() >= 9
        && key.chars[0] == 'r' && key.chars[1] == 'e'
        && key.chars[2] == 's' && key.chars[3] == 'o'
        && key.chars[4] == 'n' && key.chars[5] == 'a'
        && key.chars[6] == 't' && key.chars[7] == 'e'
        && key.chars[8] == ':'
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_key_target(key: AText) -> bool {
    spec_key_prefix(key) && key.chars.len() == 15
        && key.chars[9] == 't' && key.chars[10] == 'a'
        && key.chars[11] == 'r' && key.chars[12] == 'g'
        && key.chars[13] == 'e' && key.chars[14] == 't'
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_key_scope(key: AText) -> bool {
    spec_key_prefix(key) && key.chars.len() == 14
        && key.chars[9] == 's' && key.chars[10] == 'c'
        && key.chars[11] == 'o' && key.chars[12] == 'p'
        && key.chars[13] == 'e'
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_key_external(key: AText) -> bool {
    spec_key_prefix(key) && key.chars.len() == 17
        && key.chars[9] == 'e' && key.chars[10] == 'x'
        && key.chars[11] == 't' && key.chars[12] == 'e'
        && key.chars[13] == 'r' && key.chars[14] == 'n'
        && key.chars[15] == 'a' && key.chars[16] == 'l'
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_key_delay(key: AText) -> bool {
    spec_key_prefix(key) && key.chars.len() == 14
        && key.chars[9] == 'd' && key.chars[10] == 'e'
        && key.chars[11] == 'l' && key.chars[12] == 'a'
        && key.chars[13] == 'y'
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_text_global(x: AText) -> bool {
    x.chars.len() == 6
        && x.chars[0] == 'g' && x.chars[1] == 'l'
        && x.chars[2] == 'o' && x.chars[3] == 'b'
        && x.chars[4] == 'a' && x.chars[5] == 'l'
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_tag_value(tags: ATags, which: u8) -> Option<AText>
{
    crate::types::spec_tag_value(tags, which)
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_tags_has_target(tags: ATags) -> bool {
    crate::types::spec_has_target(tags)
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_tags_timer_targeted(tags: ATags) -> bool {
    crate::types::spec_is_timer(tags) && crate::types::spec_has_target(tags)
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_tags_otype(tags: ATags) -> OType {
    crate::types::spec_otype(tags)
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_digit(c: char) -> u64 {
    if c == '0' { 0 } else if c == '1' { 1 } else if c == '2' { 2 }
    else if c == '3' { 3 } else if c == '4' { 4 } else if c == '5' { 5 }
    else if c == '6' { 6 } else if c == '7' { 7 } else if c == '8' { 8 }
    else if c == '9' { 9 } else { 0 }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_parse_nat_from(chars: Seq<char>, acc: u64) -> u64
    decreases chars.len(),
{
    if chars.len() == 0 {
        acc
    } else if acc > MAX_TIME / 10 {
        MAX_TIME
    } else {
        let ten = acc * 10;
        let digit = spec_digit(chars[0]);
        if digit > MAX_TIME - ten {
            MAX_TIME
        } else {
            spec_parse_nat_from(chars.drop_first(), (ten + digit) as u64)
        }
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_parse_nat_bounded(x: AText) -> u64 {
    crate::types::spec_parse_nat_bounded(x)
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_promise_project(p: APromiseObject, now: u64) -> APromiseObject {
    crate::state::spec_project_promise(p, now)
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_task_fulfill(t: ATaskObject) -> ATaskObject {
    crate::state::spec_fulfill_task(t)
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_task_view(t: ATaskObject, p: APromiseObject) -> ATaskObject {
    if p.state != PromiseState::Pending && t.state != TaskState::Fulfilled {
        spec_task_fulfill(t)
    } else {
        t
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_object_project(o: AObject, now: u64) -> AObject {
    crate::state::spec_project_object(o, now)
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_add_callback(p: APromiseObject, id: AIdent) -> APromiseObject {
    crate::state::spec_add_callback(p, id)
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_add_listener(p: APromiseObject, address: AText) -> APromiseObject {
    crate::state::spec_add_listener(p, address)
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_contains_ident(ids: Seq<AIdent>, id: AIdent) -> bool
{
    ids.contains(id)
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_contains_text(xs: Seq<AText>, x: AText) -> bool
{
    xs.contains(x)
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_materialize_effects(
    id: AIdent,
    old: AObject,
    projected: AObject,
    materialize: bool,
) -> Seq<AEffect> {
    if !materialize {
        Seq::empty()
    } else {
        let promise_effects =
            if projected.promise.state != old.promise.state {
                seq![AEffect::SetPromise(id, projected.promise)]
            } else {
                Seq::empty()
            };
        let task_effects = match (old.task, projected.task) {
            (Some(a), Some(b)) if a.state != b.state =>
                seq![AEffect::SetTask(id, b)],
            _ => Seq::empty(),
        };
        promise_effects + task_effects
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_read_object(
    state: AState,
    id: AIdent,
    now: u64,
    materialize: bool,
) -> AReadResult {
    AReadResult {
        object: crate::state::spec_read_object(state, id, now),
        effects: crate::state::spec_read_effects(state, id, now, materialize),
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_set_settled_effects(
    object: AObject,
    promise: APromiseObject,
) -> Seq<AEffect> {
    crate::state::spec_set_settled_effects(object, promise)
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_create_promise(req: APromiseCreateReq, now: u64) -> ACreated {
    let promise = crate::state::spec_created_promise(req, now);
    ACreated {
        object: AObject {
            id: req.id,
            promise,
            task: crate::state::spec_created_task(promise, now),
        },
        effects: crate::state::spec_create_promise_effects(req, now),
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_promise_get_action(
    state: AState,
    req: APromiseGetReq,
    now: u64,
    materialize: bool,
) -> APromiseActionResult {
    let read = spec_read_object(state, req.id, now, materialize);
    match read.object {
        None => spec_promise_finish(state, spec_promise_error(404), read.effects),
        Some(object) => spec_promise_finish(
            state,
            APromiseRes {
                status: 200,
                promise: Some(spec_promise_record(object.promise, object.id)),
            },
            read.effects,
        ),
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_promise_create_action(
    state: AState,
    req: APromiseCreateReq,
    now: u64,
    materialize: bool,
) -> APromiseActionResult {
    if spec_tags_timer_targeted(req.tags) {
        spec_promise_finish(state, spec_promise_error(400), Seq::empty())
    } else {
        let read = spec_read_object(state, req.id, now, materialize);
        match read.object {
            Some(object) => spec_promise_finish(
                state,
                APromiseRes {
                    status: 200,
                    promise: Some(spec_promise_record(object.promise, object.id)),
                },
                read.effects,
            ),
            None => {
                let made = spec_create_promise(req, now);
                spec_promise_finish(
                    state,
                    APromiseRes {
                        status: 200,
                        promise: Some(spec_promise_record(
                            made.object.promise,
                            made.object.id,
                        )),
                    },
                    read.effects + made.effects,
                )
            }
        }
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_promise_settle_action(
    state: AState,
    req: APromiseSettleReq,
    now: u64,
    materialize: bool,
) -> APromiseActionResult {
    if !spec_settable(req.state) {
        spec_promise_finish(state, spec_promise_error(400), Seq::empty())
    } else {
        let read = spec_read_object(state, req.id, now, materialize);
        match read.object {
            None => spec_promise_finish(state, spec_promise_error(404), read.effects),
            Some(object) => {
                if object.promise.state == PromiseState::Pending {
                    let promise = APromiseObject {
                        state: req.state,
                        value: req.value,
                        settled_at: Some(now),
                        ..object.promise
                    };
                    spec_promise_finish(
                        state,
                        APromiseRes {
                            status: 200,
                            promise: Some(spec_promise_record(promise, object.id)),
                        },
                        read.effects + spec_set_settled_effects(object, promise),
                    )
                } else {
                    spec_promise_finish(
                        state,
                        APromiseRes {
                            status: 200,
                            promise: Some(spec_promise_record(object.promise, object.id)),
                        },
                        read.effects,
                    )
                }
            }
        }
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_promise_register_callback_action(
    state: AState,
    req: APromiseRegisterCallbackReq,
    now: u64,
    materialize: bool,
) -> APromiseActionResult {
    if spec_ident_eq(req.awaited, req.awaiter)
        || !spec_same_origin(req.awaited, req.awaiter)
    {
        spec_promise_finish(state, spec_promise_error(400), Seq::empty())
    } else {
        let awaited = spec_read_object(state, req.awaited, now, materialize);
        match awaited.object {
            None => spec_promise_finish(
                state,
                spec_promise_error(404),
                awaited.effects,
            ),
            Some(oa) => {
                // Reader semantics: this is another read of `state`, not of a
                // state obtained by applying `awaited.effects`.
                let awaiter = spec_read_object(state, req.awaiter, now, materialize);
                let reads = awaited.effects + awaiter.effects;
                match awaiter.object {
                    None => spec_promise_finish(state, spec_promise_error(422), reads),
                    Some(ow) => {
                        if spec_tags_otype(ow.promise.tags) != OType::Runnable
                            || !spec_awaitable(spec_tags_otype(oa.promise.tags))
                        {
                            spec_promise_finish(state, spec_promise_error(422), reads)
                        } else {
                            let effects =
                                if oa.promise.state == PromiseState::Pending
                                    && ow.promise.state == PromiseState::Pending
                                {
                                    reads.push(AEffect::SetPromise(
                                        oa.id,
                                        spec_add_callback(oa.promise, req.awaiter),
                                    ))
                                } else {
                                    reads
                                };
                            spec_promise_finish(
                                state,
                                APromiseRes {
                                    status: 200,
                                    promise: Some(spec_promise_record(oa.promise, oa.id)),
                                },
                                effects,
                            )
                        }
                    }
                }
            }
        }
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_promise_register_listener_action(
    state: AState,
    req: APromiseRegisterListenerReq,
    now: u64,
    materialize: bool,
) -> APromiseActionResult {
    let read = spec_read_object(state, req.awaited, now, materialize);
    match read.object {
        None => spec_promise_finish(state, spec_promise_error(404), read.effects),
        Some(object) => {
            if !spec_awaitable(spec_tags_otype(object.promise.tags)) {
                spec_promise_finish(state, spec_promise_error(422), read.effects)
            } else {
                let effects = if object.promise.state == PromiseState::Pending {
                    read.effects.push(AEffect::SetPromise(
                        object.id,
                        spec_add_listener(object.promise, req.address),
                    ))
                } else {
                    read.effects
                };
                spec_promise_finish(
                    state,
                    APromiseRes {
                        status: 200,
                        promise: Some(spec_promise_record(object.promise, object.id)),
                    },
                    effects,
                )
            }
        }
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_promise_search_action(
    state: AState,
    _req: APromiseSearchReq,
    _now: u64,
    _materialize: bool,
) -> APromiseSearchActionResult {
    spec_promise_search_finish(
        state,
        APromiseSearchRes {
            status: 501,
            promises: Seq::empty(),
            cursor: None,
        },
        Seq::empty(),
    )
}

} // verus!
