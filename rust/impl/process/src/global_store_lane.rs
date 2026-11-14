//! Document-lane ownership and queue serialization for invariant 1.

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports, dead_code))]

use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::handler_docs::{FiringSpec, FlightsSpec, WorkSpec};
#[cfg(verus_keep_ghost)]
use crate::state::S;
#[cfg(verus_keep_ghost)]
use crate::target::TargetSpec;

#[cfg(verus_keep_ghost)]
verus! {

pub open spec fn lane_has_no_active_flight(
    flights: FlightsSpec,
    name: Seq<char>,
) -> bool {
    forall|fid: u64|
        flights.inflight.contains_key(fid) ==>
            crate::target::spec_name(
                flights.inflight[fid].target,
            ) != name
}

pub open spec fn lane_has_no_secondary_flight_owner(
    flights: FlightsSpec,
    name: Seq<char>,
) -> bool {
    forall|fid: u64|
        flights.inflight.contains_key(fid) ==> {
            match #[trigger] flights.inflight[fid].phase {
                crate::handler_docs::PhaseSpec::FireLoadingOrigin {
                    ctx,
                    ..
                }
                | crate::handler_docs::PhaseSpec::FireOrigin {
                    ctx,
                    ..
                } =>
                    crate::target::spec_name(
                        crate::target::TargetSpec::Origin(ctx.origin),
                    ) != name,
                _ => true,
            }
        }
}

pub open spec fn secondary_flight_lanes_consistent(
    state: S,
) -> bool {
    forall|fid: u64|
        state.flights.inflight.contains_key(fid) ==> {
            match #[trigger] state.flights.inflight[fid].phase {
                crate::handler_docs::PhaseSpec::FireLoadingOrigin {
                    ctx,
                    ..
                }
                | crate::handler_docs::PhaseSpec::FireOrigin {
                    ctx,
                    ..
                } => {
                    let name = crate::target::spec_name(
                        crate::target::TargetSpec::Origin(ctx.origin),
                    );
                    &&& state.flights.slots.contains_key(name)
                    &&& state.flights.slots[name].busy == Some(fid)
                },
                _ => true,
            }
        }
}

pub open spec fn detached_flight_owns_primary(
    state: S,
    flight: crate::handler_docs::FlightSpec,
) -> bool {
    let primary = crate::target::spec_name(flight.target);
    &&& !state.flights.inflight.contains_key(flight.id)
    &&& state.flights.slots.contains_key(primary)
    &&& state.flights.slots[primary].busy == Some(flight.id)
}

pub proof fn lemma_detached_busy_owner_leaves_secondary_lane_unowned(
    state: S,
    name: Seq<char>,
    owner: u64,
)
    requires
        secondary_flight_lanes_consistent(state),
        state.flights.slots.contains_key(name),
        state.flights.slots[name].busy == Some(owner),
        !state.flights.inflight.contains_key(owner),
    ensures
        lane_has_no_secondary_flight_owner(state.flights, name),
{
    reveal(secondary_flight_lanes_consistent);
    reveal(lane_has_no_secondary_flight_owner);
    assert forall|fid: u64|
        state.flights.inflight.contains_key(fid) implies {
            match #[trigger] state.flights.inflight[fid].phase {
                crate::handler_docs::PhaseSpec::FireLoadingOrigin {
                    ctx,
                    ..
                }
                | crate::handler_docs::PhaseSpec::FireOrigin {
                    ctx,
                    ..
                } =>
                    crate::target::spec_name(
                        crate::target::TargetSpec::Origin(ctx.origin),
                    ) != name,
                _ => true,
            }
        } by {
        match state.flights.inflight[fid].phase {
            crate::handler_docs::PhaseSpec::FireLoadingOrigin {
                ctx,
                ..
            }
            | crate::handler_docs::PhaseSpec::FireOrigin {
                ctx,
                ..
            } => {
                let secondary = crate::target::spec_name(
                    crate::target::TargetSpec::Origin(ctx.origin),
                );
                if secondary == name {
                    assert(state.flights.slots[name].busy
                        == Some(fid));
                    assert(fid == owner);
                    assert(false);
                }
            },
            _ => {},
        }
    };
}

pub proof fn lemma_detached_busy_owner_leaves_lane_unowned(
    flights: FlightsSpec,
    name: Seq<char>,
    owner: u64,
)
    requires
        crate::production_relation::flight_lanes_consistent(flights),
        flights.slots.contains_key(name),
        flights.slots[name].busy == Some(owner),
        !flights.inflight.contains_key(owner),
    ensures
        lane_has_no_active_flight(flights, name),
{
    reveal(crate::production_relation::flight_lanes_consistent);
    reveal(lane_has_no_active_flight);
    assert forall|fid: u64|
        flights.inflight.contains_key(fid) implies
            crate::target::spec_name(
                flights.inflight[fid].target,
            ) != name by {
        if crate::target::spec_name(
            flights.inflight[fid].target,
        ) == name {
            assert(flights.slots[name].busy == Some(fid));
            assert(fid == owner);
            assert(false);
        }
    };
}

pub proof fn lemma_take_flight_leaves_its_lane_unowned(
    state: S,
    fid: u64,
)
    requires
        crate::production_relation::flight_lanes_consistent(
            state.flights,
        ),
        state.flights.inflight.contains_key(fid),
    ensures
        lane_has_no_active_flight(
            crate::handler_docs::spec_take_flight(state, fid).flights,
            crate::target::spec_name(
                state.flights.inflight[fid].target,
            ),
        ),
{
    reveal(crate::production_relation::flight_lanes_consistent);
    reveal(lane_has_no_active_flight);
    reveal(crate::handler_docs::spec_take_flight);
    let name = crate::target::spec_name(
        state.flights.inflight[fid].target,
    );
    assert forall|other: u64|
        crate::handler_docs::spec_take_flight(state, fid)
            .flights.inflight.contains_key(other) implies
                crate::target::spec_name(
                    crate::handler_docs::spec_take_flight(
                        state,
                        fid,
                    ).flights.inflight[other].target,
                ) != name by {
        assert(other != fid);
        if crate::target::spec_name(
            state.flights.inflight[other].target,
        ) == name {
            assert(state.flights.slots[name].busy == Some(fid));
            assert(state.flights.slots[name].busy == Some(other));
            assert(false);
        }
    };
}

pub proof fn lemma_take_flight_preserves_primary_slot_ownership(
    state: S,
    fid: u64,
)
    requires
        crate::production_relation::flight_lanes_consistent(
            state.flights,
        ),
        state.flights.inflight.contains_key(fid),
    ensures
        ({
            let primary = crate::target::spec_name(
                state.flights.inflight[fid].target,
            );
            let detached =
                crate::handler_docs::spec_take_flight(state, fid);
            &&& detached.flights.slots == state.flights.slots
            &&& detached.flights.slots.contains_key(primary)
            &&& detached.flights.slots[primary].busy == Some(fid)
        }),
{
    reveal(crate::handler_docs::spec_take_flight);
    reveal(crate::production_relation::flight_lanes_consistent);
}

/// A physical document lane has at most one active flight. Any Store
/// mutation owned by a flight is therefore issued by that unique owner.
pub proof fn lemma_document_lane_has_one_active_owner(
    flights: FlightsSpec,
    left: u64,
    right: u64,
)
    requires
        crate::production_relation::flight_lanes_consistent(flights),
        flights.inflight.contains_key(left),
        flights.inflight.contains_key(right),
        crate::target::spec_name(flights.inflight[left].target)
            == crate::target::spec_name(flights.inflight[right].target),
    ensures
        left == right,
{
    crate::production_relation::lemma_same_lane_active_flight_is_unique(
        flights,
        left,
        right,
    );
}

/// Busy-lane submission only appends queue data. It neither starts another
/// flight nor creates a Store operation.
pub proof fn lemma_busy_document_lane_only_queues(
    state: S,
    target: TargetSpec,
    work: WorkSpec,
    firing: Option<FiringSpec>,
    debug: bool,
)
    requires
        ({
            let name = crate::target::spec_name(target);
            let noted = match work {
                WorkSpec::Sweep { now, .. } =>
                    crate::state::spec_note(
                        state,
                        crate::types::NoteSpec::SweepBegin {
                            flight: state.next_flight,
                            target: name,
                            now,
                        },
                    ),
                _ => state,
            };
            crate::handler_docs::spec_slot_of(noted, name).busy is Some
        }),
    ensures
        ({
            let next = crate::handler_docs::spec_submit(
                state,
                target,
                work,
                firing,
                debug,
            );
            &&& next.ops == state.ops
            &&& next.store_requests == state.store_requests
            &&& next.store_certificates == state.store_certificates
            &&& next.flights.inflight == state.flights.inflight
        }),
{
    crate::production_relation::lemma_busy_lane_submission_is_queued(
        state,
        target,
        work,
        firing,
        debug,
    );
    reveal(crate::handler_docs::spec_with_slot);
    reveal(crate::handler_docs::spec_without_slot);
    reveal(crate::state::spec_note);
}

proof fn lemma_claim_free_lane_preserves_existing_ownership(
    state: S,
    name: Seq<char>,
    owner: u64,
    queue: Seq<crate::handler_docs::QueuedSpec>,
)
    requires
        crate::production_relation::flight_lanes_consistent(
            state.flights,
        ),
        crate::handler_docs::spec_slot_of(state, name).busy is None,
    ensures
        crate::production_relation::flight_lanes_consistent(
            crate::handler_docs::spec_with_slot(
                state,
                name,
                crate::handler_docs::SlotSpec {
                    busy: Some(owner),
                    queue,
                },
            ).flights,
        ),
{
    reveal(crate::production_relation::flight_lanes_consistent);
    reveal(crate::handler_docs::spec_with_slot);
    reveal(crate::handler_docs::spec_slot_of);
    let next = crate::handler_docs::spec_with_slot(
        state,
        name,
        crate::handler_docs::SlotSpec {
            busy: Some(owner),
            queue,
        },
    );
    assert forall|fid: u64|
        next.flights.inflight.contains_key(fid) implies {
            let flight = #[trigger] next.flights.inflight[fid];
            let flight_name =
                crate::target::spec_name(flight.target);
            &&& next.flights.slots.contains_key(flight_name)
            &&& next.flights.slots[flight_name].busy == Some(fid)
        } by {
        let flight = state.flights.inflight[fid];
        let flight_name = crate::target::spec_name(flight.target);
        if flight_name == name {
            assert(state.flights.slots.contains_key(name));
            assert(state.flights.slots[name].busy == Some(fid));
            assert(false);
        }
    };
}

pub proof fn lemma_attach_owned_flight_preserves_lane_ownership(
    state: S,
    flight: crate::handler_docs::FlightSpec,
)
    requires
        crate::production_relation::flight_lanes_consistent(
            state.flights,
        ),
        secondary_flight_lanes_consistent(state),
        !state.flights.inflight.contains_key(flight.id),
        state.flights.slots.contains_key(
            crate::target::spec_name(flight.target),
        ),
        state.flights.slots[
            crate::target::spec_name(flight.target)
        ].busy == Some(flight.id),
        match flight.phase {
            crate::handler_docs::PhaseSpec::FireLoadingOrigin {
                ctx,
                ..
            }
            | crate::handler_docs::PhaseSpec::FireOrigin {
                ctx,
                ..
            } => {
                let name = crate::target::spec_name(
                    crate::target::TargetSpec::Origin(ctx.origin),
                );
                &&& state.flights.slots.contains_key(name)
                &&& state.flights.slots[name].busy == Some(flight.id)
            },
            _ => true,
        },
    ensures
        crate::production_relation::flight_lanes_consistent(
            crate::handler_docs::spec_inflight(state, flight).flights,
        ),
        secondary_flight_lanes_consistent(
            crate::handler_docs::spec_inflight(state, flight),
        ),
{
    reveal(crate::production_relation::flight_lanes_consistent);
    reveal(secondary_flight_lanes_consistent);
    reveal(crate::handler_docs::spec_inflight);
    let next = crate::handler_docs::spec_inflight(state, flight);
    assert forall|fid: u64|
        next.flights.inflight.contains_key(fid) implies {
            let active = #[trigger] next.flights.inflight[fid];
            let name = crate::target::spec_name(active.target);
            &&& next.flights.slots.contains_key(name)
            &&& next.flights.slots[name].busy == Some(fid)
        } by {
        if fid == flight.id {
            assert(next.flights.inflight[fid] == flight);
        } else {
            assert(next.flights.inflight[fid]
                == state.flights.inflight[fid]);
        }
    };
}

proof fn lemma_abandon_unowned_lane_preserves_lane_ownership(
    state: S,
    name: Seq<char>,
)
    requires
        crate::production_relation::flight_lanes_consistent(
            state.flights,
        ),
        forall|fid: u64|
            state.flights.inflight.contains_key(fid) ==>
                crate::target::spec_name(
                    state.flights.inflight[fid].target,
                ) != name,
    ensures
        crate::production_relation::flight_lanes_consistent(
            crate::handler_docs::spec_abandon_slot(state, name).flights,
        ),
{
    reveal(crate::production_relation::flight_lanes_consistent);
    reveal(crate::handler_docs::spec_abandon_slot);
}

proof fn lemma_attach_nonsecondary_flight_preserves_all_lanes(
    state: S,
    flight: crate::handler_docs::FlightSpec,
)
    requires
        crate::production_relation::flight_lanes_consistent(
            state.flights,
        ),
        secondary_flight_lanes_consistent(state),
        !state.flights.inflight.contains_key(flight.id),
        state.flights.slots.contains_key(
            crate::target::spec_name(flight.target),
        ),
        state.flights.slots[
            crate::target::spec_name(flight.target)
        ].busy == Some(flight.id),
        !(flight.phase is FireLoadingOrigin),
        !(flight.phase is FireOrigin),
    ensures
        crate::production_relation::flight_lanes_consistent(
            crate::handler_docs::spec_inflight(state, flight).flights,
        ),
        secondary_flight_lanes_consistent(
            crate::handler_docs::spec_inflight(state, flight),
        ),
{
    lemma_attach_owned_flight_preserves_lane_ownership(state, flight);
}

pub proof fn lemma_begin_preserves_lane_ownership(
    state: S,
    flight: crate::handler_docs::FlightSpec,
)
    requires
        crate::global_store_invariants::production_core_control_body(
            state,
        ),
        crate::production_relation::flight_lanes_consistent(
            state.flights,
        ),
        secondary_flight_lanes_consistent(state),
        !state.flights.inflight.contains_key(flight.id),
        state.flights.slots.contains_key(
            crate::target::spec_name(flight.target),
        ),
        state.flights.slots[
            crate::target::spec_name(flight.target)
        ].busy == Some(flight.id),
    ensures
        crate::production_relation::flight_lanes_consistent(
            crate::handler_docs::spec_begin(state, flight).flights,
        ),
        secondary_flight_lanes_consistent(
            crate::handler_docs::spec_begin(state, flight),
        ),
{
    reveal(crate::handler_docs::spec_begin);
    reveal(crate::handler_docs::spec_load_origin);
    reveal(crate::handler_docs::spec_op_exhausted);
    reveal(crate::handler_docs::spec_abandon_slot);
    reveal(crate::state::spec_store);
    reveal(crate::state::spec_store_certified);
    reveal(crate::state::spec_store_raw);
    reveal(crate::state::spec_emit);
    reveal(crate::state::spec_note);
    reveal(crate::handler_timers::spec_timer_op_exhausted);
    reveal(crate::handler_timers::spec_with_timers);
    let lane = crate::target::spec_name(flight.target);
    match flight.work {
        WorkSpec::Fire { schedule, .. } => {
            let issued = crate::state::spec_store(
                state,
                echod_concrete::store::StoreReqSpec::Get {
                    key: crate::keys::spec_sched_key(
                        state.keys.prefix,
                        schedule,
                    ),
                },
                crate::state::Owner::Flight(flight.id),
            );
            match issued.1 {
                Some(op) => {
                    lemma_attach_nonsecondary_flight_preserves_all_lanes(
                        issued.0,
                        crate::handler_docs::FlightSpec {
                            phase:
                                crate::handler_docs::PhaseSpec::
                                    FireLoadingSchedule { op },
                            ..flight
                        },
                    );
                },
                None => {},
            }
        },
        _ => match flight.target {
            TargetSpec::Origin(origin) => {
                let loaded = crate::handler_docs::spec_load_origin(
                    state,
                    flight.id,
                    origin,
                );
                match loaded.1 {
                    Some(op) => {
                        lemma_attach_nonsecondary_flight_preserves_all_lanes(
                            loaded.0,
                            crate::handler_docs::FlightSpec {
                                phase:
                                    crate::handler_docs::PhaseSpec::
                                        Loading {
                                            op,
                                            revalidating: loaded.2,
                                        },
                                ..flight
                            },
                        );
                    },
                    None => {},
                }
            },
            TargetSpec::Schedule(id) => {
                let issued = crate::state::spec_store(
                    state,
                    echod_concrete::store::StoreReqSpec::Get {
                        key: crate::keys::spec_sched_key(
                            state.keys.prefix,
                            id,
                        ),
                    },
                    crate::state::Owner::Flight(flight.id),
                );
                match issued.1 {
                    Some(op) => {
                        lemma_attach_nonsecondary_flight_preserves_all_lanes(
                            issued.0,
                            crate::handler_docs::FlightSpec {
                                phase:
                                    crate::handler_docs::PhaseSpec::
                                        Loading {
                                            op,
                                            revalidating: None,
                                        },
                                ..flight
                            },
                        );
                    },
                    None => {},
                }
            },
        },
    }
    let next = crate::handler_docs::spec_begin(state, flight);
    assert(crate::production_relation::flight_lanes_consistent(
        next.flights,
    )) by {
        reveal(crate::production_relation::flight_lanes_consistent);
    };
    assert(secondary_flight_lanes_consistent(next)) by {
        reveal(secondary_flight_lanes_consistent);
    };
}

/// Starting a flight is only legal on a free target lane. The start either
/// exhausts before attaching a flight, or installs the allocated flight after
/// marking that exact target slot busy with its id.
pub proof fn lemma_start_on_free_lane_preserves_lane_ownership(
    state: S,
    target: TargetSpec,
    work: WorkSpec,
    firing: Option<FiringSpec>,
    debug: bool,
)
    requires
        crate::global_store_invariants::production_core_control_body(
            state,
        ),
        crate::production_relation::flight_lanes_consistent(
            state.flights,
        ),
        secondary_flight_lanes_consistent(state),
        crate::handler_docs::spec_slot_of(
            state,
            crate::target::spec_name(target),
        ).busy is None,
    ensures
        crate::production_relation::flight_lanes_consistent(
            crate::handler_docs::spec_start(
                state,
                target,
                work,
                firing,
                debug,
            ).flights,
        ),
        secondary_flight_lanes_consistent(
            crate::handler_docs::spec_start(
                state,
                target,
                work,
                firing,
                debug,
            ),
        ),
{
    reveal(
        crate::global_store_invariants::production_core_control_body,
    );
    reveal(crate::handler_docs::spec_start);
    reveal(crate::handler_docs::spec_with_slot);
    reveal(crate::state::spec_flight);
    reveal(secondary_flight_lanes_consistent);
    let name = crate::target::spec_name(target);
    let slot = crate::handler_docs::spec_slot_of(state, name);
    let allocated = crate::state::spec_flight(state);
    let flight = crate::handler_docs::FlightSpec {
        id: state.next_flight,
        target,
        work,
        attempt: 0,
        phase: crate::handler_docs::PhaseSpec::Idle,
        firing,
        debug,
        idle: false,
    };
    match allocated.1 {
        None => {
            assert(crate::production_relation::flight_lanes_consistent(
                allocated.0.flights,
            ));
            assert forall|fid: u64|
                allocated.0.flights.inflight.contains_key(fid) implies
                    crate::target::spec_name(
                        allocated.0.flights.inflight[fid].target,
                    ) != name by {
                let active = allocated.0.flights.inflight[fid];
                if crate::target::spec_name(active.target) == name {
                    assert(state.flights.slots.contains_key(name));
                    assert(state.flights.slots[name].busy == Some(fid));
                    assert(false);
                }
            };
            lemma_abandon_unowned_lane_preserves_lane_ownership(
                allocated.0,
                name,
            );
            reveal(crate::handler_docs::spec_op_exhausted);
            reveal(crate::state::spec_emit);
            reveal(crate::state::spec_note);
            reveal(
                crate::handler_timers::spec_timer_op_exhausted,
            );
            reveal(crate::handler_timers::spec_with_timers);
            assert(secondary_flight_lanes_consistent(
                crate::handler_docs::spec_op_exhausted(
                    allocated.0,
                    flight,
                ),
            )) by {
                assert forall|fid: u64|
                    crate::handler_docs::spec_op_exhausted(
                        allocated.0,
                        flight,
                    ).flights.inflight.contains_key(fid)
                    implies {
                        match #[trigger]
                            crate::handler_docs::spec_op_exhausted(
                                allocated.0,
                                flight,
                            ).flights.inflight[fid].phase
                        {
                            crate::handler_docs::PhaseSpec::
                                FireLoadingOrigin { ctx, .. }
                            | crate::handler_docs::PhaseSpec::
                                FireOrigin { ctx, .. } => {
                                let secondary =
                                    crate::target::spec_name(
                                        crate::target::TargetSpec::
                                            Origin(ctx.origin),
                                    );
                                &&& crate::handler_docs::
                                    spec_op_exhausted(
                                        allocated.0,
                                        flight,
                                    ).flights.slots
                                        .contains_key(secondary)
                                &&& crate::handler_docs::
                                    spec_op_exhausted(
                                        allocated.0,
                                        flight,
                                    ).flights.slots[secondary].busy
                                        == Some(fid)
                            },
                            _ => true,
                        }
                    } by {};
            };
        },
        Some(_) => {
            let claimed = crate::handler_docs::spec_with_slot(
                allocated.0,
                name,
                crate::handler_docs::SlotSpec {
                    busy: Some(flight.id),
                    ..slot
                },
            );
            lemma_claim_free_lane_preserves_existing_ownership(
                allocated.0,
                name,
                flight.id,
                slot.queue,
            );
            assert(crate::global_store_control::detached_flight_control(
                claimed,
                flight.id,
            )) by {
                reveal(
                    crate::global_store_control::detached_flight_control,
                );
                reveal(
                    crate::global_store_invariants::
                        production_core_control_body,
                );
            };
            crate::global_store_control::
                lemma_begin_preserves_core_control_body(
                    claimed,
                    flight,
                );
            lemma_begin_preserves_lane_ownership(claimed, flight);
        },
    }
    let next = crate::handler_docs::spec_start(
        state,
        target,
        work,
        firing,
        debug,
    );
    assert(crate::production_relation::flight_lanes_consistent(
        next.flights,
    ));
    assert(secondary_flight_lanes_consistent(next));
}

pub proof fn lemma_submit_preserves_lane_ownership(
    state: S,
    target: TargetSpec,
    work: WorkSpec,
    firing: Option<FiringSpec>,
    debug: bool,
)
    requires
        crate::global_store_invariants::production_core_control_body(
            state,
        ),
        crate::production_relation::flight_lanes_consistent(
            state.flights,
        ),
        secondary_flight_lanes_consistent(state),
    ensures
        crate::production_relation::flight_lanes_consistent(
            crate::handler_docs::spec_submit(
                state,
                target,
                work,
                firing,
                debug,
            ).flights,
        ),
        secondary_flight_lanes_consistent(
            crate::handler_docs::spec_submit(
                state,
                target,
                work,
                firing,
                debug,
            ),
        ),
{
    reveal(crate::handler_docs::spec_submit);
    reveal(crate::state::spec_note);
    reveal(secondary_flight_lanes_consistent);
    let name = crate::target::spec_name(target);
    let noted = match work {
        WorkSpec::Sweep { now, .. } =>
            crate::state::spec_note(
                state,
                crate::types::NoteSpec::SweepBegin {
                    flight: state.next_flight,
                    target: name,
                    now,
                },
            ),
        _ => state,
    };
    let slot = crate::handler_docs::spec_slot_of(noted, name);
    if slot.busy is Some {
        reveal(crate::handler_docs::spec_with_slot);
        reveal(
            crate::production_relation::flight_lanes_consistent,
        );
    } else {
        let slotted =
            crate::handler_docs::spec_with_slot(noted, name, slot);
        assert(crate::global_store_invariants::
            production_core_control_body(slotted)) by {
            reveal(crate::handler_docs::spec_with_slot);
            reveal(
                crate::global_store_invariants::
                    production_core_control_body,
            );
        };
        assert(crate::production_relation::flight_lanes_consistent(
            slotted.flights,
        )) by {
            reveal(crate::handler_docs::spec_with_slot);
        };
        assert(secondary_flight_lanes_consistent(slotted)) by {
            reveal(crate::handler_docs::spec_with_slot);
        };
        lemma_start_on_free_lane_preserves_lane_ownership(
            slotted,
            target,
            work,
            firing,
            debug,
        );
    }
}

/// Releasing a lane is safe only after its active owner has detached.  A
/// queued work item starts on that same lane; a waiter keeps its original
/// primary lane while acquiring this secondary lane.
pub proof fn lemma_release_of_unowned_lane_preserves_lane_ownership(
    state: S,
    name: Seq<char>,
)
    requires
        crate::global_store_invariants::production_core_control_body(
            state,
        ),
        crate::production_relation::flight_lanes_consistent(
            state.flights,
        ),
        secondary_flight_lanes_consistent(state),
        crate::global_store_invariants::queued_work_lanes_consistent(
            state,
        ),
        lane_has_no_active_flight(state.flights, name),
        lane_has_no_secondary_flight_owner(state.flights, name),
    ensures
        crate::production_relation::flight_lanes_consistent(
            crate::handler_docs::spec_release(state, name).flights,
        ),
        secondary_flight_lanes_consistent(
            crate::handler_docs::spec_release(state, name),
        ),
{
    reveal(crate::handler_docs::spec_release);
    reveal(crate::handler_docs::spec_resume);
    reveal(crate::handler_sched::spec_fire_load_origin);
    reveal(crate::handler_docs::spec_load_origin);
    reveal(crate::handler_docs::spec_op_exhausted);
    reveal(crate::handler_docs::spec_abandon_slot);
    reveal(crate::handler_docs::spec_inflight);
    reveal(crate::handler_docs::spec_take_flight);
    reveal(crate::handler_docs::spec_with_slot);
    reveal(crate::handler_docs::spec_without_slot);
    reveal(crate::state::spec_store);
    reveal(crate::state::spec_store_certified);
    reveal(crate::state::spec_store_raw);
    reveal(crate::state::spec_emit);
    reveal(crate::state::spec_note);
    reveal(crate::handler_timers::spec_timer_op_exhausted);
    reveal(crate::handler_timers::spec_with_timers);
    reveal(
        crate::global_store_invariants::queued_work_lanes_consistent,
    );
    reveal(secondary_flight_lanes_consistent);
    reveal(lane_has_no_secondary_flight_owner);
    if state.flights.slots.contains_key(name) {
        let slot = state.flights.slots[name];
        if slot.queue.len() == 0 {
            lemma_abandon_unowned_lane_preserves_lane_ownership(
                state,
                name,
            );
        } else {
            let rest = slot.queue.drop_first();
            match slot.queue[0] {
                crate::handler_docs::QueuedSpec::Work {
                    target,
                    work,
                    firing,
                    debug,
                } => {
                    assert(crate::target::spec_name(target) == name);
                    let slotted =
                        crate::handler_docs::spec_with_slot(
                            state,
                            name,
                            crate::handler_docs::SlotSpec {
                                busy: None,
                                queue: rest,
                            },
                        );
                    assert(crate::global_store_invariants::
                        production_core_control_body(slotted)) by {
                        reveal(
                            crate::global_store_invariants::
                                production_core_control_body,
                        );
                    };
                    assert(crate::production_relation::
                        flight_lanes_consistent(slotted.flights)) by {
                        reveal(
                            crate::production_relation::
                                flight_lanes_consistent,
                        );
                        reveal(lane_has_no_active_flight);
                    };
                    lemma_start_on_free_lane_preserves_lane_ownership(
                        slotted,
                        target,
                        work,
                        firing,
                        debug,
                    );
                },
                crate::handler_docs::QueuedSpec::Waiter(waiter) => {
                    assert(state.flights.inflight.contains_key(waiter));
                    let queued_flight =
                        state.flights.inflight[waiter];
                    assert(name != crate::target::spec_name(
                        queued_flight.target,
                    ));
                    match queued_flight.phase {
                        crate::handler_docs::PhaseSpec::
                            FireWaitingOrigin(ctx) => {
                            assert(name == crate::target::spec_name(
                                crate::target::TargetSpec::Origin(
                                    ctx.origin,
                                ),
                            ));
                        },
                        _ => assert(false),
                    }
                    let slotted =
                        crate::handler_docs::spec_with_slot(
                            state,
                            name,
                            crate::handler_docs::SlotSpec {
                                busy: Some(waiter),
                                queue: rest,
                            },
                        );
                    assert(crate::production_relation::
                        flight_lanes_consistent(slotted.flights)) by {
                        reveal(
                            crate::production_relation::
                                flight_lanes_consistent,
                        );
                    };
                    if slotted.flights.inflight.contains_key(waiter) {
                        let flight =
                            slotted.flights.inflight[waiter];
                        match flight.phase {
                            crate::handler_docs::PhaseSpec::
                                FireWaitingOrigin(ctx) => {
                                let detached =
                                    crate::handler_docs::
                                        spec_take_flight(
                                            slotted,
                                            waiter,
                                        );
                                let resumed =
                                    crate::handler_docs::FlightSpec {
                                        phase:
                                            crate::handler_docs::
                                                PhaseSpec::Idle,
                                        ..flight
                                    };
                                match crate::handler_docs::
                                    spec_load_origin(
                                        detached,
                                        waiter,
                                        ctx.origin,
                                    ).1 {
                                    Some(_) => {
                                        crate::production_relation::
                                            lemma_inflight_replacement_preserves_lane_owner(
                                                slotted,
                                                waiter,
                                                crate::handler_docs::
                                                    FlightSpec {
                                                        phase:
                                                            crate::handler_docs::
                                                                PhaseSpec::
                                                                    FireLoadingOrigin {
                                                                        op:
                                                                            crate::handler_docs::
                                                                                spec_load_origin(
                                                                                    detached,
                                                                                    waiter,
                                                                                    ctx.origin,
                                                                                ).1.unwrap(),
                                                                        revalidating:
                                                                            crate::handler_docs::
                                                                                spec_load_origin(
                                                                                    detached,
                                                                                    waiter,
                                                                                    ctx.origin,
                                                                                ).2,
                                                                        ctx,
                                                                    },
                                                        ..resumed
                                                    },
                                            );
                                    },
                                    None => {},
                                }
                            },
                            _ => {},
                        }
                    }
                    assert(crate::production_relation::
                        flight_lanes_consistent(
                            crate::handler_docs::spec_release(
                                state,
                                name,
                            ).flights,
                        )) by {
                        reveal(
                            crate::production_relation::
                                flight_lanes_consistent,
                        );
                        assert forall|fid: u64|
                            crate::handler_docs::spec_release(
                                state,
                                name,
                            ).flights.inflight.contains_key(fid)
                            implies {
                                let active = #[trigger]
                                    crate::handler_docs::spec_release(
                                        state,
                                        name,
                                    ).flights.inflight[fid];
                                let active_name =
                                    crate::target::spec_name(
                                        active.target,
                                    );
                                &&& crate::handler_docs::spec_release(
                                    state,
                                    name,
                                ).flights.slots.contains_key(
                                    active_name,
                                )
                                &&& crate::handler_docs::spec_release(
                                    state,
                                    name,
                                ).flights.slots[active_name].busy
                                    == Some(fid)
                            } by {
                            if state.flights.inflight.contains_key(fid) {
                                assert(crate::target::spec_name(
                                    state.flights.inflight[fid].target,
                                ) != name) by {
                                    reveal(lane_has_no_active_flight);
                                };
                                if slotted.flights.inflight
                                    .contains_key(waiter)
                                    && fid != waiter
                                    && crate::target::spec_name(
                                        state.flights.inflight[fid]
                                            .target,
                                    ) == crate::target::spec_name(
                                        slotted.flights.inflight[waiter]
                                            .target,
                                    )
                                {
                                    let shared =
                                        crate::target::spec_name(
                                            state.flights.inflight[fid]
                                                .target,
                                        );
                                    assert(state.flights.slots[shared]
                                        .busy == Some(fid));
                                    assert(state.flights.slots[shared]
                                        .busy == Some(waiter));
                                    assert(false);
                                }
                            } else {
                                assert(fid == waiter);
                            }
                        };
                    };
                },
            }
        }
    }
    assert(secondary_flight_lanes_consistent(
        crate::handler_docs::spec_release(state, name),
    ));
}

/// Releasing a distinct secondary lane cannot clear the primary slot of a
/// detached flight.  A resumed waiter may exhaust while loading, but its
/// primary lane is different by the pre-release lane ownership invariant.
pub proof fn lemma_release_other_lane_preserves_detached_primary(
    state: S,
    name: Seq<char>,
    flight: crate::handler_docs::FlightSpec,
)
    requires
        crate::global_store_invariants::production_core_control_body(
            state,
        ),
        crate::production_relation::flight_lanes_consistent(
            state.flights,
        ),
        secondary_flight_lanes_consistent(state),
        crate::global_store_invariants::queued_work_lanes_consistent(
            state,
        ),
        lane_has_no_active_flight(state.flights, name),
        lane_has_no_secondary_flight_owner(state.flights, name),
        detached_flight_owns_primary(state, flight),
        state.flights_exhausted || flight.id < state.next_flight,
        name != crate::target::spec_name(flight.target),
    ensures
        detached_flight_owns_primary(
            crate::handler_docs::spec_release(state, name),
            flight,
        ),
{
    lemma_release_of_unowned_lane_preserves_lane_ownership(state, name);
    reveal(crate::handler_docs::spec_release);
    reveal(crate::handler_docs::spec_start);
    reveal(crate::handler_docs::spec_resume);
    reveal(crate::handler_docs::spec_begin);
    reveal(crate::handler_sched::spec_fire_load_origin);
    reveal(crate::handler_docs::spec_load_origin);
    reveal(crate::handler_docs::spec_op_exhausted);
    reveal(crate::handler_docs::spec_abandon_slot);
    reveal(crate::handler_docs::spec_inflight);
    reveal(crate::handler_docs::spec_take_flight);
    reveal(crate::handler_docs::spec_with_slot);
    reveal(crate::handler_docs::spec_without_slot);
    reveal(crate::handler_docs::spec_slot_of);
    reveal(crate::state::spec_flight);
    reveal(crate::state::spec_store);
    reveal(crate::state::spec_store_certified);
    reveal(crate::state::spec_store_raw);
    reveal(crate::state::spec_emit);
    reveal(crate::state::spec_note);
    reveal(crate::handler_timers::spec_timer_op_exhausted);
    reveal(crate::handler_timers::spec_with_timers);
    reveal(
        crate::global_store_invariants::queued_work_lanes_consistent,
    );
    reveal(crate::production_relation::flight_lanes_consistent);
    reveal(detached_flight_owns_primary);
    if state.flights.slots.contains_key(name) {
        let slot = state.flights.slots[name];
        if slot.queue.len() > 0 {
            match slot.queue[0] {
                crate::handler_docs::QueuedSpec::Work {
                    target,
                    ..
                } => {
                    assert(crate::target::spec_name(target) == name);
                },
                crate::handler_docs::QueuedSpec::Waiter(waiter) => {
                    assert(state.flights.inflight.contains_key(waiter));
                    assert(waiter != flight.id);
                    let waiter_primary = crate::target::spec_name(
                        state.flights.inflight[waiter].target,
                    );
                    assert(waiter_primary
                        != crate::target::spec_name(flight.target)) by {
                        if waiter_primary
                            == crate::target::spec_name(flight.target)
                        {
                            assert(state.flights.slots[waiter_primary]
                                .busy == Some(waiter));
                            assert(state.flights.slots[waiter_primary]
                                .busy == Some(flight.id));
                            assert(false);
                        }
                    };
                },
            }
        }
    }
}

/// A schedule fire keeps its primary schedule lane while claiming the
/// workflow lane used by its first commit.
pub proof fn lemma_fire_claim_preserves_lane_ownership(
    state: S,
    flight: crate::handler_docs::FlightSpec,
    context: crate::handler_docs::FireCtxSpec,
)
    requires
        crate::global_store_invariants::production_core_control_body(
            state,
        ),
        crate::production_relation::flight_lanes_consistent(
            state.flights,
        ),
        secondary_flight_lanes_consistent(state),
        !state.flights.inflight.contains_key(flight.id),
        state.flights.slots.contains_key(
            crate::target::spec_name(flight.target),
        ),
        state.flights.slots[
            crate::target::spec_name(flight.target)
        ].busy == Some(flight.id),
        crate::target::spec_name(flight.target)
            != crate::target::spec_name(
                crate::target::TargetSpec::Origin(context.origin),
            ),
    ensures
        crate::production_relation::flight_lanes_consistent(
            crate::handler_sched::spec_fire_claim(
                state,
                flight,
                context,
            ).flights,
        ),
        secondary_flight_lanes_consistent(
            crate::handler_sched::spec_fire_claim(
                state,
                flight,
                context,
            ),
        ),
{
    reveal(crate::handler_sched::spec_fire_claim);
    reveal(crate::handler_sched::spec_fire_load_origin);
    reveal(crate::handler_docs::spec_load_origin);
    reveal(crate::handler_docs::spec_op_exhausted);
    reveal(crate::handler_docs::spec_abandon_slot);
    reveal(crate::handler_docs::spec_inflight);
    reveal(crate::handler_docs::spec_with_slot);
    reveal(crate::handler_docs::spec_slot_of);
    reveal(crate::state::spec_store);
    reveal(crate::state::spec_store_certified);
    reveal(crate::state::spec_store_raw);
    reveal(crate::state::spec_emit);
    reveal(crate::state::spec_note);
    reveal(crate::handler_timers::spec_timer_op_exhausted);
    reveal(crate::handler_timers::spec_with_timers);
    reveal(secondary_flight_lanes_consistent);
    let origin_lane = crate::target::spec_name(
        crate::target::TargetSpec::Origin(context.origin),
    );
    let slot =
        crate::handler_docs::spec_slot_of(state, origin_lane);
    if slot.busy is Some {
        let slotted = crate::handler_docs::spec_with_slot(
            state,
            origin_lane,
            crate::handler_docs::SlotSpec {
                queue: slot.queue.push(
                    crate::handler_docs::QueuedSpec::Waiter(
                        flight.id,
                    ),
                ),
                ..slot
            },
        );
        assert(crate::production_relation::flight_lanes_consistent(
            slotted.flights,
        )) by {
            reveal(
                crate::production_relation::flight_lanes_consistent,
            );
        };
        assert(secondary_flight_lanes_consistent(slotted)) by {
            assert forall|fid: u64|
                slotted.flights.inflight.contains_key(fid) implies {
                    match #[trigger] slotted.flights.inflight[fid].phase {
                        crate::handler_docs::PhaseSpec::
                            FireLoadingOrigin { ctx, .. }
                        | crate::handler_docs::PhaseSpec::FireOrigin {
                            ctx,
                            ..
                        } => {
                            let secondary = crate::target::spec_name(
                                crate::target::TargetSpec::Origin(
                                    ctx.origin,
                                ),
                            );
                            &&& slotted.flights.slots
                                .contains_key(secondary)
                            &&& slotted.flights.slots[secondary].busy
                                == Some(fid)
                        },
                        _ => true,
                    }
                } by {
                assert(state.flights.inflight.contains_key(fid));
                assert({
                    match #[trigger] state.flights.inflight[fid].phase {
                        crate::handler_docs::PhaseSpec::
                            FireLoadingOrigin { ctx, .. }
                        | crate::handler_docs::PhaseSpec::FireOrigin {
                            ctx,
                            ..
                        } => {
                            let secondary = crate::target::spec_name(
                                crate::target::TargetSpec::Origin(
                                    ctx.origin,
                                ),
                            );
                            &&& state.flights.slots
                                .contains_key(secondary)
                            &&& state.flights.slots[secondary].busy
                                == Some(fid)
                        },
                        _ => true,
                    }
                });
                let active = state.flights.inflight[fid];
                match active.phase {
                    crate::handler_docs::PhaseSpec::
                        FireLoadingOrigin { ctx, .. }
                    | crate::handler_docs::PhaseSpec::FireOrigin {
                        ctx,
                        ..
                    } => {
                        let secondary = crate::target::spec_name(
                            crate::target::TargetSpec::Origin(
                                ctx.origin,
                            ),
                        );
                        if secondary == origin_lane {
                            assert(state.flights.slots
                                .contains_key(secondary));
                            assert(state.flights.slots[secondary].busy
                                == Some(fid));
                            assert(slotted.flights.slots[secondary]
                                .busy == slot.busy);
                        } else {
                            assert(state.flights.slots
                                .contains_key(secondary));
                            assert(slotted.flights.slots[secondary]
                                == state.flights.slots[secondary]);
                        }
                    },
                    _ => {},
                }
            };
        };
        lemma_attach_owned_flight_preserves_lane_ownership(
            slotted,
            crate::handler_docs::FlightSpec {
                phase:
                    crate::handler_docs::PhaseSpec::FireWaitingOrigin(
                        context,
                    ),
                ..flight
            },
        );
    } else {
        let slotted = crate::handler_docs::spec_with_slot(
            state,
            origin_lane,
            crate::handler_docs::SlotSpec {
                busy: Some(flight.id),
                ..slot
            },
        );
        assert(crate::production_relation::flight_lanes_consistent(
            slotted.flights,
        )) by {
            reveal(
                crate::production_relation::flight_lanes_consistent,
            );
        };
        assert(secondary_flight_lanes_consistent(slotted)) by {
            assert forall|fid: u64|
                slotted.flights.inflight.contains_key(fid) implies {
                    match #[trigger] slotted.flights.inflight[fid].phase {
                        crate::handler_docs::PhaseSpec::
                            FireLoadingOrigin { ctx, .. }
                        | crate::handler_docs::PhaseSpec::FireOrigin {
                            ctx,
                            ..
                        } => {
                            let secondary = crate::target::spec_name(
                                crate::target::TargetSpec::Origin(
                                    ctx.origin,
                                ),
                            );
                            &&& slotted.flights.slots
                                .contains_key(secondary)
                            &&& slotted.flights.slots[secondary].busy
                                == Some(fid)
                        },
                        _ => true,
                    }
                } by {
                    assert(state.flights.inflight.contains_key(fid));
                    assert({
                        match #[trigger]
                            state.flights.inflight[fid].phase
                        {
                            crate::handler_docs::PhaseSpec::
                                FireLoadingOrigin { ctx, .. }
                            | crate::handler_docs::PhaseSpec::
                                FireOrigin { ctx, .. } => {
                                let secondary =
                                    crate::target::spec_name(
                                        crate::target::TargetSpec::
                                            Origin(ctx.origin),
                                    );
                                &&& state.flights.slots
                                    .contains_key(secondary)
                                &&& state.flights.slots[secondary].busy
                                    == Some(fid)
                            },
                            _ => true,
                        }
                    });
                    let active = slotted.flights.inflight[fid];
                    match active.phase {
                        crate::handler_docs::PhaseSpec::
                            FireLoadingOrigin { ctx, .. }
                        | crate::handler_docs::PhaseSpec::FireOrigin {
                            ctx,
                            ..
                        } => {
                            let secondary = crate::target::spec_name(
                                crate::target::TargetSpec::Origin(
                                    ctx.origin,
                                ),
                            );
                            if secondary == origin_lane {
                                assert(state.flights.slots
                                    .contains_key(origin_lane));
                                assert(state.flights.slots[origin_lane]
                                    .busy == Some(fid));
                                assert(slot
                                    == state.flights.slots[origin_lane]);
                                assert(slot.busy is Some);
                                assert(false);
                            } else {
                                assert(state.flights.slots
                                    .contains_key(secondary));
                                assert(slotted.flights.slots[secondary]
                                    == state.flights.slots[secondary]);
                            }
                        },
                        _ => {},
                    }
                };
        };
        match crate::handler_docs::spec_load_origin(
            slotted,
            flight.id,
            context.origin,
        ).1 {
            Some(_) => {
                let loaded = crate::handler_docs::spec_load_origin(
                    slotted,
                    flight.id,
                    context.origin,
                );
                assert(crate::production_relation::
                    flight_lanes_consistent(loaded.0.flights));
                assert(secondary_flight_lanes_consistent(loaded.0));
                lemma_attach_owned_flight_preserves_lane_ownership(
                    loaded.0,
                    crate::handler_docs::FlightSpec {
                        phase:
                            crate::handler_docs::PhaseSpec::
                                FireLoadingOrigin {
                                    op: loaded.1.unwrap(),
                                    revalidating: loaded.2,
                                    ctx: context,
                                },
                        ..flight
                    },
                );
            },
            None => {
                assert forall|fid: u64|
                    crate::handler_sched::spec_fire_claim(
                        state,
                        flight,
                        context,
                    ).flights.inflight.contains_key(fid)
                    implies {
                        let active = #[trigger]
                            crate::handler_sched::spec_fire_claim(
                                state,
                                flight,
                                context,
                            ).flights.inflight[fid];
                        let name =
                            crate::target::spec_name(active.target);
                        &&& crate::handler_sched::spec_fire_claim(
                            state,
                            flight,
                            context,
                        ).flights.slots.contains_key(name)
                        &&& crate::handler_sched::spec_fire_claim(
                            state,
                            flight,
                            context,
                        ).flights.slots[name].busy == Some(fid)
                    } by {
                    assert(state.flights.inflight.contains_key(fid));
                    assert(fid != flight.id);
                    let active_name = crate::target::spec_name(
                        state.flights.inflight[fid].target,
                    );
                    assert(active_name != origin_lane) by {
                        if active_name == origin_lane {
                            assert(state.flights.slots[origin_lane]
                                .busy == Some(fid));
                            assert(slot.busy is Some);
                            assert(false);
                        }
                    };
                    assert(active_name
                        != crate::target::spec_name(flight.target)) by {
                        if active_name
                            == crate::target::spec_name(flight.target)
                        {
                            assert(state.flights.slots[active_name]
                                .busy == Some(fid));
                            assert(state.flights.slots[active_name]
                                .busy == Some(flight.id));
                            assert(false);
                        }
                    };
                };
            },
        }
    }
    assert(secondary_flight_lanes_consistent(
        crate::handler_sched::spec_fire_claim(
            state,
            flight,
            context,
        ),
    ));
}

} // verus!
