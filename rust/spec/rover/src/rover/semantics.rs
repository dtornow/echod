//! Rover's mathematical semantics.
//!
//! This module is specification-only. [`super::replay`] is executable code
//! verified against it.

use vstd::prelude::*;

use crate::Time;

use super::{BoundaryEvent, Envelope, ProcessEvent, RoverModel};

verus! {

/// [`super::StepResult`] as specifications see it.
pub struct StepResultV<S, P, M> {
    pub state: S,
    pub send: Seq<(P, M)>,
}

/// The complete world: process-local states, append-only network, and time.
pub struct WorldV<P, S, M> {
    pub process: Seq<(P, S)>,
    pub network: Seq<Envelope<P, M>>,
    pub now: Time,
}

pub type World<M> = WorldV<
    <M as RoverModel>::Pid,
    <M as RoverModel>::StateV,
    <M as RoverModel>::Message,
>;

/// Labels retain exactly what happened in one world step.
pub enum Label<P, M> {
    Input {
        recipient: P,
        at: Time,
        message: M,
    },
    Process {
        process: P,
        at: Time,
        event: ProcessEvent<P, M>,
        send: Seq<(P, M)>,
    },
    Outside {
        sender: P,
        at: Time,
        message: M,
    },
}

pub type Lab<M> = Label<<M as RoverModel>::Pid, <M as RoverModel>::Message>;
pub type Ev<M> = BoundaryEvent<<M as RoverModel>::Pid, <M as RoverModel>::Message>;

/// Executable process slots as the mathematical world sees their state views.
pub open spec fn process_view<M: RoverModel>(
    process: Seq<(M::Pid, M::State)>,
) -> Seq<(M::Pid, M::StateV)> {
    process.map_values(|entry: (M::Pid, M::State)| (entry.0, entry.1@))
}

/// Process `pid` exists and is not the distinguished outside endpoint.
pub open spec fn is_process<M: RoverModel>(m: M, world: World<M>, pid: M::Pid) -> bool {
    pid != m.spec_outside() && exists|i: int|
        0 <= i < world.process.len() && #[trigger] world.process[i].0 == pid
}

/// A receive is valid whenever its message occurs in the append-only network.
pub open spec fn event_valid<P, S, M>(
    world: WorldV<P, S, M>,
    recipient: P,
    event: ProcessEvent<P, M>,
) -> bool {
    match event {
        ProcessEvent::Receive { sender, message } => exists|i: int|
            0 <= i < world.network.len()
                && #[trigger] world.network[i] == Envelope { sender, recipient, message },
        ProcessEvent::Timeout => true,
    }
}

/// Turn a process's sends into append-only network envelopes.
pub open spec fn envelopes<P, M>(sender: P, send: Seq<(P, M)>) -> Seq<Envelope<P, M>> {
    send.map_values(|entry: (P, M)| Envelope {
        sender,
        recipient: entry.0,
        message: entry.1,
    })
}

pub open spec fn inject<P, S, M>(
    world: WorldV<P, S, M>,
    outside: P,
    recipient: P,
    at: Time,
    message: M,
) -> WorldV<P, S, M> {
    WorldV {
        network: world.network.push(Envelope { sender: outside, recipient, message }),
        now: at,
        ..world
    }
}

pub open spec fn land<P, S, M>(
    world: WorldV<P, S, M>,
    slot: int,
    process: P,
    at: Time,
    result: StepResultV<S, P, M>,
) -> WorldV<P, S, M> {
    WorldV {
        process: world.process.update(slot, (process, result.state)),
        network: world.network + envelopes(process, result.send),
        now: at,
    }
}

pub open spec fn observe_outside<P, S, M>(
    world: WorldV<P, S, M>,
    at: Time,
) -> WorldV<P, S, M> {
    WorldV { now: at, ..world }
}

/// One atomic Rover transition.
pub open spec fn step<M: RoverModel>(
    m: M,
    config: M::Config,
    world: World<M>,
    label: Lab<M>,
    next: World<M>,
) -> bool {
    match label {
        Label::Input { recipient, at, message } => {
            world.now <= at
                && is_process(m, world, recipient)
                && m.spec_injectable(config, message)
                && next == inject(world, m.spec_outside(), recipient, at, message)
        }
        Label::Process { process, at, event, send } => {
            world.now <= at
                && is_process(m, world, process)
                && event_valid(world, process, event)
                && exists|i: int, j: int|
                    #![trigger m.spec_on_event(
                        config,
                        process,
                        world.process[i].1,
                        at,
                        event,
                    )[j]]
                {
                    &&& 0 <= i < world.process.len()
                    &&& world.process[i].0 == process
                    &&& {
                    let outcomes = m.spec_on_event(config, process, world.process[i].1, at, event);
                    &&& 0 <= j < outcomes.len()
                    &&& outcomes[j].send == send
                    &&& next == land(world, i, process, at, outcomes[j])
                    }
                }
        }
        Label::Outside { sender, at, message } => {
            world.now <= at
                && exists|i: int| {
                    0 <= i < world.network.len()
                        && #[trigger] world.network[i] == Envelope {
                            sender,
                            recipient: m.spec_outside(),
                            message,
                        }
                }
                && next == observe_outside(world, at)
        }
    }
}

/// The observable boundary contribution of a label.
pub open spec fn observe<P, M>(label: Label<P, M>) -> Seq<BoundaryEvent<P, M>> {
    match label {
        Label::Input { recipient, at, message } =>
            seq![BoundaryEvent::Input { recipient, at, message }],
        Label::Process { .. } => Seq::empty(),
        Label::Outside { sender, at, message } =>
            seq![BoundaryEvent::Output { sender, at, message }],
    }
}

pub type Execution<M> = Seq<(Lab<M>, World<M>)>;

pub open spec fn before<M: RoverModel>(
    first: World<M>,
    execution: Execution<M>,
    i: int,
) -> World<M> {
    if i == 0 { first } else { execution[i - 1].1 }
}

/// Every execution entry is a valid step from the preceding world.
pub open spec fn legal<M: RoverModel>(
    m: M,
    config: M::Config,
    first: World<M>,
    execution: Execution<M>,
) -> bool {
    forall|i: int| 0 <= i < execution.len() ==> #[trigger]
        step(m, config, before::<M>(first, execution, i), execution[i].0, execution[i].1)
}

/// Boundary trace shown by an execution.
pub open spec fn trace<M: RoverModel>(execution: Execution<M>) -> Seq<Ev<M>>
    decreases execution.len(),
{
    if execution.len() == 0 {
        Seq::empty()
    } else {
        trace::<M>(execution.drop_last()) + observe(execution.last().0)
    }
}

pub open spec fn initial<M: RoverModel>(m: M, config: M::Config) -> World<M> {
    WorldV {
        process: m.spec_initial(config),
        network: Seq::empty(),
        now: 0,
    }
}

/// A boundary trace is valid when some legal execution shows exactly it.
pub open spec fn valid_trace<M: RoverModel>(
    m: M,
    config: M::Config,
    events: Seq<Ev<M>>,
) -> bool {
    exists|execution: Execution<M>|
        #![trigger legal(m, config, initial(m, config), execution), trace::<M>(execution)]
        legal(m, config, initial(m, config), execution)
            && trace::<M>(execution) == events
}

/// Rover's translation of the catalogue's monotone-outbox property: once a
/// message is emitted into the world network, no later step removes it.
pub open spec fn network_extends<M: RoverModel>(
    before: World<M>,
    after: World<M>,
) -> bool {
    exists|suffix: Seq<Envelope<M::Pid, M::Message>>|
        after.network == before.network + suffix
}

pub proof fn step_preserves_network<M: RoverModel>(
    model: M,
    config: M::Config,
    before: World<M>,
    label: Lab<M>,
    after: World<M>,
)
    requires
        step(model, config, before, label, after),
    ensures
        network_extends::<M>(before, after),
{
    reveal(step);
    reveal(network_extends);
    match label {
        Label::Input {
            recipient,
            at: _,
            message,
        } => {
            let suffix = seq![Envelope {
                sender: model.spec_outside(),
                recipient,
                message,
            }];
            assert(after.network == before.network + suffix);
            assert(exists|suffix: Seq<Envelope<M::Pid, M::Message>>|
                after.network == before.network + suffix);
        }
        Label::Process {
            process,
            at,
            event,
            send: _,
        } => {
            let i = choose|i: int|
                #![trigger before.process[i]]
                exists|j: int|
                #![trigger model.spec_on_event(
                    config,
                    process,
                    before.process[i].1,
                    at,
                    event,
                )[j]]
            {
                &&& 0 <= i < before.process.len()
                &&& before.process[i].0 == process
                &&& {
                    let outcomes = model.spec_on_event(
                        config,
                        process,
                        before.process[i].1,
                        at,
                        event,
                    );
                    &&& 0 <= j < outcomes.len()
                    &&& after == land(before, i, process, at, outcomes[j])
                }
            };
            let j = choose|j: int|
                #![trigger model.spec_on_event(
                    config,
                    process,
                    before.process[i].1,
                    at,
                    event,
                )[j]]
            {
                &&& 0 <= i < before.process.len()
                &&& before.process[i].0 == process
                &&& {
                    let outcomes = model.spec_on_event(
                        config,
                        process,
                        before.process[i].1,
                        at,
                        event,
                    );
                    &&& 0 <= j < outcomes.len()
                    &&& after == land(before, i, process, at, outcomes[j])
                }
            };
            let outcome = model.spec_on_event(
                config,
                process,
                before.process[i].1,
                at,
                event,
            )[j];
            let suffix = envelopes(process, outcome.send);
            assert(after.network == before.network + suffix);
            assert(exists|suffix: Seq<Envelope<M::Pid, M::Message>>|
                after.network == before.network + suffix);
        }
        Label::Outside { .. } => {
            assert(after.network == before.network);
            let suffix = Seq::<Envelope<M::Pid, M::Message>>::empty();
            assert(after.network == before.network + suffix);
            assert(exists|suffix: Seq<Envelope<M::Pid, M::Message>>|
                after.network == before.network + suffix);
        }
    }
}

/// Every model admits the empty trace.
pub proof fn empty_trace_valid<M: RoverModel>(m: M, config: M::Config)
    ensures
        valid_trace(m, config, Seq::<Ev<M>>::empty()),
{
    let execution = Execution::<M>::empty();
    assert(legal(m, config, initial(m, config), execution));
    assert(trace::<M>(execution) =~= Seq::<Ev<M>>::empty());
}

} // verus!
