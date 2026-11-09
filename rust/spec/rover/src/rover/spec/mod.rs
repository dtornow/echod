//! The complete mathematical Rover specification.

use vstd::prelude::*;

use crate::{Data, Time};

use super::comm::{BoundaryEvent, Envelope, ProcessEvent};

pub mod refinement;

verus! {

/// One stateful process in a Rover world.
pub trait RoverProc: Sized {
    type Config;
    type Pid: Data;
    type Message: Data;

    spec fn on_event(
        self,
        config: Self::Config,
        now: Time,
        event: ProcessEvent<Self::Pid, Self::Message>,
    ) -> Seq<StepResultV<Self, Self::Pid, Self::Message>>;
}

/// Model-specific policy supplied to the generic Rover specification.
pub trait RoverModel: Sized {
    type Config;
    type Pid: Data;
    type Proc: RoverProc<Config = Self::Config, Pid = Self::Pid, Message = Self::Message>;
    type Message: Data;
    type Boundary;

    open spec fn outside(&self) -> Self::Pid {
        arbitrary()
    }

    open spec fn processes(&self, config: Self::Config) -> Seq<(Self::Pid, Self::Proc)> {
        arbitrary()
    }

    open spec fn injectable(&self, config: Self::Config, message: Self::Message) -> bool {
        arbitrary()
    }

    open spec fn observe(&self, label: LabelOf<Self>) -> Seq<Self::Boundary> {
        arbitrary()
    }
}

/// One possible local-process result.
pub struct StepResultV<S, P, M> {
    pub state: S,
    pub send: Seq<(P, M)>,
}

/// An ordered finite process map. Executable initialization proves pids are
/// unique; the order is retained so search can enumerate processes and
/// certificates can name a stable slot.
pub type ProcMap<P, S> = Seq<(P, S)>;

/// The complete Rover world.
pub struct RoverSpec<M: RoverModel> {
    pub process: ProcMap<M::Pid, M::Proc>,
    pub network: Seq<Envelope<M::Pid, M::Message>>,
    pub now: Time,
}

pub type World<M> = RoverSpec<M>;

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

pub type LabelOf<M> = Label<<M as RoverModel>::Pid, <M as RoverModel>::Message>;
pub type EventOf<M> = BoundaryEvent<<M as RoverModel>::Pid, <M as RoverModel>::Message>;
pub type Lab<M> = LabelOf<M>;
pub type Ev<M> = EventOf<M>;

/// Process `pid` exists and is not the distinguished outside endpoint.
pub open spec fn is_process<M: RoverModel>(m: M, world: World<M>, pid: M::Pid) -> bool {
    pid != m.outside() && exists|i: int|
        0 <= i < world.process.len() && #[trigger] world.process[i].0 == pid
}

/// A receive is valid whenever its message occurs in the append-only network.
pub open spec fn event_valid<M: RoverModel>(
    world: World<M>,
    recipient: M::Pid,
    event: ProcessEvent<M::Pid, M::Message>,
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

pub open spec fn inject<M: RoverModel>(
    world: World<M>,
    outside: M::Pid,
    recipient: M::Pid,
    at: Time,
    message: M::Message,
) -> World<M> {
    RoverSpec {
        network: world.network.push(Envelope { sender: outside, recipient, message }),
        now: at,
        ..world
    }
}

pub open spec fn land<M: RoverModel>(
    world: World<M>,
    slot: int,
    process: M::Pid,
    at: Time,
    result: StepResultV<M::Proc, M::Pid, M::Message>,
) -> World<M> {
    RoverSpec {
        process: world.process.update(slot, (process, result.state)),
        network: world.network + envelopes(process, result.send),
        now: at,
    }
}

pub open spec fn observe_outside<M: RoverModel>(
    world: World<M>,
    at: Time,
) -> World<M> {
    RoverSpec { now: at, ..world }
}

/// The process-delivery arm of [`step`].
pub open spec fn process_transition<M: RoverModel>(
    model: M,
    config: M::Config,
    world: World<M>,
    process: M::Pid,
    at: Time,
    event: ProcessEvent<M::Pid, M::Message>,
    send: Seq<(M::Pid, M::Message)>,
    next: World<M>,
) -> bool {
    &&& world.now <= at
    &&& is_process(model, world, process)
    &&& event_valid(world, process, event)
    &&& exists|i: int, j: int|
        #![trigger world.process[i].1.on_event(config, at, event)[j]]
    {
        &&& 0 <= i < world.process.len()
        &&& world.process[i].0 == process
        &&& {
            let outcomes = world.process[i].1.on_event(config, at, event);
            &&& 0 <= j < outcomes.len()
            &&& outcomes[j].send == send
            &&& next == land(world, i, process, at, outcomes[j])
        }
    }
}

impl<M: RoverModel> RoverSpec<M> {
    pub open spec fn init(model: M, config: M::Config) -> Self {
        RoverSpec {
            process: model.processes(config),
            network: Seq::empty(),
            now: 0,
        }
    }

    /// One atomic Rover transition.
    pub open spec fn step(
        self,
        model: M,
        config: M::Config,
        label: Lab<M>,
        next: Self,
    ) -> bool {
        let world = self;
        match label {
        Label::Input { recipient, at, message } => {
            &&& world.now <= at
            &&& is_process(model, world, recipient)
            &&& model.injectable(config, message)
            &&& next == inject(world, model.outside(), recipient, at, message)
        }
        Label::Process { process, at, event, send } => {
            process_transition(model, config, world, process, at, event, send, next)
        }
        Label::Outside { sender, at, message } => {
            &&& world.now <= at
            &&& exists|i: int| {
                &&& 0 <= i < world.network.len()
                &&& #[trigger] world.network[i] == Envelope {
                    sender,
                    recipient: model.outside(),
                    message,
                }
            }
            &&& next == observe_outside(world, at)
        }
        }
    }
}

/// One process outcome witnesses one complete Rover process step.
pub proof fn process_step<M: RoverModel>(
    model: M,
    config: M::Config,
    world: World<M>,
    i: int,
    at: Time,
    event: ProcessEvent<M::Pid, M::Message>,
    j: int,
)
    requires
        world.now <= at,
        0 <= i < world.process.len(),
        is_process(model, world, world.process[i].0),
        event_valid(world, world.process[i].0, event),
        0 <= j < world.process[i].1.on_event(config, at, event).len(),
    ensures
        ({
            let process = world.process[i].0;
            let outcome = world.process[i].1.on_event(config, at, event)[j];
            world.step(
                model,
                config,
                Label::Process { process, at, event, send: outcome.send },
                land(world, i, process, at, outcome),
            )
        }),
{
    let process = world.process[i].0;
    let outcome = world.process[i].1.on_event(config, at, event)[j];
    assert(exists|i2: int, j2: int|
        #![trigger world.process[i2].1.on_event(config, at, event)[j2]]
    {
        &&& 0 <= i2 < world.process.len()
        &&& world.process[i2].0 == process
        &&& {
            let outcomes = world.process[i2].1.on_event(config, at, event);
            &&& 0 <= j2 < outcomes.len()
            &&& outcomes[j2].send == outcome.send
            &&& land(world, i, process, at, outcome)
                == land(world, i2, process, at, outcomes[j2])
        }
    }) by {
        assert(0 <= i < world.process.len());
    }
    assert(process_transition(
        model,
        config,
        world,
        process,
        at,
        event,
        outcome.send,
        land(world, i, process, at, outcome),
    )) by {
        reveal(process_transition);
        assert(world.now <= at);
        assert(is_process(model, world, process));
        assert(event_valid(world, process, event));
        assert(exists|i2: int, j2: int|
            #![trigger world.process[i2].1.on_event(config, at, event)[j2]]
        {
            &&& 0 <= i2 < world.process.len()
            &&& world.process[i2].0 == process
            &&& {
                let outcomes = world.process[i2].1.on_event(config, at, event);
                &&& 0 <= j2 < outcomes.len()
                &&& outcomes[j2].send == outcome.send
                &&& land(world, i, process, at, outcome)
                    == land(world, i2, process, at, outcomes[j2])
            }
        });
    }
    reveal(RoverSpec::step);
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
        before::<M>(first, execution, i).step(m, config, execution[i].0, execution[i].1)
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

/// A boundary trace is valid when some legal execution shows exactly it.
pub open spec fn valid_trace<M: RoverModel>(
    m: M,
    config: M::Config,
    events: Seq<Ev<M>>,
) -> bool {
    exists|execution: Execution<M>|
        #![trigger legal(m, config, RoverSpec::<M>::init(m, config), execution), trace::<M>(execution)]
        legal(m, config, RoverSpec::<M>::init(m, config), execution)
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
        before.step(model, config, label, after),
    ensures
        network_extends::<M>(before, after),
{
    reveal(RoverSpec::step);
    reveal(network_extends);
    match label {
        Label::Input {
            recipient,
            at: _,
            message,
        } => {
            let suffix = seq![Envelope {
                sender: model.outside(),
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
                #![trigger before.process[i].1.on_event(
                    config,
                    at,
                    event,
                )[j]]
            {
                &&& 0 <= i < before.process.len()
                &&& before.process[i].0 == process
                &&& {
                    let outcomes = before.process[i].1.on_event(
                        config,
                        at,
                        event,
                    );
                    &&& 0 <= j < outcomes.len()
                    &&& after == land(before, i, process, at, outcomes[j])
                }
            };
            let j = choose|j: int|
                #![trigger before.process[i].1.on_event(
                    config,
                    at,
                    event,
                )[j]]
            {
                &&& 0 <= i < before.process.len()
                &&& before.process[i].0 == process
                &&& {
                    let outcomes = before.process[i].1.on_event(
                        config,
                        at,
                        event,
                    );
                    &&& 0 <= j < outcomes.len()
                    &&& after == land(before, i, process, at, outcomes[j])
                }
            };
            let outcome = before.process[i].1.on_event(
                config,
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
    assert(legal(m, config, RoverSpec::<M>::init(m, config), execution));
    assert(trace::<M>(execution) =~= Seq::<Ev<M>>::empty());
}

} // verus!
