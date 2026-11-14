//! Verified replay for Rover certificates.
//!
//! Search is untrusted. This module re-executes every named action and proves
//! that successful replay witnesses [`super::semantics::valid_trace`].

use vstd::prelude::*;

use crate::certificate::trusted::{copy, same};
use crate::Time;

#[allow(unused_imports)] // proof-only names are erased by ordinary Rust
use super::semantics::{self, Execution, Label, StepResultV, WorldV};
use super::{BoundaryEvent, Envelope, EventOf, ProcessEvent, RoverModel};

verus! {

/// One atomic Rover step named by a certificate.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum Action<P, M> {
    Inject {
        recipient: P,
        at: Time,
        message: M,
    },
    /// Take the `outcome`-th result of the model's local step.
    Process {
        slot: usize,
        process: P,
        at: Time,
        event: ProcessEvent<P, M>,
        outcome: usize,
    },
    Observe {
        sender: P,
        at: Time,
        message: M,
    },
}

pub type ActionOf<M> = Action<<M as RoverModel>::Pid, <M as RoverModel>::Message>;
pub type Certificate<M> = Vec<ActionOf<M>>;

/// The label a successful action must make.
pub(crate) open spec fn action_label<M: RoverModel>(
    m: M,
    config: M::Config,
    world: semantics::World<M>,
    action: ActionOf<M>,
) -> semantics::Lab<M> {
    match action {
        Action::Inject { recipient, at, message } =>
            Label::Input { recipient, at, message },
        Action::Process { slot, process, at, event, outcome } => {
            let result = m.spec_on_event(
                config,
                process,
                world.process[slot as int].1,
                at,
                event,
            )[outcome as int];
            Label::Process { process, at, event, send: result.send }
        }
        Action::Observe { sender, at, message } =>
            Label::Outside { sender, at, message },
    }
}

pub(crate) open spec fn shown<P, M>(
    action: Action<P, M>,
) -> Option<BoundaryEvent<P, M>> {
    match action {
        Action::Inject { recipient, at, message } =>
            Some(BoundaryEvent::Input { recipient, at, message }),
        Action::Process { .. } => None,
        Action::Observe { sender, at, message } =>
            Some(BoundaryEvent::Output { sender, at, message }),
    }
}

/// Executable replay state. Its view is exactly the mathematical Rover world.
pub(crate) struct World<'a, M: RoverModel> {
    pub(crate) model: &'a M,
    pub(crate) config: &'a M::Config,
    pub(crate) process: Vec<(M::Pid, M::State)>,
    pub(crate) network: Vec<Envelope<M::Pid, M::Message>>,
    pub(crate) now: Time,
}

impl<M: RoverModel> View for World<'_, M> {
    type V = semantics::World<M>;

    open(crate) spec fn view(&self) -> semantics::World<M> {
        WorldV {
            process: semantics::process_view::<M>(self.process@),
            network: self.network@,
            now: self.now,
        }
    }
}

impl<'a, M: RoverModel> World<'a, M> {
    pub(crate) fn initial(model: &'a M, config: &'a M::Config) -> (world: Self)
        ensures
            world@ == semantics::initial(*model, *config),
            world.model == model,
            world.config == config,
    {
        World {
            model,
            config,
            process: model.initial(config),
            network: Vec::new(),
            now: 0,
        }
    }

    /// Whether some initial process slot has this id.
    fn process_present(&self, pid: &M::Pid) -> (present: bool)
        ensures
            present ==> exists|i: int| 0 <= i < self@.process.len()
                && #[trigger] self@.process[i].0 == *pid,
    {
        for i in 0..self.process.len() {
            if same(&self.process[i].0, pid) {
                assert(self@.process[i as int].0 == *pid);
                return true;
            }
        }
        false
    }

    /// If this returns true, the receive is justified by an envelope in the
    /// append-only network.
    fn receive_valid(
        &self,
        recipient: &M::Pid,
        sender: &M::Pid,
        message: &M::Message,
    ) -> (valid: bool)
        ensures
            valid ==> exists|i: int| 0 <= i < self@.network.len()
                && #[trigger] self@.network[i] == (Envelope {
                    sender: *sender,
                    recipient: *recipient,
                    message: *message,
                }),
    {
        for i in 0..self.network.len() {
            let envelope = &self.network[i];
            if same(&envelope.sender, sender)
                && same(&envelope.recipient, recipient)
                && same(&envelope.message, message)
            {
                assert(self@.network[i as int] == Envelope {
                    sender: *sender,
                    recipient: *recipient,
                    message: *message,
                });
                return true;
            }
        }
        false
    }

    /// If this returns true, the exact output envelope was previously sent.
    fn output_sent(
        &self,
        sender: &M::Pid,
        outside: &M::Pid,
        message: &M::Message,
    ) -> (sent: bool)
        ensures
            sent ==> exists|i: int| 0 <= i < self@.network.len()
                && #[trigger] self@.network[i] == (Envelope {
                    sender: *sender,
                    recipient: *outside,
                    message: *message,
                }),
    {
        for i in 0..self.network.len() {
            let envelope = &self.network[i];
            if same(&envelope.sender, sender)
                && same(&envelope.recipient, outside)
                && same(&envelope.message, message)
            {
                assert(self@.network[i as int] == Envelope {
                    sender: *sender,
                    recipient: *outside,
                    message: *message,
                });
                return true;
            }
        }
        false
    }

    /// Append every message sent by one process.
    fn append_sends(
        &mut self,
        sender: M::Pid,
        send: Vec<(M::Pid, M::Message)>,
    )
        ensures
            final(self)@ == (WorldV {
                network: old(self)@.network + semantics::envelopes(sender, send@),
                ..old(self)@
            }),
            final(self).model == old(self).model,
            final(self).config == old(self).config,
    {
        let ghost before = self.network@;
        let ghost all = send@;
        let mut send = send;
        while !send.is_empty()
            invariant
                self.model == old(self).model,
                self.config == old(self).config,
                self@.process == old(self)@.process,
                self@.now == old(self)@.now,
                send@.len() <= all.len(),
                send@ == all.subrange(all.len() - send@.len(), all.len() as int),
                self@.network == before + semantics::envelopes(
                    sender,
                    all.subrange(0, all.len() - send@.len()),
                ),
            decreases send.len(),
        {
            let (recipient, message) = send.remove(0);
            self.network.push(Envelope {
                sender: copy(&sender),
                recipient,
                message,
            });
            proof {
                assert(send@ =~= all.subrange(all.len() - send@.len(), all.len() as int));
                assert(self@.network =~= before + semantics::envelopes(
                    sender,
                    all.subrange(0, all.len() - send@.len()),
                ));
            }
        }
        proof {
            assert(all.subrange(0, all.len() as int) =~= all);
            assert(semantics::envelopes(
                sender,
                all.subrange(0, all.len() as int),
            ) =~= semantics::envelopes(sender, all));
            assert(self@.network
                =~= before + semantics::envelopes(sender, all));
        }
    }

    /// Execute and validate one certificate action.
    pub(crate) fn apply(
        &mut self,
        action: &ActionOf<M>,
    ) -> (result: Result<Option<EventOf<M>>, ()>)
        ensures
            result is Ok ==> {
                let label = action_label(
                    *old(self).model,
                    *old(self).config,
                    old(self)@,
                    *action,
                );
                &&& semantics::step(
                    *old(self).model,
                    *old(self).config,
                    old(self)@,
                    label,
                    final(self)@,
                )
                &&& result->Ok_0 == shown(*action)
            },
            final(self).model == old(self).model,
            final(self).config == old(self).config,
    {
        let ghost original = self@;
        match action {
            Action::Inject { recipient, at, message } => {
                if *at < self.now {
                    return Err(());
                }
                let outside = self.model.outside();
                let is_outside = same(recipient, &outside);
                let is_process = self.process_present(recipient);
                if is_outside
                    || !is_process
                    || !self.model.injectable(self.config, message)
                {
                    return Err(());
                }
                let ghost before = self@;
                proof {
                    assert(!(*recipient == outside));
                }
                self.network.push(Envelope {
                    sender: outside,
                    recipient: copy(recipient),
                    message: copy(message),
                });
                self.now = *at;
                proof {
                    assert(!(*recipient == outside));
                    assert(outside == self.model.spec_outside());
                    assert(semantics::is_process(
                        *self.model,
                        before,
                        *recipient,
                    ));
                    assert(before == original);
                    assert(semantics::step(
                        *self.model,
                        *self.config,
                        original,
                        action_label(
                            *self.model,
                            *self.config,
                            original,
                            *action,
                        ),
                        self@,
                    ));
                    assert(shown(*action) == Some(BoundaryEvent::Input {
                        recipient: *recipient,
                        at: *at,
                        message: *message,
                    }));
                }
                Ok(Some(BoundaryEvent::Input {
                    recipient: copy(recipient),
                    at: *at,
                    message: copy(message),
                }))
            }
            Action::Process { slot, process, at, event, outcome } => {
                if *at < self.now {
                    return Err(());
                }
                let outside = self.model.outside();
                if same(process, &outside) || *slot >= self.process.len() {
                    return Err(());
                }
                if !same(&self.process[*slot].0, process) {
                    return Err(());
                }
                let state = copy(&self.process[*slot].1);
                let event_ok = match event {
                    ProcessEvent::Timeout => true,
                    ProcessEvent::Receive { sender, message } =>
                        self.receive_valid(process, sender, message),
                };
                if !event_ok {
                    return Err(());
                }
                proof {
                    reveal(semantics::event_valid);
                    match event {
                        ProcessEvent::Timeout => {}
                        ProcessEvent::Receive { sender, message } => {
                            assert(exists|i: int| 0 <= i < self@.network.len()
                                && #[trigger] self@.network[i] == Envelope {
                                    sender: *sender,
                                    recipient: *process,
                                    message: *message,
                                });
                        }
                    }
                    assert(semantics::event_valid(self@, *process, *event));
                }
                let ghost spec_outcomes = self.model.spec_on_event(
                    *self.config,
                    *process,
                    state@,
                    *at,
                    *event,
                );
                let mut outcomes =
                    self.model.on_event(self.config, process, &state, *at, event);
                if *outcome >= outcomes.len() {
                    return Err(());
                }
                let selected = outcomes.swap_remove(*outcome);
                let ghost next_state = selected.state@;
                let ghost selected_v = StepResultV {
                    state: next_state,
                    send: selected.send@,
                };
                let ghost before = self@;
                proof {
                    assert(selected_v == spec_outcomes[*outcome as int]);
                    assert(!(*process == outside));
                    assert(before.process[*slot as int].0 == *process);
                    assert(state@ == before.process[*slot as int].1);
                }
                self.process.set(
                    *slot,
                    (copy(process), selected.state),
                );
                proof {
                    assert(self@.process == before.process.update(
                        *slot as int,
                        (*process, next_state),
                    ));
                    assert(self@.network == before.network);
                    assert(self@.now == before.now);
                }
                self.append_sends(copy(process), selected.send);
                self.now = *at;
                proof {
                    assert(!(*process == outside));
                    assert(outside == self.model.spec_outside());
                    assert(semantics::is_process(
                        *self.model,
                        before,
                        *process,
                    ));
                    assert(self@ == semantics::land(
                        before,
                        *slot as int,
                        *process,
                        *at,
                        selected_v,
                    ));
                    assert(before == original);
                    assert(exists|i: int| 0 <= i < original.process.len()
                        && #[trigger] original.process[i].0 == *process) by {
                        assert(0 <= *slot as int);
                        assert((*slot as int) < original.process.len());
                    }
                    assert(semantics::step(
                        *self.model,
                        *self.config,
                        original,
                        action_label(
                            *self.model,
                            *self.config,
                            original,
                            *action,
                        ),
                        self@,
                    ));
                    assert(shown(*action) is None);
                }
                Ok(None)
            }
            Action::Observe { sender, at, message } => {
                if *at < self.now {
                    return Err(());
                }
                let outside = self.model.outside();
                if !self.output_sent(sender, &outside, message) {
                    return Err(());
                }
                let ghost before = self@;
                self.now = *at;
                proof {
                    assert(outside == self.model.spec_outside());
                    assert(before == original);
                    assert(semantics::step(
                        *self.model,
                        *self.config,
                        original,
                        action_label(
                            *self.model,
                            *self.config,
                            original,
                            *action,
                        ),
                        self@,
                    ));
                    assert(shown(*action) == Some(BoundaryEvent::Output {
                        sender: *sender,
                        at: *at,
                        message: *message,
                    }));
                }
                Ok(Some(BoundaryEvent::Output {
                    sender: copy(sender),
                    at: *at,
                    message: copy(message),
                }))
            }
        }
    }
}

/// A legal execution remains legal after one valid step.
proof fn extend<M: RoverModel>(
    m: M,
    config: M::Config,
    first: semantics::World<M>,
    execution: Execution<M>,
    label: semantics::Lab<M>,
    next: semantics::World<M>,
)
    requires
        semantics::legal(m, config, first, execution),
        semantics::step(
            m,
            config,
            semantics::before::<M>(first, execution, execution.len() as int),
            label,
            next,
        ),
    ensures
        semantics::legal(m, config, first, execution.push((label, next))),
        semantics::before::<M>(
            first,
            execution.push((label, next)),
            execution.len() as int + 1,
        ) == next,
        semantics::trace::<M>(execution.push((label, next)))
            == semantics::trace::<M>(execution) + semantics::observe(label),
{
    let more = execution.push((label, next));
    assert(more.drop_last() =~= execution);
    assert forall|i: int| 0 <= i < more.len() implies #[trigger]
        semantics::step(
            m,
            config,
            semantics::before::<M>(first, more, i),
            more[i].0,
            more[i].1,
        ) by {
        if i < execution.len() {
            assert(semantics::step(
                m,
                config,
                semantics::before::<M>(first, execution, i),
                execution[i].0,
                execution[i].1,
            ));
        }
    }
}

proof fn action_observe<M: RoverModel>(
    m: M,
    config: M::Config,
    world: semantics::World<M>,
    action: ActionOf<M>,
)
    ensures
        semantics::observe(action_label(m, config, world, action))
            == match shown(action) {
                Some(event) => seq![event],
                None => Seq::empty(),
            },
{
    match action {
        Action::Inject { .. } => {}
        Action::Process { .. } => {}
        Action::Observe { .. } => {}
    }
}

/// Replay a certificate and check that its visible labels are exactly `events`.
///
/// The search is irrelevant to this contract: any successfully replayed
/// certificate proves that the supplied trace is a valid Rover trace.
pub fn replay<M: RoverModel>(
    model: &M,
    config: &M::Config,
    events: &[EventOf<M>],
    certificate: &[ActionOf<M>],
) -> (result: Result<(), usize>)
    ensures
        result is Ok ==> semantics::valid_trace(*model, *config, events@),
{
    let mut world = World::initial(model, config);
    let mut visible = 0usize;
    let ghost first = semantics::initial(*model, *config);
    let ghost mut execution: Execution<M> = Seq::empty();

    for k in 0..certificate.len()
        invariant
            world.model == model,
            world.config == config,
            visible <= events.len(),
            semantics::legal(*model, *config, first, execution),
            semantics::before::<M>(first, execution, execution.len() as int)
                == world@,
            semantics::trace::<M>(execution)
                == events@.subrange(0, visible as int),
    {
        let ghost before_world = world@;
        let ghost label = action_label(
            *model,
            *config,
            before_world,
            certificate@[k as int],
        );
        let shown = match world.apply(&certificate[k]) {
            Ok(value) => value,
            Err(()) => return Err(visible),
        };
        match shown {
            Some(event) => {
                if visible >= events.len() || !same(&events[visible], &event) {
                    return Err(visible);
                }
                visible += 1;
                proof {
                    action_observe(
                        *model,
                        *config,
                        before_world,
                        certificate@[k as int],
                    );
                    extend(
                        *model,
                        *config,
                        first,
                        execution,
                        label,
                        world@,
                    );
                    execution = execution.push((label, world@));
                    assert(semantics::trace::<M>(execution)
                        =~= events@.subrange(0, visible as int));
                }
            }
            None => {
                proof {
                    action_observe(
                        *model,
                        *config,
                        before_world,
                        certificate@[k as int],
                    );
                    extend(
                        *model,
                        *config,
                        first,
                        execution,
                        label,
                        world@,
                    );
                    execution = execution.push((label, world@));
                }
            }
        }
    }
    if visible != events.len() {
        return Err(visible);
    }
    proof {
        assert(events@.subrange(0, events@.len() as int) =~= events@);
        assert(semantics::trace::<M>(execution) == events@);
        assert(semantics::valid_trace(*model, *config, events@));
    }
    Ok(())
}

} // verus!

// Search needs cheap snapshots. This code is ordinary Rust; replay remains the
// verified acceptance boundary.
impl<M: RoverModel> Clone for World<'_, M> {
    fn clone(&self) -> Self {
        World {
            model: self.model,
            config: self.config,
            process: self.process.clone(),
            network: self.network.clone(),
            now: self.now,
        }
    }
}

impl<M: RoverModel> World<'_, M> {
    pub(crate) fn same_snapshot(&self, other: &Self) -> bool
    where
        M::State: PartialEq,
    {
        self.process == other.process && self.network == other.network && self.now == other.now
    }
}
