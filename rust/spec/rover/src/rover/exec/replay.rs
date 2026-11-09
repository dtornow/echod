//! Verified replay for Rover certificates.
//!
//! Search is untrusted. This module re-executes every named action and proves
//! that successful replay witnesses [`crate::rover::spec::valid_trace`].

use vstd::prelude::*;

use std::collections::BTreeSet;

#[allow(unused_imports)] // proof-only names are erased by ordinary Rust
use super::super::spec::{
    self as specification, Execution, Label, State as SpecState, StepResultV,
};
#[allow(unused_imports)] // proof-only names are erased by ordinary Rust
use super::{Proc as ExecProc, Spec as ExecSpec};
use super::super::comm::{BoundaryEvent, Envelope, ProcessEvent, Time};
#[allow(unused_imports)]
use super::super::spec::{Proc as SpecProc, Spec as SpecModel};

verus! {

#[verifier::external_body]
fn copy<T: Clone>(value: &T) -> (copy: T)
    ensures
        copy == *value,
{
    value.clone()
}

#[verifier::external_body]
fn same<T: PartialEq>(left: &T, right: &T) -> (equal: bool)
    ensures
        equal == (*left == *right),
{
    left == right
}

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
    Clock {
        at: Time,
    },
}

pub type Certificate<P, M> = Vec<Action<P, M>>;

/// The label a successful action must make.
pub(crate) open spec fn action_label<M: ExecSpec>(
    model: M::Spec,
    config: <M::Spec as SpecModel>::Config,
    world: SpecState<M::Spec>,
    action: Action<
        <M::Spec as SpecModel>::Pid,
        <M::Spec as SpecModel>::Message,
    >,
) -> Label<
    <M::Spec as SpecModel>::Pid,
    <M::Spec as SpecModel>::Message,
> {
    match action {
        Action::Inject { recipient, at, message } =>
            Label::Input { recipient, at, message },
        Action::Process { slot, process, at, event, outcome } => {
            let result = world.process[slot as int].1.on_event(
                config,
                at,
                event,
            )[outcome as int];
            Label::Process { process, at, event, send: result.send }
        }
        Action::Observe { sender, at, message } =>
            Label::Outside { sender, at, message },
        Action::Clock { at } => Label::Clock { at },
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
        Action::Clock { at } => Some(BoundaryEvent::Clock { at }),
    }
}

/// Executable replay state. Its view is exactly the mathematical Rover world.
pub(crate) struct ReplayState<'a, M: ExecSpec> {
    pub(crate) model: &'a M,
    pub(crate) config: &'a <M::Spec as SpecModel>::Config,
    pub(crate) process: Vec<(<M::Spec as SpecModel>::Pid, M::Proc)>,
    pub(crate) network: Vec<Envelope<
        <M::Spec as SpecModel>::Pid,
        <M::Spec as SpecModel>::Message,
    >>,
    pub(crate) delivered: Vec<Envelope<
        <M::Spec as SpecModel>::Pid,
        <M::Spec as SpecModel>::Message,
    >>,
    pub(crate) now: Time,
    pub(crate) marks: Vec<&'static str>,
}

impl<M: ExecSpec> View for ReplayState<'_, M> {
    type V = SpecState<M::Spec>;

    open(crate) spec fn view(&self) -> SpecState<M::Spec> {
        SpecState {
            process: process_view::<M>(self.process@),
            network: self.network@,
            now: self.now,
        }
    }
}

/// Executable process slots as the mathematical world sees their state views.
pub(crate) open spec fn process_view<M: ExecSpec>(
    process: Seq<(<M::Spec as SpecModel>::Pid, M::Proc)>,
) -> Seq<(
    <M::Spec as SpecModel>::Pid,
    <M::Spec as SpecModel>::Proc,
)> {
    process.map_values(
        |entry: (<M::Spec as SpecModel>::Pid, M::Proc)| (entry.0, entry.1@)
    )
}

impl<'a, M: ExecSpec> ReplayState<'a, M> {
    pub(crate) fn initial(
        model: &'a M,
        config: &'a <M::Spec as SpecModel>::Config,
    ) -> (world: Self)
        ensures
            world@ == SpecState::<M::Spec>::init(model.spec(), *config),
            world.model == model,
            world.config == config,
    {
        ReplayState {
            model,
            config,
            process: model.initial(config),
            network: Vec::new(),
            delivered: Vec::new(),
            now: 0,
            marks: Vec::new(),
        }
    }

    /// Whether some initial process slot has this id.
    fn process_present(&self, pid: &<M::Spec as SpecModel>::Pid) -> (present: bool)
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
        recipient: &<M::Spec as SpecModel>::Pid,
        sender: &<M::Spec as SpecModel>::Pid,
        message: &<M::Spec as SpecModel>::Message,
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
        sender: &<M::Spec as SpecModel>::Pid,
        outside: &<M::Spec as SpecModel>::Pid,
        message: &<M::Spec as SpecModel>::Message,
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
        sender: <M::Spec as SpecModel>::Pid,
        send: Vec<(
            <M::Spec as SpecModel>::Pid,
            <M::Spec as SpecModel>::Message,
        )>,
    )
        ensures
            final(self)@ == (SpecState {
                network: old(self)@.network + specification::envelopes(sender, send@),
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
                self@.network == before + specification::envelopes(
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
                assert(self@.network =~= before + specification::envelopes(
                    sender,
                    all.subrange(0, all.len() - send@.len()),
                ));
            }
        }
        proof {
            assert(all.subrange(0, all.len() as int) =~= all);
            assert(specification::envelopes(
                sender,
                all.subrange(0, all.len() as int),
            ) =~= specification::envelopes(sender, all));
            assert(self@.network
                =~= before + specification::envelopes(sender, all));
        }
    }

    /// Execute and validate one certificate action.
    pub(crate) fn apply(
        &mut self,
        action: &Action<
            <M::Spec as SpecModel>::Pid,
            <M::Spec as SpecModel>::Message,
        >,
    ) -> (result: Result<Option<BoundaryEvent<
        <M::Spec as SpecModel>::Pid,
        <M::Spec as SpecModel>::Message,
    >>, ()>)
        ensures
            result is Ok ==> {
                let label = action_label::<M>(
                    old(self).model.spec(),
                    *old(self).config,
                    old(self)@,
                    *action,
                );
                &&& old(self)@.step(
                    old(self).model.spec(),
                    *old(self).config,
                    label,
                    final(self)@,
                )
                &&& result->Ok_0 == shown(*action)
            },
            final(self).model == old(self).model,
            final(self).config == old(self).config,
    {
        let ghost original = self@;
        self.marks.clear();
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
                    assert(outside == self.model.spec().outside());
                    assert(specification::is_process(
                        self.model.spec(),
                        before,
                        *recipient,
                    ));
                    assert(before == original);
                    assert(original.step(
                        self.model.spec(),
                        *self.config,
                        action_label::<M>(
                            self.model.spec(),
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
                    reveal(specification::event_valid);
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
                    assert(specification::event_valid(self@, *process, *event));
                }
                let ghost spec_outcomes = state@.on_event(
                    *self.config,
                    *at,
                    *event,
                );
                let mut outcomes = state.on_event(self.config, *at, event);
                if *outcome >= outcomes.len() {
                    return Err(());
                }
                let selected = outcomes.swap_remove(*outcome);
                self.marks = selected.marks;
                if let ProcessEvent::Receive { sender, message } = event {
                    self.delivered.push(Envelope {
                        sender: copy(sender),
                        recipient: copy(process),
                        message: copy(message),
                    });
                }
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
                    assert(outside == self.model.spec().outside());
                    assert(specification::is_process(
                        self.model.spec(),
                        before,
                        *process,
                    ));
                    assert(self@ == specification::land(
                        before,
                        *slot as int,
                        *process,
                        *at,
                        selected_v,
                    ));
                    assert(before == original);
                    assert(original.now <= *at);
                    assert(specification::is_process(
                        self.model.spec(),
                        original,
                        *process,
                    ));
                    assert(specification::event_valid(original, *process, *event));
                    assert(original.process[*slot as int].0 == *process);
                    assert(exists|i: int| 0 <= i < original.process.len()
                        && #[trigger] original.process[i].0 == *process) by {
                        assert(0 <= *slot as int);
                        assert((*slot as int) < original.process.len());
                    }
                    assert(0 <= *outcome as int && (*outcome as int)
                        < original.process[*slot as int].1.on_event(
                            *self.config,
                            *at,
                            *event,
                        ).len());
                    assert(original.process[*slot as int].1.on_event(
                        *self.config,
                        *at,
                        *event,
                    )[*outcome as int] == selected_v);
                    let label = action_label::<M>(
                        self.model.spec(),
                        *self.config,
                        original,
                        *action,
                    );
                    assert(label == Label::Process {
                        process: *process,
                        at: *at,
                        event: *event,
                        send: selected_v.send,
                    });
                    assert(exists|i: int, j: int|
                        #![trigger original.process[i].1.on_event(
                            *self.config,
                            *at,
                            *event,
                        )[j]]
                    {
                        &&& 0 <= i < original.process.len()
                        &&& original.process[i].0 == *process
                        &&& {
                            let outcomes = original.process[i].1.on_event(
                                *self.config,
                                *at,
                                *event,
                            );
                            &&& 0 <= j < outcomes.len()
                            &&& outcomes[j].send == selected_v.send
                            &&& self@ == specification::land(
                                original,
                                i,
                                *process,
                                *at,
                                outcomes[j],
                            )
                        }
                    }) by {
                        assert(self@ == specification::land(
                            original,
                            *slot as int,
                            *process,
                            *at,
                            selected_v,
                        ));
                    }
                    specification::process_step(
                        self.model.spec(),
                        *self.config,
                        original,
                        *slot as int,
                        *at,
                        *event,
                        *outcome as int,
                    );
                    reveal(SpecState::step);
                    assert(original.step(
                        self.model.spec(),
                        *self.config,
                        label,
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
                    assert(outside == self.model.spec().outside());
                    assert(before == original);
                    assert(original.step(
                        self.model.spec(),
                        *self.config,
                        action_label::<M>(
                            self.model.spec(),
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
            Action::Clock { at } => {
                if *at < self.now {
                    return Err(());
                }
                let ghost before = self@;
                self.now = *at;
                proof {
                    assert(before == original);
                    assert(original.step(
                        self.model.spec(),
                        *self.config,
                        action_label::<M>(
                            self.model.spec(),
                            *self.config,
                            original,
                            *action,
                        ),
                        self@,
                    ));
                    assert(shown(*action) == Some(BoundaryEvent::Clock { at: *at }));
                }
                Ok(Some(BoundaryEvent::Clock { at: *at }))
            }
        }
    }
}

/// A legal execution remains legal after one valid step.
proof fn extend<S: SpecModel>(
    spec: S,
    config: S::Config,
    first: SpecState<S>,
    execution: Execution<S>,
    label: Label<S::Pid, S::Message>,
    next: SpecState<S>,
)
    requires
        specification::legal(spec, config, first, execution),
        specification::before::<S>(first, execution, execution.len() as int).step(
            spec,
            config,
            label,
            next,
        ),
    ensures
        specification::legal(spec, config, first, execution.push((label, next))),
        specification::before::<S>(
            first,
            execution.push((label, next)),
            execution.len() as int + 1,
        ) == next,
        specification::trace::<S>(execution.push((label, next)))
            == specification::trace::<S>(execution) + specification::observe(label),
{
    let more = execution.push((label, next));
    assert(more.drop_last() =~= execution);
    assert forall|i: int| 0 <= i < more.len() implies #[trigger]
        specification::before::<S>(first, more, i).step(
            spec,
            config,
            more[i].0,
            more[i].1,
        ) by {
        if i < execution.len() {
            assert(specification::before::<S>(first, execution, i).step(
                spec,
                config,
                execution[i].0,
                execution[i].1,
            ));
        }
    }
}

proof fn action_observe<M: ExecSpec>(
    model: M::Spec,
    config: <M::Spec as SpecModel>::Config,
    world: SpecState<M::Spec>,
    action: Action<
        <M::Spec as SpecModel>::Pid,
        <M::Spec as SpecModel>::Message,
    >,
)
    ensures
        specification::observe(action_label::<M>(model, config, world, action))
            == match shown(action) {
                Some(event) => seq![event],
                None => Seq::empty(),
            },
{
    match action {
        Action::Inject { .. } => {}
        Action::Process { .. } => {}
        Action::Observe { .. } => {}
        Action::Clock { .. } => {}
    }
}

/// Replay a certificate and check that its visible labels are exactly `events`.
///
/// The search is irrelevant to this contract: any successfully replayed
/// certificate proves that the supplied trace is a valid Rover trace.
pub fn replay<M: ExecSpec>(
    model: &M,
    config: &<M::Spec as SpecModel>::Config,
    events: &[BoundaryEvent<
        <M::Spec as SpecModel>::Pid,
        <M::Spec as SpecModel>::Message,
    >],
    certificate: &[Action<
        <M::Spec as SpecModel>::Pid,
        <M::Spec as SpecModel>::Message,
    >],
) -> (result: Result<(), usize>)
    ensures
        result is Ok ==> specification::valid_trace(model.spec(), *config, events@),
{
    let mut world = ReplayState::initial(model, config);
    let mut visible = 0usize;
    let ghost first = SpecState::<M::Spec>::init(model.spec(), *config);
    let ghost mut execution: Execution<M::Spec> = Seq::empty();

    for k in 0..certificate.len()
        invariant
            world.model == model,
            world.config == config,
            visible <= events.len(),
            specification::legal(model.spec(), *config, first, execution),
            specification::before::<M::Spec>(first, execution, execution.len() as int)
                == world@,
            specification::trace::<M::Spec>(execution)
                == events@.subrange(0, visible as int),
    {
        let ghost before_world = world@;
        let ghost label = action_label::<M>(
            model.spec(),
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
                    action_observe::<M>(
                        model.spec(),
                        *config,
                        before_world,
                        certificate@[k as int],
                    );
                    extend(
                        model.spec(),
                        *config,
                        first,
                        execution,
                        label,
                        world@,
                    );
                    execution = execution.push((label, world@));
                    assert(specification::trace::<M::Spec>(execution)
                        =~= events@.subrange(0, visible as int));
                }
            }
            None => {
                proof {
                    action_observe::<M>(
                        model.spec(),
                        *config,
                        before_world,
                        certificate@[k as int],
                    );
                    extend(
                        model.spec(),
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
        assert(specification::trace::<M::Spec>(execution) == events@);
        assert(specification::valid_trace(model.spec(), *config, events@));
    }
    Ok(())
}

} // verus!

/// Coverage labels along a certificate that replays successfully.
pub fn marks<M: ExecSpec>(
    model: &M,
    config: &<M::Spec as SpecModel>::Config,
    certificate: &[Action<
        <M::Spec as SpecModel>::Pid,
        <M::Spec as SpecModel>::Message,
    >],
) -> Option<BTreeSet<&'static str>> {
    let mut state = ReplayState::initial(model, config);
    let mut marks = BTreeSet::new();
    for action in certificate {
        state.apply(action).ok()?;
        marks.extend(state.marks.iter().copied());
    }
    Some(marks)
}

// Search needs cheap snapshots. This code is ordinary Rust; replay remains the
// verified acceptance boundary.
impl<M: ExecSpec> Clone for ReplayState<'_, M> {
    fn clone(&self) -> Self {
        ReplayState {
            model: self.model,
            config: self.config,
            process: self.process.clone(),
            network: self.network.clone(),
            delivered: self.delivered.clone(),
            now: self.now,
            marks: self.marks.clone(),
        }
    }
}

impl<M: ExecSpec> ReplayState<'_, M> {
    pub(crate) fn same_snapshot(&self, other: &Self) -> bool {
        self.process == other.process && self.network == other.network && self.now == other.now
    }
}
