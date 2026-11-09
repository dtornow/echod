//! Generic Rover trace refinement from a forward simulation.
//!
//! Concrete and abstract models may use entirely different process ids and
//! internal messages. Each supplies a projection from its labels to one shared
//! boundary type. A model-specific proof relates initial worlds and proves
//! `simulation`; this module proves once that those local facts imply trace
//! inclusion for executions of every finite length.

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports))]

use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use super::{before, legal, Execution, Label, Spec, State};

verus! {

/// Where an execution ends.
pub open spec fn end<M: Spec>(
    first: State<M>,
    execution: Execution<M>,
) -> State<M> {
    if execution.len() == 0 {
        first
    } else {
        execution.last().1
    }
}

/// Project an execution through a model-specific boundary observer.
pub open spec fn project<M: Spec>(
    model: M,
    execution: Execution<M>,
) -> Seq<M::Boundary>
    decreases execution.len(),
{
    if execution.len() == 0 {
        Seq::empty()
    } else {
        project::<M>(model, execution.drop_last())
            + model.observe(execution.last().0)
    }
}

/// A boundary trace admitted by one Rover model.
pub open spec fn valid_boundary_trace<M: Spec>(
    model: M,
    config: M::Config,
    events: Seq<M::Boundary>,
) -> bool {
    exists|execution: Execution<M>|
        #![trigger legal(model, config, State::<M>::init(model, config), execution)]
        legal(model, config, State::<M>::init(model, config), execution)
            && project::<M>(model, execution) == events
}

/// Abstract steps matching one concrete label's visible boundary contribution.
pub open spec fn matches<A: Spec>(
    abstract_model: A,
    abstract_config: A::Config,
    start: State<A>,
    visible: Seq<A::Boundary>,
    finish: State<A>,
) -> bool {
    exists|execution: Execution<A>|
        #![trigger legal(abstract_model, abstract_config, start, execution)]
        legal(abstract_model, abstract_config, start, execution)
            && project::<A>(abstract_model, execution) == visible
            && end::<A>(start, execution) == finish
}

/// Every concrete step from related worlds has a matching finite abstract run
/// and leaves the worlds related again.
pub open spec fn simulation<
    C: Spec,
    A: Spec<Boundary = C::Boundary>,
>(
    concrete_model: C,
    concrete_config: C::Config,
    abstract_model: A,
    abstract_config: A::Config,
    relation: spec_fn(State<C>, State<A>) -> bool,
) -> bool {
    forall|
        concrete_before: State<C>,
        concrete_label: Label<C::Pid, C::Message>,
        concrete_after: State<C>,
        abstract_before: State<A>,
    |
        #![trigger
            relation(concrete_before, abstract_before),
            concrete_before.step(
                concrete_model,
                concrete_config,
                concrete_label,
                concrete_after,
            )
        ]
        relation(concrete_before, abstract_before)
        && concrete_before.step(
            concrete_model,
            concrete_config,
            concrete_label,
            concrete_after,
        )
        ==> exists|abstract_after: State<A>|
            #[trigger] matches(
                abstract_model,
                abstract_config,
                abstract_before,
                concrete_model.observe(concrete_label),
                abstract_after,
            )
            && relation(concrete_after, abstract_after)
}

/// Trace inclusion at the shared boundary.
pub open spec fn refines<
    C: Spec,
    A: Spec<Boundary = C::Boundary>,
>(
    concrete_model: C,
    concrete_config: C::Config,
    abstract_model: A,
    abstract_config: A::Config,
) -> bool {
    forall|events: Seq<C::Boundary>|
        #![trigger valid_boundary_trace(
            concrete_model,
            concrete_config,
            events,
        )]
        valid_boundary_trace(
            concrete_model,
            concrete_config,
            events,
        )
        ==> valid_boundary_trace(
            abstract_model,
            abstract_config,
            events,
        )
}

// ---------------------------------------------------------------------------
// Execution algebra
// ---------------------------------------------------------------------------

pub proof fn lemma_project_add<M: Spec>(
    model: M,
    first: Execution<M>,
    second: Execution<M>,
)
    ensures
        project::<M>(model, first + second)
            == project::<M>(model, first)
                + project::<M>(model, second),
    decreases second.len(),
{
    if second.len() == 0 {
        assert(first + second =~= first);
    } else {
        lemma_project_add::<M>(model, first, second.drop_last());
        assert((first + second).drop_last() =~= first + second.drop_last());
        assert((first + second).last() == second.last());
        assert(project::<M>(model, first + second)
            =~= project::<M>(model, first)
                + project::<M>(model, second));
    }
}

pub proof fn lemma_end_add<M: Spec>(
    first: State<M>,
    prefix: Execution<M>,
    suffix: Execution<M>,
)
    ensures
        end::<M>(first, prefix + suffix)
            == end::<M>(end::<M>(first, prefix), suffix),
{
    if suffix.len() == 0 {
        assert(prefix + suffix =~= prefix);
    } else {
        assert((prefix + suffix).last() == suffix.last());
    }
}

pub proof fn lemma_legal_add<M: Spec>(
    model: M,
    config: M::Config,
    first: State<M>,
    prefix: Execution<M>,
    suffix: Execution<M>,
)
    requires
        legal(model, config, first, prefix),
        legal(model, config, end::<M>(first, prefix), suffix),
    ensures
        legal(model, config, first, prefix + suffix),
{
    let combined = prefix + suffix;
    assert forall|i: int| 0 <= i < combined.len() implies
        #[trigger] before::<M>(first, combined, i).step(
            model,
            config,
            combined[i].0,
            combined[i].1,
        ) by {
        if i < prefix.len() {
            assert(combined[i] == prefix[i]);
            assert(before::<M>(first, combined, i)
                == before::<M>(first, prefix, i));
        } else {
            let j = i - prefix.len();
            assert(combined[i] == suffix[j]);
            assert(before::<M>(first, combined, i)
                == before::<M>(end::<M>(first, prefix), suffix, j));
        }
    }
}

// ---------------------------------------------------------------------------
// Lift one-step simulation to arbitrary executions
// ---------------------------------------------------------------------------

proof fn lemma_simulate_prefix<
    C: Spec,
    A: Spec<Boundary = C::Boundary>,
>(
    concrete_model: C,
    concrete_config: C::Config,
    abstract_model: A,
    abstract_config: A::Config,
    relation: spec_fn(State<C>, State<A>) -> bool,
    concrete_execution: Execution<C>,
    k: int,
)
    requires
        relation(
            State::<C>::init(concrete_model, concrete_config),
            State::<A>::init(abstract_model, abstract_config),
        ),
        simulation(
            concrete_model,
            concrete_config,
            abstract_model,
            abstract_config,
            relation,
        ),
        legal(
            concrete_model,
            concrete_config,
            State::<C>::init(concrete_model, concrete_config),
            concrete_execution,
        ),
        0 <= k <= concrete_execution.len(),
    ensures
        exists|abstract_execution: Execution<A>|
            #![trigger legal(
                abstract_model,
                abstract_config,
                State::<A>::init(abstract_model, abstract_config),
                abstract_execution,
            )]
            legal(
                abstract_model,
                abstract_config,
                State::<A>::init(abstract_model, abstract_config),
                abstract_execution,
            )
            && project::<A>(abstract_model, abstract_execution)
                == project::<C>(
                    concrete_model,
                    concrete_execution.take(k),
                )
            && relation(
                before::<C>(
                    State::<C>::init(concrete_model, concrete_config),
                    concrete_execution,
                    k,
                ),
                end::<A>(
                    State::<A>::init(abstract_model, abstract_config),
                    abstract_execution,
                ),
            ),
    decreases k,
{
    let concrete_initial = State::<C>::init(concrete_model, concrete_config);
    let abstract_initial = State::<A>::init(abstract_model, abstract_config);
    if k == 0 {
        let abstract_execution = Execution::<A>::empty();
        assert(concrete_execution.take(0)
            =~= Execution::<C>::empty());
        assert(project::<A>(abstract_model, abstract_execution)
            =~= Seq::<C::Boundary>::empty());
        assert(project::<C>(
            concrete_model,
            concrete_execution.take(0),
        ) =~= Seq::<C::Boundary>::empty());
        assert(before::<C>(
            concrete_initial,
            concrete_execution,
            0,
        ) == concrete_initial);
        assert(end::<A>(abstract_initial, abstract_execution)
            == abstract_initial);
        assert(legal(
            abstract_model,
            abstract_config,
            abstract_initial,
            abstract_execution,
        ));
        assert(relation(concrete_initial, abstract_initial));
        assert(exists|execution: Execution<A>|
            #[trigger] legal(
                abstract_model,
                abstract_config,
                abstract_initial,
                execution,
            )
            && project::<A>(abstract_model, execution)
                == project::<C>(
                    concrete_model,
                    concrete_execution.take(0),
                )
            && relation(
                before::<C>(
                    concrete_initial,
                    concrete_execution,
                    0,
                ),
                end::<A>(abstract_initial, execution),
            ));
    } else {
        lemma_simulate_prefix(
            concrete_model,
            concrete_config,
            abstract_model,
            abstract_config,
            relation,
            concrete_execution,
            k - 1,
        );
        let abstract_prefix = choose|execution: Execution<A>|
            #![trigger legal(
                abstract_model,
                abstract_config,
                abstract_initial,
                execution,
            )]
            legal(
                abstract_model,
                abstract_config,
                abstract_initial,
                execution,
            )
            && project::<A>(
                abstract_model,
                execution,
            ) == project::<C>(
                concrete_model,
                concrete_execution.take(k - 1),
            )
            && relation(
                before::<C>(
                    concrete_initial,
                    concrete_execution,
                    k - 1,
                ),
                end::<A>(abstract_initial, execution),
            );
        let concrete_before =
            before::<C>(concrete_initial, concrete_execution, k - 1);
        let concrete_label = concrete_execution[k - 1].0;
        let concrete_after = concrete_execution[k - 1].1;
        let abstract_before = end::<A>(abstract_initial, abstract_prefix);
        assert(concrete_before.step(
            concrete_model,
            concrete_config,
            concrete_label,
            concrete_after,
        ));
        let abstract_after = choose|world: State<A>|
            #[trigger] matches(
                abstract_model,
                abstract_config,
                abstract_before,
                concrete_model.observe(concrete_label),
                world,
            )
            && relation(concrete_after, world);
        let abstract_suffix = choose|execution: Execution<A>|
            #![trigger legal(
                abstract_model,
                abstract_config,
                abstract_before,
                execution,
            )]
            legal(
                abstract_model,
                abstract_config,
                abstract_before,
                execution,
            )
            && project::<A>(
                abstract_model,
                execution,
            ) == concrete_model.observe(concrete_label)
            && end::<A>(abstract_before, execution) == abstract_after;
        let abstract_execution = abstract_prefix + abstract_suffix;
        lemma_legal_add(
            abstract_model,
            abstract_config,
            abstract_initial,
            abstract_prefix,
            abstract_suffix,
        );
        lemma_project_add::<A>(
            abstract_model,
            abstract_prefix,
            abstract_suffix,
        );
        lemma_end_add::<A>(
            abstract_initial,
            abstract_prefix,
            abstract_suffix,
        );
        assert(concrete_execution.take(k).drop_last()
            =~= concrete_execution.take(k - 1));
        assert(concrete_execution.take(k).last()
            == concrete_execution[k - 1]);
        assert(project::<C>(
            concrete_model,
            concrete_execution.take(k),
        ) =~= project::<C>(
            concrete_model,
            concrete_execution.take(k - 1),
        ) + concrete_model.observe(concrete_label));
        assert(before::<C>(
            concrete_initial,
            concrete_execution,
            k,
        ) == concrete_after);
        assert(end::<A>(abstract_initial, abstract_execution)
            == abstract_after);
        assert(legal(
            abstract_model,
            abstract_config,
            abstract_initial,
            abstract_execution,
        ));
        assert(project::<A>(
            abstract_model,
            abstract_execution,
        ) == project::<C>(
            concrete_model,
            concrete_execution.take(k),
        ));
        assert(relation(
            before::<C>(
                concrete_initial,
                concrete_execution,
                k,
            ),
            end::<A>(abstract_initial, abstract_execution),
        ));
        assert(exists|execution: Execution<A>|
            #[trigger] legal(
                abstract_model,
                abstract_config,
                abstract_initial,
                execution,
            )
            && project::<A>(abstract_model, execution)
                == project::<C>(
                    concrete_model,
                    concrete_execution.take(k),
                )
            && relation(
                before::<C>(
                    concrete_initial,
                    concrete_execution,
                    k,
                ),
                end::<A>(abstract_initial, execution),
            ));
    }
}

/// The generic theorem: a related initial world and a proved forward
/// simulation imply concrete boundary traces are included in abstract traces.
pub proof fn concrete_refines_abstract<
    C: Spec,
    A: Spec<Boundary = C::Boundary>,
>(
    concrete_model: C,
    concrete_config: C::Config,
    abstract_model: A,
    abstract_config: A::Config,
    relation: spec_fn(State<C>, State<A>) -> bool,
)
    requires
        relation(
            State::<C>::init(concrete_model, concrete_config),
            State::<A>::init(abstract_model, abstract_config),
        ),
        simulation(
            concrete_model,
            concrete_config,
            abstract_model,
            abstract_config,
            relation,
        ),
    ensures
        refines(
            concrete_model,
            concrete_config,
            abstract_model,
            abstract_config,
        ),
{
    assert forall|events: Seq<C::Boundary>|
        #![trigger valid_boundary_trace(
            concrete_model,
            concrete_config,
            events,
        )]
        valid_boundary_trace(
            concrete_model,
            concrete_config,
            events,
        )
        implies valid_boundary_trace(
            abstract_model,
            abstract_config,
            events,
        ) by {
        let concrete_initial = State::<C>::init(concrete_model, concrete_config);
        let concrete_execution = choose|execution: Execution<C>|
            #![trigger legal(
                concrete_model,
                concrete_config,
                concrete_initial,
                execution,
            )]
            legal(
                concrete_model,
                concrete_config,
                concrete_initial,
                execution,
            )
            && project::<C>(concrete_model, execution) == events;
        lemma_simulate_prefix(
            concrete_model,
            concrete_config,
            abstract_model,
            abstract_config,
            relation,
            concrete_execution,
            concrete_execution.len() as int,
        );
        assert(concrete_execution.take(concrete_execution.len() as int)
            =~= concrete_execution);
        let abstract_execution = choose|execution: Execution<A>|
            #![trigger legal(
                abstract_model,
                abstract_config,
                State::<A>::init(abstract_model, abstract_config),
                execution,
            )]
            legal(
                abstract_model,
                abstract_config,
                State::<A>::init(abstract_model, abstract_config),
                execution,
            )
            && project::<A>(
                abstract_model,
                execution,
            ) == project::<C>(
                concrete_model,
                concrete_execution,
            )
            && relation(
                end::<C>(concrete_initial, concrete_execution),
                end::<A>(
                    State::<A>::init(abstract_model, abstract_config),
                    execution,
                ),
            );
        assert(project::<A>(
            abstract_model,
            abstract_execution,
        ) == events);
    }
}

} // verus!
