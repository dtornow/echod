//! The wire's tags, read back: what `tags_in` writes, `tags_get` finds. The
//! four tags the model knows are the four keys the wire writes, under
//! distinct names, so each reads back as it was written.

use vstd::prelude::*;

use echod_kernel::object::first_dispatch;
use echod_kernel::tags::*;
use echod_kernel::tags_proof::lemma_tags_get_append;
use echod_kernel::types::*;
use resonate::twins::*;
use resonate::Tags;

use crate::theorem::promise_v;
use crate::translate::*;

verus! {

pub open spec fn key_scope() -> Chars { "resonate:scope"@ }

/// The keys the wire writes, and the one it never does, are distinct words.
pub proof fn lemma_keys_distinct()
    ensures
        key_target() != key_external(),
        key_target() != key_timer(),
        key_target() != key_delay(),
        key_target() != key_scope(),
        key_external() != key_timer(),
        key_external() != key_delay(),
        key_external() != key_scope(),
        key_timer() != key_delay(),
        key_timer() != key_scope(),
        key_delay() != key_scope(),
{
    reveal_strlit("resonate:target");
    reveal_strlit("resonate:external");
    reveal_strlit("resonate:timer");
    reveal_strlit("resonate:delay");
    reveal_strlit("resonate:scope");
}

/// One segment of the wire's tags: a pair under its key, or nothing.
pub proof fn lemma_seg(seg: ATags, k1: Chars, v: Chars, present: bool, k: Chars)
    requires
        seg == (if present { seq![(k1, v)] } else { Seq::<(Chars, Chars)>::empty() }),
    ensures
        tags_get(seg, k) == (if present && k == k1 { Some(v) } else { None::<Chars> }),
        tags_has(seg, k) == (present && k == k1),
{
    if present {
        assert(seg.len() == 1);
        assert(seg[0] == (k1, v));
        assert(seg.drop_first() =~= Seq::<(Chars, Chars)>::empty());
        assert(tags_get(Seq::<(Chars, Chars)>::empty(), k) is None);
    } else {
        assert(seg.len() == 0);
    }
}

/// What `tags_get` finds in the wire's tags: each tag under its key, and
/// nothing under `resonate:scope`.
pub proof fn lemma_tags_in(t: Tags)
    ensures
        tags_get(tags_in(t), key_delay()) == (match t.delay { Some(d) => Some(nat_chars(d as nat)), None => None::<Chars> }),
        tags_get(tags_in(t), key_external()) == (if t.external { Some(tru()) } else { None::<Chars> }),
        tags_get(tags_in(t), key_target()) == (if t.target && !t.timer { Some(worker()) } else { None::<Chars> }),
        tags_get(tags_in(t), key_timer()) == (if t.timer { Some(tru()) } else { None::<Chars> }),
        tags_get(tags_in(t), key_scope()) is None,
{
    lemma_keys_distinct();
    let delay: ATags = match t.delay {
        Some(d) => seq![(key_delay(), nat_chars(d as nat))],
        None => Seq::empty(),
    };
    let external: ATags = if t.external { seq![(key_external(), tru())] } else { Seq::empty() };
    let target: ATags = if t.target && !t.timer { seq![(key_target(), worker())] } else { Seq::empty() };
    let timer: ATags = if t.timer { seq![(key_timer(), tru())] } else { Seq::empty() };
    assert(tags_in(t) == delay + external + target + timer);
    assert(delay + external + target + timer == delay + (external + (target + timer))) by {
        assert(delay + external + target + timer =~= delay + (external + (target + timer)));
    }
    let keys = seq![key_delay(), key_external(), key_target(), key_timer(), key_scope()];
    assert forall|i: int| 0 <= i < keys.len() implies {
        let k = #[trigger] keys[i];
        tags_get(tags_in(t), k) == (if tags_has(delay, k) { tags_get(delay, k) } else if tags_has(external, k) { tags_get(external, k) } else if tags_has(target, k) { tags_get(target, k) } else { tags_get(timer, k) })
    } by {
        let k = keys[i];
        lemma_tags_get_append(delay, external + (target + timer), k);
        lemma_tags_get_append(external, target + timer, k);
        lemma_tags_get_append(target, timer, k);
    }
    assert forall|i: int| 0 <= i < keys.len() implies {
        let k = #[trigger] keys[i];
        &&& tags_get(delay, k) == (match t.delay { Some(d) => if k == key_delay() { Some(nat_chars(d as nat)) } else { None::<Chars> }, None => None::<Chars> })
        &&& tags_has(delay, k) == (t.delay is Some && k == key_delay())
        &&& tags_get(external, k) == (if t.external && k == key_external() { Some(tru()) } else { None::<Chars> })
        &&& tags_has(external, k) == (t.external && k == key_external())
        &&& tags_get(target, k) == (if t.target && !t.timer && k == key_target() { Some(worker()) } else { None::<Chars> })
        &&& tags_has(target, k) == (t.target && !t.timer && k == key_target())
        &&& tags_get(timer, k) == (if t.timer && k == key_timer() { Some(tru()) } else { None::<Chars> })
        &&& tags_has(timer, k) == (t.timer && k == key_timer())
    } by {
        let k = keys[i];
        match t.delay {
            Some(d) => { lemma_seg(delay, key_delay(), nat_chars(d as nat), true, k); },
            None => { lemma_seg(delay, key_delay(), nat_chars(0), false, k); },
        }
        lemma_seg(external, key_external(), tru(), t.external, k);
        lemma_seg(target, key_target(), worker(), t.target && !t.timer, k);
        lemma_seg(timer, key_timer(), tru(), t.timer, k);
    }
    assert(keys[0] == key_delay() && keys[1] == key_external() && keys[2] == key_target() && keys[3] == key_timer() && keys[4] == key_scope());
}

/// The wire's tags read back as the model's, where the wire did not drop a
/// sleep's target.
pub proof fn lemma_tags_roundtrip(t: Tags)
    requires
        !(t.timer && t.target),
    ensures
        tags_out(tags_in(t)) == t,
{
    lemma_tags_in(t);
    match t.delay {
        Some(d) => {
            axiom_nat_chars(d as nat);
        },
        None => {},
    }
}

/// How the kernel reads the wire's tags: the kind, the timer, the delay.
pub proof fn lemma_tags_in_kind(t: Tags, now: nat)
    ensures
        otype(tags_in(t)) == (if t.target && !t.timer { OType::Runnable } else if t.external || t.timer { OType::External } else { OType::Internal }),
        is_timer(tags_in(t)) == t.timer,
        !timer_targeted(tags_in(t)),
        tags_get(tags_in(t), key_scope()) is None,
        first_dispatch(tags_in(t), now) == (match t.delay { Some(d) => if d > now { d as nat } else { now }, None => now }),
{
    lemma_tags_in(t);
    match t.delay {
        Some(d) => {
            axiom_nat_chars(d as nat);
        },
        None => {},
    }
}

/// Awaitable in the kernel is external in the model, when no object is
/// scoped global.
pub proof fn lemma_external(p: APromise)
    requires
        tags_get(p.tags, key_scope()) != Some("global"@),
    ensures
        external_v(promise_v(p)) == p.otype().awaitable(),
        (promise_v(p).tags.target) == (p.otype() == OType::Runnable),
        promise_v(p).tags.timer == p.is_timer(),
{
}

} // verus!
