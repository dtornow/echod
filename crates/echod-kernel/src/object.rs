//! One object at an instant: projection, the task's view of its promise, and
//! the small edits every handler makes. Spec first, exec after, each exec
//! function proven equal to its spec.

use vstd::prelude::*;

use crate::tags::{is_timer, otype, OType};
use crate::types::*;

verus! {

// ---------------------------------------------------------------------------
// Specification
// ---------------------------------------------------------------------------

impl APromise {
    pub open spec fn is_timer(self) -> bool {
        is_timer(self.tags)
    }

    pub open spec fn otype(self) -> OType {
        otype(self.tags)
    }

    /// `PromiseObject.project`: a pending promise past its deadline is settled
    /// by its deadline — resolved if it is a timer, timed out otherwise.
    pub open spec fn project_promise(self, now: nat) -> APromise {
        if self.state == PromiseState::Pending && self.timeout_at <= now {
            if self.is_timer() {
                APromise { state: PromiseState::Resolved, settled_at: Some(self.timeout_at), ..self }
            } else {
                APromise { state: PromiseState::RejectedTimedout, settled_at: Some(self.timeout_at), ..self }
            }
        } else {
            self
        }
    }

    /// `Object.project`: the promise projected, and the task viewed through it.
    pub open spec fn project(self, now: nat) -> APromise {
        let p = self.project_promise(now);
        APromise {
            task: match self.task {
                Some(t) => Some(t.view_through(p)),
                None => None,
            },
            ..p
        }
    }

    pub open spec fn add_callback(self, awaiter: Seq<char>) -> APromise {
        if self.callbacks.contains(awaiter) {
            self
        } else {
            APromise { callbacks: self.callbacks.push(awaiter), ..self }
        }
    }

    pub open spec fn add_listener(self, address: Seq<char>) -> APromise {
        if self.listeners.contains(address) {
            self
        } else {
            APromise { listeners: self.listeners.push(address), ..self }
        }
    }
}

impl ATask {
    /// `TaskObject.fulfill`.
    pub open spec fn fulfill(self) -> ATask {
        ATask {
            state: TaskState::Fulfilled,
            pid: None,
            ttl: None,
            lease_timeout_at: None,
            retry_timeout_at: None,
            resumes: Seq::empty(),
            ..self
        }
    }

    /// `TaskObject.view`: a task whose promise is settled is fulfilled.
    pub open spec fn view_through(self, p: APromise) -> ATask {
        if p.state != PromiseState::Pending && self.state != TaskState::Fulfilled {
            self.fulfill()
        } else {
            self
        }
    }
}

// ---------------------------------------------------------------------------
// Executable
// ---------------------------------------------------------------------------

pub fn seq_contains(v: &Vec<String>, x: &String) -> (r: bool)
    ensures r == v.deep_view().contains(x@),
{
    let ghost s = v.deep_view();
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v@.len(),
            s == v.deep_view(),
            forall|j: int| 0 <= j < i ==> s[j] != x@,
        decreases v@.len() - i,
    {
        if v[i] == *x {
            assert(s[i as int] == x@);
            return true;
        }
        i += 1;
    }
    false
}

/// `v` with `x` appended; the deep view is the view pushed.
pub fn push_string(v: &mut Vec<String>, x: String)
    ensures final(v).deep_view() == old(v).deep_view().push(x@),
{
    let ghost s = old(v).deep_view();
    v.push(x);
    assert(v.deep_view() =~= s.push(x@));
}

/// `s` without every occurrence of `x`, in order.
pub open spec fn without(s: Seq<Seq<char>>, x: Seq<char>) -> Seq<Seq<char>>
    decreases s.len(),
{
    if s.len() == 0 {
        Seq::empty()
    } else if s.last() == x {
        without(s.drop_last(), x)
    } else {
        without(s.drop_last(), x).push(s.last())
    }
}

/// What `without` keeps: everything but `x`.
pub proof fn lemma_without_contains(s: Seq<Seq<char>>, x: Seq<char>, y: Seq<char>)
    ensures
        without(s, x).contains(y) <==> (s.contains(y) && y != x),
    decreases s.len(),
{
    if s.len() == 0 {
    } else {
        let init = s.drop_last();
        lemma_without_contains(init, x, y);
        assert(s.contains(y) <==> (init.contains(y) || s.last() == y)) by {
            if s.contains(y) {
                let i = choose|i: int| 0 <= i < s.len() && s[i] == y;
                if i < s.len() - 1 {
                    assert(init[i] == y);
                }
            }
            if init.contains(y) {
                let i = choose|i: int| 0 <= i < init.len() && init[i] == y;
                assert(s[i] == y);
            }
            if s.last() == y {
                assert(s[s.len() - 1] == y);
            }
        }
        if s.last() != x {
            let w = without(init, x);
            assert(w.push(s.last()).contains(y) <==> (w.contains(y) || s.last() == y)) by {
                if w.push(s.last()).contains(y) {
                    let i = choose|i: int| 0 <= i < w.push(s.last()).len() && w.push(s.last())[i] == y;
                    if i < w.len() {
                        assert(w[i] == y);
                    }
                }
                if w.contains(y) {
                    let i = choose|i: int| 0 <= i < w.len() && w[i] == y;
                    assert(w.push(s.last())[i] == y);
                }
                if s.last() == y {
                    assert(w.push(s.last())[w.len() as int] == y);
                }
            }
        }
    }
}

/// `without` keeps a duplicate-free sequence duplicate-free.
pub proof fn lemma_without_no_dups(s: Seq<Seq<char>>, x: Seq<char>)
    requires
        crate::properties::no_dups(s),
    ensures
        crate::properties::no_dups(without(s, x)),
    decreases s.len(),
{
    if s.len() == 0 {
    } else {
        let init = s.drop_last();
        assert(crate::properties::no_dups(init)) by {
            assert forall|i: int, j: int| 0 <= i < init.len() && 0 <= j < init.len() && init[i] == init[j]
                implies i == j by {
                assert(s[i] == init[i]);
                assert(s[j] == init[j]);
            }
        }
        lemma_without_no_dups(init, x);
        if s.last() != x {
            let w = without(init, x);
            assert(!w.contains(s.last())) by {
                lemma_without_contains(init, x, s.last());
                if init.contains(s.last()) {
                    let i = choose|i: int| 0 <= i < init.len() && init[i] == s.last();
                    assert(s[i] == s[s.len() - 1]);
                }
            }
            assert forall|i: int, j: int| 0 <= i < w.push(s.last()).len() && 0 <= j < w.push(s.last()).len()
                && w.push(s.last())[i] == w.push(s.last())[j] implies i == j by {
                if i < w.len() && j < w.len() {
                } else if i < w.len() {
                    assert(w[i] == s.last());
                } else if j < w.len() {
                    assert(w[j] == s.last());
                }
            }
        }
    }
}

/// `v` without every occurrence of `x`.
pub fn remove_string(v: &Vec<String>, x: &String) -> (r: Vec<String>)
    ensures r.deep_view() == without(v.deep_view(), x@),
{
    let ghost s = v.deep_view();
    let mut r: Vec<String> = Vec::new();
    let mut i: usize = 0;
    assert(r.deep_view() =~= Seq::<Seq<char>>::empty());
    assert(s.take(0) =~= Seq::<Seq<char>>::empty());
    while i < v.len()
        invariant
            i <= v@.len(),
            s == v.deep_view(),
            r.deep_view() == without(s.take(i as int), x@),
        decreases v@.len() - i,
    {
        let ghost before = r.deep_view();
        assert(s.take(i as int + 1) =~= s.take(i as int).push(s[i as int]));
        assert(s.take(i as int).push(s[i as int]).drop_last() =~= s.take(i as int));
        if v[i] != *x {
            assert(s[i as int] != x@);
            let y = v[i].clone();
            r.push(y);
            assert(r.deep_view() =~= before.push(s[i as int]));
        } else {
            assert(s[i as int] == x@);
        }
        i += 1;
    }
    assert(s.take(v@.len() as int) =~= s);
    r
}

impl Promise {
    pub fn is_timer(&self) -> (r: bool)
        ensures r == self@.is_timer(),
    {
        crate::tags::exec_is_timer(&self.tags)
    }

    pub fn otype(&self) -> (r: OType)
        ensures r == self@.otype(),
    {
        crate::tags::exec_otype(&self.tags)
    }

    /// `Object.project`, in place.
    pub fn project(&mut self, now: u64)
        ensures final(self)@ == old(self)@.project(now as nat),
    {
        if self.state == PromiseState::Pending && self.timeout_at <= now {
            if self.is_timer() {
                self.state = PromiseState::Resolved;
            } else {
                self.state = PromiseState::RejectedTimedout;
            }
            self.settled_at = Some(self.timeout_at);
        }
        let settled = self.state != PromiseState::Pending;
        match &mut self.task {
            Some(t) => {
                if settled && t.state != TaskState::Fulfilled {
                    t.fulfill();
                }
            }
            None => {}
        }
    }

    pub fn add_callback(&mut self, awaiter: &String)
        ensures final(self)@ == old(self)@.add_callback(awaiter@),
    {
        if !seq_contains(&self.callbacks, awaiter) {
            push_string(&mut self.callbacks, awaiter.clone());
        }
    }

    pub fn add_listener(&mut self, address: &String)
        ensures final(self)@ == old(self)@.add_listener(address@),
    {
        if !seq_contains(&self.listeners, address) {
            push_string(&mut self.listeners, address.clone());
        }
    }

    /// `toRecord`.
    pub fn to_record(&self) -> (r: PromiseRecord)
        ensures r@ == self@.to_record(),
    {
        PromiseRecord {
            id: self.id.clone(),
            state: self.state,
            param: self.param.dup(),
            value: self.value.dup(),
            tags: clone_tags(&self.tags),
            timeout_at: self.timeout_at,
            created_at: self.created_at,
            settled_at: self.settled_at,
        }
    }
}

impl Task {
    pub fn fulfill(&mut self)
        ensures final(self)@ == old(self)@.fulfill(),
    {
        self.state = TaskState::Fulfilled;
        self.pid = None;
        self.ttl = None;
        self.lease_timeout_at = None;
        self.retry_timeout_at = None;
        self.resumes = Vec::new();
        assert(self.resumes.deep_view() =~= Seq::<Seq<char>>::empty());
    }

    pub fn to_record(&self, id: &String) -> (r: TaskRecord)
        ensures r@ == self@.to_record(id@),
    {
        TaskRecord {
            id: id.clone(),
            state: self.state,
            version: self.version,
            resumes: self.resumes.len() as u64,
            ttl: self.ttl,
            pid: match &self.pid {
                Some(p) => Some(p.clone()),
                None => None,
            },
        }
    }
}

pub fn clone_tags(t: &Tags) -> (r: Tags)
    ensures r.deep_view() == t.deep_view(),
{
    let ghost s = t.deep_view();
    let mut r: Tags = Vec::new();
    let mut i: usize = 0;
    assert(r.deep_view() =~= s.take(0));
    while i < t.len()
        invariant
            i <= t@.len(),
            s == t.deep_view(),
            r.deep_view() == s.take(i as int),
        decreases t@.len() - i,
    {
        let ghost before = r.deep_view();
        r.push((t[i].0.clone(), t[i].1.clone()));
        assert(r.deep_view() =~= before.push(s[i as int]));
        assert(s.take(i as int + 1) =~= s.take(i as int).push(s[i as int]));
        i += 1;
    }
    assert(s.take(t@.len() as int) =~= s);
    r
}

impl Value {
    pub fn dup(&self) -> (r: Value)
        ensures r@ == self@,
    {
        Value {
            headers: clone_tags(&self.headers),
            data: match &self.data {
                Some(d) => Some(d.clone()),
                None => None,
            },
        }
    }
}

} // verus!
