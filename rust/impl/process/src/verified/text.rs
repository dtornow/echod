//! Strings built in the process: a literal, two or three pieces joined, a
//! copy, a prefix taken off, a number written out. The joins are proved;
//! `strip_prefix` and the decimal text wrap the standard library and state
//! what it does.

use vstd::prelude::*;

verus! {

/// A copy of a string.
pub fn copy_string(s: &String) -> (r: String)
    ensures
        r == *s,
{
    s.clone()
}

/// `str::strip_prefix`, stated: `Some(rest)` exactly when `s` is `p` then
/// `rest`.
#[verifier::external_body]
pub fn strip_prefix(s: &str, p: &str) -> (r: Option<String>)
    ensures
        match r {
            Some(rest) => s@ == p@ + rest@,
            None => !(s@.len() >= p@.len() && s@.subrange(0, p@.len() as int) == p@),
        },
{
    s.strip_prefix(p).map(|rest| rest.to_string())
}

/// Does `s` start with `p`?
pub open spec fn spec_starts_with(s: Seq<char>, p: Seq<char>) -> bool {
    s.len() >= p.len() && s.subrange(0, p.len() as int) == p
}

/// `str::starts_with`, stated.
#[verifier::external_body]
pub fn starts_with(s: &str, p: &str) -> (r: bool)
    ensures
        r == spec_starts_with(s@, p@),
{
    s.starts_with(p)
}

/// The decimal text of a number. What the standard library writes.
pub uninterp spec fn spec_u64_text(n: u64) -> Seq<char>;

/// `n.to_string()`.
#[verifier::external_body]
pub fn u64_text(n: u64) -> (r: String)
    ensures
        r@ == spec_u64_text(n),
{
    n.to_string()
}

/// A literal as an owned string.
pub fn text(lit: &str) -> (r: String)
    ensures
        r@ == lit@,
{
    let mut s = String::new();
    s.push_str(lit);
    proof {
        assert(s@ =~= lit@);
    }
    s
}

/// `a` then `b`.
pub fn concat(a: &str, b: &str) -> (r: String)
    ensures
        r@ == a@ + b@,
{
    let mut s = String::new();
    s.push_str(a);
    s.push_str(b);
    proof {
        assert(s@ =~= a@ + b@);
    }
    s
}

/// `a`, `b`, then `c`.
pub fn concat3(a: &str, b: &str, c: &str) -> (r: String)
    ensures
        r@ == a@ + b@ + c@,
{
    let mut s = String::new();
    s.push_str(a);
    s.push_str(b);
    s.push_str(c);
    proof {
        assert(s@ =~= a@ + b@ + c@);
    }
    s
}

} // verus!
