//! Trusted runtime realizations of copy, address, cron, and expansion.

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports))]

use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::axioms::{
    spec_address_valid, spec_cron_valid, spec_expand, spec_has_colon as abstract_spec_has_colon,
    spec_next_cron,
};

verus! {
/// A derived `Clone` is a copy.
#[verifier::external_body]
pub fn copy<T: Clone>(t: &T) -> (r: T)
    ensures
        r == *t,
{
    t.clone()
}

/// Any absolute URL: a scheme, a colon, and a non-empty rest with no whitespace.
#[verifier::external_body]
pub fn address_valid(addr: &String) -> (r: bool)
    ensures
        r == spec_address_valid(addr@),
{
    let addr = addr.trim();
    let Some((scheme, rest)) = addr.split_once(':') else { return false };
    let mut chars = scheme.chars();
    chars.next().is_some_and(|c| c.is_ascii_alphabetic())
        && chars.all(|c| c.is_ascii_alphanumeric() || "+.-".contains(c))
        && !rest.is_empty()
        && !rest.chars().any(char::is_whitespace)
}

#[verifier::external_body]
pub fn has_colon(id: &String) -> (r: bool)
    ensures
        r == abstract_spec_has_colon(id@),
{
    id.contains(':')
}

/// A cron expression the reference server's engine accepts: five fields, or
/// six to seven with seconds (and a year).
#[verifier::external_body]
pub fn cron_valid(cron: &String) -> (r: bool)
    ensures
        r == spec_cron_valid(cron@),
{
    echod_cron::valid(cron)
}

/// Lean's `nextCron`: the first instant strictly after `after` the cron names,
/// as the reference server computes it (whole seconds, in milliseconds).
#[verifier::external_body]
pub fn next_cron(cron: &String, after: u64) -> (r: u64)
    ensures
        r == spec_next_cron(cron@, after),
        r > after,
{
    echod_cron::next_run_at(cron, after)
}

/// Lean's `expand`: the schedule's promise id template with `{{.id}}` the
/// schedule's id and `{{.timestamp}}` the occurrence's instant.
#[verifier::external_body]
pub fn expand(template: &String, id: &String, at: u64) -> (r: String)
    ensures
        r@ == spec_expand(template@, id@, at),
{
    template.replace("{{.id}}", id).replace("{{.timestamp}}", &at.to_string())
}


} // verus!
