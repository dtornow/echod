//! Local trusted realizations used by the concrete executable model.

use vstd::prelude::*;

verus! {

#[verifier::external_body]
pub fn next_cron(cron: &String, after: u64) -> (result: u64)
    ensures
        result == echod_abstract_spec::trusted::spec_next_cron(cron@, after),
        result > after,
{
    echod_cron::next_run_at(cron, after)
}

#[verifier::external_body]
pub fn expand(template: &String, id: &String, at: u64) -> (result: String)
    ensures
        result@ == echod_abstract_spec::trusted::spec_expand(template@, id@, at),
{
    template
        .replace("{{.id}}", id)
        .replace("{{.timestamp}}", &at.to_string())
}

} // verus!
