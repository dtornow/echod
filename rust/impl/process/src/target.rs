//! What a step is run on: an origin's document, or a schedule's.

/// What a step is run on.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Target {
    Origin(String),
    Schedule(String),
}

impl Target {
    /// The name the keys and the node's decisions go by: the origin, or
    /// `sched:<id>`.
    pub fn name(&self) -> String {
        match self {
            Target::Origin(o) => o.clone(),
            Target::Schedule(id) => format!("sched:{id}"),
        }
    }

    /// The target a timer key's name (`origin` or `sched:<id>`) says.
    pub fn of_name(name: &str) -> Target {
        match name.strip_prefix("sched:") {
            Some(id) => Target::Schedule(id.to_string()),
            None => Target::Origin(name.to_string()),
        }
    }
}
