//! A checker that, when dropped, backs everything it accepted with a
//! certificate that `echod_rover::certify` replays.

use std::ops::{Deref, DerefMut};

use echod_rover::{Checker, Engine};

pub struct Certified<S: Engine>(pub Checker<S>);

impl<S: Engine> Deref for Certified<S> {
    type Target = Checker<S>;
    fn deref(&self) -> &Checker<S> {
        &self.0
    }
}

impl<S: Engine> DerefMut for Certified<S> {
    fn deref_mut(&mut self) -> &mut Checker<S> {
        &mut self.0
    }
}

impl<S: Engine> Drop for Certified<S> {
    fn drop(&mut self) {
        if !std::thread::panicking() {
            if let Err(v) = self.0.certified() {
                panic!("no certificate for an accepted history: {v}");
            }
        }
    }
}
