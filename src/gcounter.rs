use num_bigint::BigUint;
use serde::{Deserialize, Serialize};

use crate::{Actor, CmRDT, CvRDT, Dot, ResetRemove, VClock};

/// `GCounter` is a grow-only witnessed counter.
///
/// # Examples
///
/// ```
/// use crdts::{GCounter, CmRDT};
///
/// let mut a = GCounter::new();
/// let mut b = GCounter::new();
///
/// a.apply(a.inc("A"));
/// b.apply(b.inc("B"));
///
/// assert_eq!(a.read(), b.read());
///
/// a.apply(a.inc("A"));
/// assert!(a.read() > b.read());
/// ```
#[derive(Debug, PartialEq, Eq, Clone, Hash, Serialize, Deserialize)]
pub struct GCounter<A: Actor> {
    inner: VClock<A>,
}

impl<A: Actor> Default for GCounter<A> {
    fn default() -> Self {
        Self::new()
    }
}

impl<A: Actor> CmRDT for GCounter<A> {
    type Op = Dot<A>;

    fn apply(&mut self, op: Self::Op) {
        self.inner.apply(op)
    }
}

impl<A: Actor> CvRDT for GCounter<A> {
    fn merge(&mut self, other: Self) {
        self.inner.merge(other.inner);
    }
}

impl<A: Actor> ResetRemove<A> for GCounter<A> {
    fn reset_remove(&mut self, clock: &VClock<A>) {
        self.inner.reset_remove(&clock);
    }
}

impl<A: Actor> GCounter<A> {
    /// Produce a new `GCounter`.
    pub fn new() -> Self {
        Self {
            inner: VClock::new(),
        }
    }

    /// Generate Op to increment the counter.
    pub fn inc(&self, actor: A) -> Dot<A> {
        self.inner.inc(actor)
    }

    /// Generate Op to increment the counter by a number of steps.
    pub fn inc_many(&self, actor: A, steps: u64) -> Dot<A> {
        let steps = steps + self.inner.get(&actor);
        Dot::new(actor, steps)
    }

    /// Return the current sum of this counter.
    pub fn read(&self) -> BigUint {
        self.inner.iter().map(|dot| dot.counter).sum()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_basic_by_one() {
        let mut a = GCounter::new();
        let mut b = GCounter::new();
        a.apply(a.inc("A"));
        b.apply(b.inc("B"));

        assert_eq!(a.read(), b.read());
        assert_ne!(a, b);

        a.apply(a.inc("A"));

        assert_eq!(a.read(), b.read() + BigUint::from(1u8));
    }

    #[test]
    fn test_basic_by_many() {
        let mut a = GCounter::new();
        let mut b = GCounter::new();
        let steps = 3;

        a.apply(a.inc_many("A", steps));
        b.apply(b.inc_many("B", steps));

        assert_eq!(a.read(), b.read());
        assert_ne!(a, b);

        a.apply(a.inc_many("A", steps));

        assert_eq!(a.read(), b.read() + BigUint::from(steps));
    }
}
