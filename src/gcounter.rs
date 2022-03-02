use core::convert::Infallible;
use core::fmt::{Debug, Display};

use num::{
    bigint::{BigUint, ToBigUint},
    traits::Num,
};
use serde::{Deserialize, Serialize};

use crate::{CmRDT, CvRDT, Dot, ResetRemove, VClock};

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
pub struct GCounter<A: Ord, C = u64> {
    inner: VClock<A, C>,
}

impl<A: Ord, C> Default for GCounter<A, C> {
    fn default() -> Self {
        Self {
            inner: Default::default(),
        }
    }
}

impl<A: Ord + Clone + Debug, C: Ord + Clone + Debug + Display + Num> CmRDT for GCounter<A, C> {
    type Op = Dot<A, C>;
    type Validation = Infallible;

    fn validate_op(&self, _op: &Self::Op) -> Result<(), Self::Validation> {
        Ok(())
    }

    fn apply(&mut self, op: Self::Op) {
        self.inner.apply(op)
    }
}

impl<A: Ord + Clone + Debug, C: Ord + Clone + Debug + Display + Num> CvRDT for GCounter<A, C> {
    type Validation = Infallible;

    fn validate_merge(&self, _other: &Self) -> Result<(), Self::Validation> {
        Ok(())
    }

    fn merge(&mut self, other: Self) {
        self.inner.merge(other.inner);
    }
}

impl<A: Ord, C: Ord + Clone + Num> ResetRemove<A, C> for GCounter<A, C> {
    fn reset_remove(&mut self, clock: &VClock<A, C>) {
        self.inner.reset_remove(&clock);
    }
}

impl<A: Ord + Clone, C: Ord + Clone + Num> GCounter<A, C> {
    /// Produce a new `GCounter`.
    pub fn new() -> Self {
        Default::default()
    }

    /// Return a view of the inner vector clock.
    pub fn inner(&self) -> &VClock<A, C> {
        &self.inner
    }

    /// Generate Op to increment the counter.
    pub fn inc(&self, actor: A) -> Dot<A, C> {
        self.inner.inc(actor)
    }

    /// Generate Op to increment the counter by a number of steps.
    pub fn inc_many(&self, actor: A, steps: C) -> Dot<A, C> {
        let steps = steps + self.inner.get(&actor);
        Dot::new(actor, steps)
    }

    /// Return the current sum of this counter.
    pub fn read(&self) -> BigUint
    where
        C: ToBigUint,
    {
        self.inner
            .iter()
            .map(|dot| dot.counter.to_biguint().unwrap())
            .sum()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_basic_by_one() {
        let mut a = GCounter::<&str>::new();
        let mut b = GCounter::<&str>::new();
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
        let steps = 3usize;

        a.apply(a.inc_many("A", steps));
        b.apply(b.inc_many("B", steps));

        assert_eq!(a.read(), b.read());
        assert_ne!(a, b);

        a.apply(a.inc_many("A", steps));

        assert_eq!(a.read(), b.read() + BigUint::from(steps));
    }
}
