use num::bigint::BigInt;
use serde::{Deserialize, Serialize};
use std::fmt::{Debug, Display};

use num::{bigint::ToBigUint, traits::Num};

use crate::traits::{CmRDT, CvRDT, ResetRemove};
use crate::{Dot, GCounter, VClock};

/// `PNCounter` allows the counter to be both incremented and decremented
/// by representing the increments (P) and the decrements (N) in separate
/// internal G-Counters.
///
/// Merge is implemented by merging the internal P and N counters.
/// The value of the counter is P minus N.
///
/// # Examples
///
/// ```
/// use crdts::{PNCounter, CmRDT};
///
/// let mut a = PNCounter::new();
/// a.apply(a.inc("A"));
/// a.apply(a.inc("A"));
/// a.apply(a.dec("A"));
/// a.apply(a.inc("A"));
///
/// assert_eq!(a.read(), 2.into());
/// ```
#[derive(Debug, PartialEq, Eq, Clone, Hash, Serialize, Deserialize)]
pub struct PNCounter<A: Ord, C = u64> {
    p: GCounter<A, C>,
    n: GCounter<A, C>,
}

/// The Direction of an Op.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub enum Dir {
    /// signals that the op increments the counter
    Pos,
    /// signals that the op decrements the counter
    Neg,
}

/// An Op which is produced through from mutating the counter
/// Ship these ops to other replicas to have them sync up.
#[derive(Debug, Copy, Clone, Serialize, Deserialize)]
pub struct Op<A: Ord, C = u64> {
    /// The witnessing dot for this op
    pub dot: Dot<A, C>,
    /// the direction to move the counter
    pub dir: Dir,
}

impl<A: Ord, C> Default for PNCounter<A, C> {
    fn default() -> Self {
        Self {
            p: Default::default(),
            n: Default::default(),
        }
    }
}

impl<A: Ord + Clone + Debug, C: Ord + Clone + Debug + Display + Num> CmRDT for PNCounter<A, C> {
    type Op = Op<A, C>;
    type Validation = <GCounter<A, C> as CmRDT>::Validation;

    fn validate_op(&self, op: &Self::Op) -> Result<(), Self::Validation> {
        match op {
            Op { dot, dir: Dir::Pos } => self.p.validate_op(dot),
            Op { dot, dir: Dir::Neg } => self.n.validate_op(dot),
        }
    }

    fn apply(&mut self, op: Self::Op) {
        match op {
            Op { dot, dir: Dir::Pos } => self.p.apply(dot),
            Op { dot, dir: Dir::Neg } => self.n.apply(dot),
        }
    }
}

impl<A: Ord + Clone + Debug, C: Ord + Clone + Debug + Display + Num> CvRDT for PNCounter<A, C> {
    type Validation = <GCounter<A, C> as CvRDT>::Validation;

    fn validate_merge(&self, other: &Self) -> Result<(), Self::Validation> {
        self.p.validate_merge(&other.p)?;
        self.n.validate_merge(&other.n)
    }

    fn merge(&mut self, other: Self) {
        self.p.merge(other.p);
        self.n.merge(other.n);
    }
}

impl<A: Ord, C: Ord + Clone + Num> ResetRemove<A, C> for PNCounter<A, C> {
    fn reset_remove(&mut self, clock: &VClock<A, C>) {
        self.p.reset_remove(&clock);
        self.n.reset_remove(&clock);
    }
}

impl<A: Ord + Clone, C: Ord + Clone + Num> PNCounter<A, C> {
    /// Produce a new `PNCounter`.
    pub fn new() -> Self {
        Default::default()
    }

    /// Return a view of the inner vector clocks.
    pub fn inner(&self) -> (&VClock<A, C>, &VClock<A, C>) {
        (self.p.inner(), self.n.inner())
    }

    /// Generate an Op to increment the counter.
    pub fn inc(&self, actor: A) -> Op<A, C> {
        Op {
            dot: self.p.inc(actor),
            dir: Dir::Pos,
        }
    }

    /// Generate an Op to increment the counter.
    pub fn dec(&self, actor: A) -> Op<A, C> {
        Op {
            dot: self.n.inc(actor),
            dir: Dir::Neg,
        }
    }

    /// Generate an Op to increment the counter by a number of steps.
    pub fn inc_many(&self, actor: A, steps: C) -> Op<A, C> {
        Op {
            dot: self.p.inc_many(actor, steps),
            dir: Dir::Pos,
        }
    }

    /// Generate an Op to decrement the counter by a number of steps.
    pub fn dec_many(&self, actor: A, steps: C) -> Op<A, C> {
        Op {
            dot: self.n.inc_many(actor, steps),
            dir: Dir::Neg,
        }
    }

    /// Return the current value of this counter (P-N).
    pub fn read(&self) -> BigInt
    where
        C: ToBigUint,
    {
        let p: BigInt = self.p.read().into();
        let n: BigInt = self.n.read().into();
        p - n
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use std::collections::BTreeSet;

    use quickcheck::quickcheck;

    const ACTOR_MAX: u8 = 11;

    fn build_op(prims: (u8, u64, bool)) -> Op<u8> {
        let (actor, counter, dir_choice) = prims;
        Op {
            dot: Dot { actor, counter },
            dir: if dir_choice { Dir::Pos } else { Dir::Neg },
        }
    }

    quickcheck! {
        fn prop_merge_converges(op_prims: Vec<(u8, u64, bool)>) -> bool {
            let ops: Vec<Op<u8>> = op_prims.into_iter().map(build_op).collect();

            let mut results = BTreeSet::new();

            // Permute the interleaving of operations should converge.
            // Largely taken directly from orswot
            for i in 2..ACTOR_MAX {
                let mut witnesses: Vec<PNCounter<u8>> =
                    (0..i).map(|_| PNCounter::new()).collect();
                for op in ops.iter() {
                    let index = op.dot.actor as usize % i as usize;
                    let witness = &mut witnesses[index];
                    witness.apply(op.clone());
                }
                let mut merged = PNCounter::new();
                for witness in witnesses.iter() {
                    merged.merge(witness.clone());
                }

                results.insert(merged.read());
                if results.len() > 1 {
                    println!("opvec: {:?}", ops);
                    println!("results: {:?}", results);
                    println!("witnesses: {:?}", &witnesses);
                    println!("merged: {:?}", merged);
                }
            }
            results.len() == 1
        }
    }

    #[test]
    fn test_basic_by_one() {
        let mut a = PNCounter::<&str>::new();
        assert_eq!(a.read(), 0.into());

        a.apply(a.inc("A"));
        assert_eq!(a.read(), 1.into());

        a.apply(a.inc("A"));
        assert_eq!(a.read(), 2.into());

        a.apply(a.dec("A"));
        assert_eq!(a.read(), 1.into());

        a.apply(a.inc("A"));
        assert_eq!(a.read(), 2.into());
    }

    #[test]
    fn test_basic_by_many() {
        let mut a = PNCounter::new();
        assert_eq!(a.read(), 0.into());

        let steps = 3;

        a.apply(a.inc_many("A", steps));
        assert_eq!(a.read(), steps.into());

        a.apply(a.inc_many("A", steps));
        assert_eq!(a.read(), (2 * steps).into());

        a.apply(a.dec_many("A", steps));
        assert_eq!(a.read(), steps.into());

        a.apply(a.inc_many("A", 1));
        assert_eq!(a.read(), (1 + steps).into());
    }
}
