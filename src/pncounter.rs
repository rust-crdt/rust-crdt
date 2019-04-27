use num_bigint::BigInt;
use serde::{Deserialize, Serialize};

use crate::gcounter::GCounter;
use crate::traits::{Causal, CmRDT, CvRDT};
use crate::vclock::{Actor, Dot, VClock};

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
pub struct PNCounter<A: Actor> {
    p: GCounter<A>,
    n: GCounter<A>,
}

/// The Direction of an Op.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Dir {
    /// signals that the op increments the counter
    Pos,
    /// signals that the op decrements the counter
    Neg,
}

/// An Op which is produced through from mutating the counter
/// Ship these ops to other replicas to have them sync up.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Op<A: Actor> {
    /// The witnessing dot for this op
    pub dot: Dot<A>,
    /// the direction to move the counter
    pub dir: Dir,
}

impl<A: Actor> Default for PNCounter<A> {
    fn default() -> Self {
        PNCounter::new()
    }
}

impl<A: Actor> CmRDT for PNCounter<A> {
    type Op = Op<A>;

    fn apply(&mut self, op: Self::Op) {
        match op {
            Op { dot, dir: Dir::Pos } => self.p.apply(dot),
            Op { dot, dir: Dir::Neg } => self.n.apply(dot),
        }
    }
}

impl<A: Actor> CvRDT for PNCounter<A> {
    fn merge(&mut self, other: Self) {
        self.p.merge(other.p);
        self.n.merge(other.n);
    }
}

impl<A: Actor> Causal<A> for PNCounter<A> {
    fn forget(&mut self, clock: &VClock<A>) {
        self.p.forget(&clock);
        self.n.forget(&clock);
    }
}

impl<A: Actor> PNCounter<A> {
    /// Produce a new `PNCounter`.
    pub fn new() -> Self {
        PNCounter {
            p: GCounter::new(),
            n: GCounter::new(),
        }
    }

    /// Generate an Op to increment the counter.
    pub fn inc(&self, actor: A) -> Op<A> {
        Op {
            dot: self.p.inc(actor),
            dir: Dir::Pos,
        }
    }

    /// Generate an Op to increment the counter.
    pub fn dec(&self, actor: A) -> Op<A> {
        Op {
            dot: self.n.inc(actor),
            dir: Dir::Neg,
        }
    }

    /// Return the current value of this counter (P-N).
    pub fn read(&self) -> BigInt {
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
    fn test_basic() {
        let mut a = PNCounter::new();
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

}
