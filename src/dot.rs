use std::cmp::{Ordering, PartialOrd};
use std::fmt;
use std::hash::{Hash, Hasher};

use serde::{Deserialize, Serialize};

use crate::quickcheck::{Arbitrary, Gen};

/// Dot is a version marker for a single actor
#[derive(Clone, Serialize, Deserialize)]
pub struct Dot<A> {
    /// The actor identifier
    pub actor: A,
    /// The current version of this actor
    pub counter: u64,
}

impl<A> Dot<A> {
    /// Build a Dot from an actor and counter
    pub fn new(actor: A, counter: u64) -> Self {
        Self { actor, counter }
    }

    /// Increment this dot's counter
    pub fn apply_inc(&mut self) {
        self.counter += 1;
    }
}

impl<A: Clone> Dot<A> {
    /// Generate the successor of this dot
    pub fn inc(&self) -> Self {
        Self {
            actor: self.actor.clone(),
            counter: self.counter + 1,
        }
    }
}
impl<A: Copy> Copy for Dot<A> {}

impl<A: PartialEq> PartialEq for Dot<A> {
    fn eq(&self, other: &Self) -> bool {
        self.actor == other.actor && self.counter == other.counter
    }
}

impl<A: Eq> Eq for Dot<A> {}

impl<A: Hash> Hash for Dot<A> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.actor.hash(state);
        self.counter.hash(state);
    }
}

impl<A: PartialOrd> PartialOrd for Dot<A> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if self.actor == other.actor {
            self.counter.partial_cmp(&other.counter)
        } else {
            None
        }
    }
}

impl<A: fmt::Debug> fmt::Debug for Dot<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}.{:?}", self.actor, self.counter)
    }
}

impl<A> From<(A, u64)> for Dot<A> {
    fn from(dot_material: (A, u64)) -> Self {
        let (actor, counter) = dot_material;
        Self { actor, counter }
    }
}

impl<A: Arbitrary + Clone> Arbitrary for Dot<A> {
    fn arbitrary<G: Gen>(g: &mut G) -> Self {
        Dot {
            actor: A::arbitrary(g),
            counter: u64::arbitrary(g) % 50,
        }
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        let mut shrunk_dots = Vec::new();
        if self.counter > 0 {
            shrunk_dots.push(Self::new(self.actor.clone(), self.counter - 1));
        }
        Box::new(shrunk_dots.into_iter())
    }
}

/// A type for modeling a range of Dot's from one actor.
#[derive(Debug, PartialEq, Eq)]
pub struct DotRange<A> {
    /// The actor identifier
    pub actor: A,
    /// The counter range representing the dots:
    /// `Dot::new(actor, counter_range.start) .. Dot::new(actor, counter_range.end)`
    ///
    /// Start is inclusive, end is exclusive.
    pub counter_range: core::ops::Range<u64>,
}

impl<A: fmt::Debug> fmt::Display for DotRange<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{:?}.({}..{})",
            self.actor, self.counter_range.start, self.counter_range.end
        )
    }
}

impl<A: fmt::Debug> std::error::Error for DotRange<A> {}

#[cfg(test)]
mod test {
    use super::*;
    use quickcheck::quickcheck;

    quickcheck! {
        fn inc_increments_only_the_counter(dot: Dot<u8>) -> bool {
            dot.inc() == Dot::new(dot.actor, dot.counter + 1)
        }

        fn test_partial_order(a: Dot<u8>, b: Dot<u8>) -> bool {
            let cmp_ab = a.partial_cmp(&b);
            let cmp_ba = b.partial_cmp(&a);

            match (cmp_ab, cmp_ba) {
                (None, None) => a.actor != b.actor,
                (Some(Ordering::Less), Some(Ordering::Greater)) => a.actor == b.actor && a.counter < b.counter,
                (Some(Ordering::Greater), Some(Ordering::Less)) => a.actor == b.actor && a.counter > b.counter,
                (Some(Ordering::Equal), Some(Ordering::Equal)) => a.actor == b.actor && a.counter == b.counter,
                _ => false
            }
        }
    }
}
