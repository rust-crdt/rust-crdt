use std::cmp::{Ordering, PartialOrd};
use std::fmt;
use std::hash::{Hash, Hasher};

use num::traits::{FromPrimitive, Num, NumAssign};
use serde::{Deserialize, Serialize};

use crate::quickcheck::{Arbitrary, Gen};

/// Dot is a version marker for a single actor
#[derive(Clone, Serialize, Deserialize)]
pub struct Dot<A, C = u64> {
    /// The actor identifier
    pub actor: A,
    /// The current version of this actor
    pub counter: C,
}

impl<A, C> Dot<A, C> {
    /// Build a Dot from an actor and counter
    pub fn new(actor: A, counter: C) -> Self {
        Self { actor, counter }
    }
}

impl<A, C: NumAssign> Dot<A, C> {
    /// Increment this dot's counter
    pub fn apply_inc(&mut self) {
        self.counter += C::one();
    }
}

impl<A: Clone, C: Clone + Num> Dot<A, C> {
    /// Generate the successor of this dot
    pub fn inc(&self) -> Self {
        Self {
            actor: self.actor.clone(),
            counter: self.counter.clone() + C::one(),
        }
    }
}
impl<A: Copy, C: Copy> Copy for Dot<A, C> {}

impl<A: PartialEq, C: PartialEq> PartialEq for Dot<A, C> {
    fn eq(&self, other: &Self) -> bool {
        self.actor == other.actor && self.counter == other.counter
    }
}

impl<A: Eq, C: Eq> Eq for Dot<A, C> {}

impl<A: Hash, C: Hash> Hash for Dot<A, C> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.actor.hash(state);
        self.counter.hash(state);
    }
}

impl<A: PartialOrd, C: PartialOrd> PartialOrd for Dot<A, C> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if self.actor == other.actor {
            self.counter.partial_cmp(&other.counter)
        } else {
            None
        }
    }
}

impl<A: fmt::Debug, C: fmt::Debug> fmt::Debug for Dot<A, C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}.{:?}", self.actor, self.counter)
    }
}

impl<A, C> From<(A, C)> for Dot<A, C> {
    fn from(dot_material: (A, C)) -> Self {
        let (actor, counter) = dot_material;
        Self { actor, counter }
    }
}

impl<A: Arbitrary + Clone, C: Arbitrary + Clone + Num + FromPrimitive + PartialOrd> Arbitrary
    for Dot<A, C>
{
    fn arbitrary<G: Gen>(g: &mut G) -> Self {
        Dot {
            actor: A::arbitrary(g),
            counter: C::arbitrary(g) % C::from_u8(50).unwrap(),
        }
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        let mut shrunk_dots = Vec::new();
        if self.counter > C::zero() {
            shrunk_dots.push(Self::new(
                self.actor.clone(),
                self.counter.clone() - C::one(),
            ));
        }
        Box::new(shrunk_dots.into_iter())
    }
}

/// An ordered dot.
/// dot's are first ordered by actor, dots from the same actor are ordered by counter.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct OrdDot<A: Ord, C = u64> {
    /// The actor who created this dot.
    pub actor: A,
    /// The current counter of this actor.
    pub counter: C,
}

impl<A: Ord, C> From<OrdDot<A, C>> for Dot<A, C> {
    fn from(OrdDot { actor, counter }: OrdDot<A, C>) -> Self {
        Self { actor, counter }
    }
}

impl<A: Ord, C> From<Dot<A, C>> for OrdDot<A, C> {
    fn from(Dot { actor, counter }: Dot<A, C>) -> Self {
        Self { actor, counter }
    }
}

/// A type for modeling a range of Dot's from one actor.
#[derive(Debug, PartialEq, Eq)]
pub struct DotRange<A, C = u64> {
    /// The actor identifier
    pub actor: A,
    /// The counter range representing the dots:
    /// `Dot::new(actor, counter_range.start) .. Dot::new(actor, counter_range.end)`
    ///
    /// Start is inclusive, end is exclusive.
    pub counter_range: core::ops::Range<C>,
}

impl<A: fmt::Debug + Ord, C: fmt::Display> fmt::Display for OrdDot<A, C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}.{}", self.actor, self.counter)
    }
}

impl<A: fmt::Debug, C: fmt::Display> fmt::Display for DotRange<A, C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{:?}.({}..{})",
            self.actor, self.counter_range.start, self.counter_range.end
        )
    }
}

impl<A: fmt::Debug, C: fmt::Debug + fmt::Display> std::error::Error for DotRange<A, C> {}

#[cfg(test)]
mod test {
    use super::*;
    use quickcheck_macros::quickcheck;

    #[quickcheck]
    fn prop_inc_increments_only_the_counter(dot: Dot<u8>) -> bool {
        dot.inc() == Dot::new(dot.actor, dot.counter + 1)
    }

    #[quickcheck]
    fn prop_partial_order(a: Dot<u8>, b: Dot<u8>) -> bool {
        let cmp_ab = a.partial_cmp(&b);
        let cmp_ba = b.partial_cmp(&a);

        match (cmp_ab, cmp_ba) {
            (None, None) => a.actor != b.actor,
            (Some(Ordering::Less), Some(Ordering::Greater)) => {
                a.actor == b.actor && a.counter < b.counter
            }
            (Some(Ordering::Greater), Some(Ordering::Less)) => {
                a.actor == b.actor && a.counter > b.counter
            }
            (Some(Ordering::Equal), Some(Ordering::Equal)) => {
                a.actor == b.actor && a.counter == b.counter
            }
            _ => false,
        }
    }

    #[quickcheck]
    fn prop_ordered_dot_is_ordered_by_actor_first(dot_a: Dot<u8>, dot_b: Dot<u8>) -> bool {
        let ord_dot_a: OrdDot<_> = dot_a.into();
        let ord_dot_b: OrdDot<_> = dot_b.into();

        match ord_dot_a.actor.cmp(&ord_dot_b.actor) {
            Ordering::Less => ord_dot_a < ord_dot_b,
            Ordering::Greater => ord_dot_a > ord_dot_b,
            Ordering::Equal => {
                ord_dot_a.counter.cmp(&ord_dot_b.counter) == ord_dot_a.cmp(&ord_dot_b)
            }
        }
    }
}
