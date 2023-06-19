//! This module contains a generic Vector Clock implementation.
//!
//! # Examples
//!
//! ```
//! use crdts::{Dot, VClock, CmRDT};
//!
//! let mut a = VClock::new();
//! let mut b = VClock::new();
//! a.apply(Dot::new("A", 2));
//! b.apply(Dot::new("A", 1));
//! assert!(a > b);
//! ```

use core::cmp::{self, Ordering};
use core::convert::Infallible;
use core::fmt::{self, Debug, Display};
use core::mem;
use std::collections::{btree_map, BTreeMap};

use serde::{Deserialize, Serialize};

use crate::{CmRDT, CvRDT, Dot, DotRange, ResetRemove};

/// A `VClock` is a standard vector clock.
/// It contains a set of "actors" and associated counters.
/// When a particular actor witnesses a mutation, their associated
/// counter in a `VClock` is incremented. `VClock` is typically used
/// as metadata for associated application data, rather than as the
/// container for application data. `VClock` just tracks causality.
/// It can tell you if something causally descends something else,
/// or if different replicas are "concurrent" (were mutated in
/// isolation, and need to be resolved externally).
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct VClock<A: Ord> {
    /// dots is the mapping from actors to their associated counters
    pub dots: BTreeMap<A, u64>,
}

impl<A: Ord> Default for VClock<A> {
    fn default() -> Self {
        Self {
            dots: BTreeMap::new(),
        }
    }
}

impl<A: Ord> PartialOrd for VClock<A> {
    fn partial_cmp(&self, other: &VClock<A>) -> Option<Ordering> {
        // This algorithm is pretty naive, I think there's a way to
        // just track if the ordering changes as we iterate over the
        // active dots zipped by actor.
        // ie. it's None if the ordering changes from Less to Greator
        //     or vice-versa.

        if self == other {
            Some(Ordering::Equal)
        } else if other.dots.iter().all(|(w, c)| self.get(w) >= *c) {
            Some(Ordering::Greater)
        } else if self.dots.iter().all(|(w, c)| other.get(w) >= *c) {
            Some(Ordering::Less)
        } else {
            None
        }
    }
}

impl<A: Ord + Display> Display for VClock<A> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "<")?;
        for (i, (actor, count)) in self.dots.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}:{}", actor, count)?;
        }
        write!(f, ">")
    }
}

impl<A: Ord> ResetRemove<A> for VClock<A> {
    /// Forget any actors that have smaller counts than the
    /// count in the given vclock
    fn reset_remove(&mut self, other: &Self) {
        for Dot { actor, counter } in other.iter() {
            if counter >= self.get(actor) {
                self.dots.remove(actor);
            }
        }
    }
}

impl<A: Ord + Clone + Debug> CmRDT for VClock<A> {
    type Op = Dot<A>;
    type Validation = DotRange<A>;

    fn validate_op(&self, dot: &Self::Op) -> Result<(), Self::Validation> {
        let next_counter = self.get(&dot.actor) + 1;
        if dot.counter > next_counter {
            Err(DotRange {
                actor: dot.actor.clone(),
                counter_range: next_counter..dot.counter,
            })
        } else {
            Ok(())
        }
    }

    /// Monotonically adds the given actor version to
    /// this VClock.
    ///
    /// # Examples
    /// ```
    /// use crdts::{VClock, Dot, CmRDT};
    /// let mut v = VClock::new();
    ///
    /// v.apply(Dot::new("A", 2));
    ///
    /// // now all dots applied to `v` from actor `A` where
    /// // the counter is not bigger than 2 are nops.
    /// v.apply(Dot::new("A", 0));
    /// assert_eq!(v.get(&"A"), 2);
    /// ```
    fn apply(&mut self, dot: Self::Op) {
        if self.get(&dot.actor) < dot.counter {
            self.dots.insert(dot.actor, dot.counter);
        }
    }
}

impl<A: Ord + Clone + Debug> CvRDT for VClock<A> {
    type Validation = Infallible;

    fn validate_merge(&self, _other: &Self) -> Result<(), Self::Validation> {
        Ok(())
    }

    fn merge(&mut self, other: Self) {
        for dot in other.into_iter() {
            self.apply(dot);
        }
    }
}

impl<A: Ord> VClock<A> {
    /// Returns a new `VClock` instance.
    pub fn new() -> Self {
        Default::default()
    }

    /// Returns a clone of self but with information that is older than given clock is
    /// forgotten
    pub fn clone_without(&self, base_clock: &VClock<A>) -> VClock<A>
    where
        A: Clone,
    {
        let mut cloned = self.clone();
        cloned.reset_remove(base_clock);
        cloned
    }

    /// Generate Op to increment an actor's counter.
    ///
    /// # Examples
    /// ```
    /// use crdts::{VClock, CmRDT};
    /// let mut a = VClock::new();
    ///
    /// // `a.inc()` does not mutate the vclock!
    /// let op = a.inc("A");
    /// assert_eq!(a, VClock::new());
    ///
    /// // we must apply the op to the VClock to have
    /// // its edit take effect.
    /// a.apply(op.clone());
    /// assert_eq!(a.get(&"A"), 1);
    ///
    /// // Op's can be replicated to another node and
    /// // applied to the local state there.
    /// let mut other_node = VClock::new();
    /// other_node.apply(op);
    /// assert_eq!(other_node.get(&"A"), 1);
    /// ```
    pub fn inc(&self, actor: A) -> Dot<A>
    where
        A: Clone,
    {
        self.dot(actor).inc()
    }

    /// Return the associated counter for this actor.
    /// All actors not in the vclock have an implied count of 0
    pub fn get(&self, actor: &A) -> u64 {
        self.dots.get(actor).cloned().unwrap_or(0)
    }

    /// Return the Dot for a given actor
    pub fn dot(&self, actor: A) -> Dot<A> {
        let counter = self.get(&actor);
        Dot::new(actor, counter)
    }

    /// True if two vector clocks have diverged.
    ///
    /// # Examples
    /// ```
    /// use crdts::{VClock, CmRDT};
    /// let (mut a, mut b) = (VClock::new(), VClock::new());
    /// a.apply(a.inc("A"));
    /// b.apply(b.inc("B"));
    /// assert!(a.concurrent(&b));
    /// ```
    pub fn concurrent(&self, other: &VClock<A>) -> bool {
        self.partial_cmp(other).is_none()
    }

    /// Returns `true` if this vector clock contains nothing.
    pub fn is_empty(&self) -> bool {
        self.dots.is_empty()
    }

    /// Returns the common elements (same actor and counter)
    /// for two `VClock` instances.
    pub fn intersection(left: &VClock<A>, right: &VClock<A>) -> VClock<A>
    where
        A: Clone,
    {
        let mut dots = BTreeMap::new();
        for (left_actor, left_counter) in left.dots.iter() {
            let right_counter = right.get(left_actor);
            if right_counter == *left_counter {
                dots.insert(left_actor.clone(), *left_counter);
            }
        }
        Self { dots }
    }

    /// Reduces this VClock to the greatest-lower-bound of the given
    /// VClock and itsef, as an example see the following code.
    /// ``` rust
    /// use crdts::{VClock, Dot, ResetRemove, CmRDT};
    /// let mut c = VClock::new();
    /// c.apply(Dot::new(23, 6));
    /// c.apply(Dot::new(89, 14));
    /// let c2 = c.clone();
    ///
    /// c.glb(&c2); // this is a no-op since `glb { c, c } = c`
    /// assert_eq!(c, c2);
    ///
    /// c.apply(Dot::new(43, 1));
    /// assert_eq!(c.get(&43), 1);
    /// c.glb(&c2); // should remove the 43 => 1 entry
    /// assert_eq!(c.get(&43), 0);
    /// ```
    pub fn glb(&mut self, other: &Self) {
        self.dots = mem::take(&mut self.dots)
            .into_iter()
            .filter_map(|(actor, count)| {
                // Since an actor missing from the dots map has an implied
                // counter of 0 we can save some memory, and remove the actor.
                let min_count = cmp::min(count, other.get(&actor));
                match min_count {
                    0 => None,
                    _ => Some((actor, min_count)),
                }
            })
            .collect();
    }

    /// Returns an iterator over the dots in this vclock
    pub fn iter(&self) -> impl Iterator<Item = Dot<&A>> {
        self.dots.iter().map(|(a, c)| Dot {
            actor: a,
            counter: *c,
        })
    }
}

/// Generated from calls to VClock::into_iter()
pub struct IntoIter<A: Ord> {
    btree_iter: btree_map::IntoIter<A, u64>,
}

impl<A: Ord> std::iter::Iterator for IntoIter<A> {
    type Item = Dot<A>;

    fn next(&mut self) -> Option<Dot<A>> {
        self.btree_iter
            .next()
            .map(|(actor, counter)| Dot::new(actor, counter))
    }
}

impl<A: Ord> std::iter::IntoIterator for VClock<A> {
    type Item = Dot<A>;
    type IntoIter = IntoIter<A>;

    /// Consumes the vclock and returns an iterator over dots in the clock
    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            btree_iter: self.dots.into_iter(),
        }
    }
}

impl<A: Ord + Clone + Debug> std::iter::FromIterator<Dot<A>> for VClock<A> {
    fn from_iter<I: IntoIterator<Item = Dot<A>>>(iter: I) -> Self {
        let mut clock = VClock::default();

        for dot in iter {
            clock.apply(dot);
        }

        clock
    }
}

impl<A: Ord + Clone + Debug> From<Dot<A>> for VClock<A> {
    fn from(dot: Dot<A>) -> Self {
        let mut clock = VClock::default();
        clock.apply(dot);
        clock
    }
}

#[cfg(feature = "quickcheck")]
use quickcheck::{Arbitrary, Gen};

#[cfg(feature = "quickcheck")]
impl<A: Ord + Clone + Debug + Arbitrary> Arbitrary for VClock<A> {
    fn arbitrary(g: &mut Gen) -> Self {
        let mut clock = VClock::default();

        for _ in 0..u8::arbitrary(g) % 10 {
            clock.apply(Dot::arbitrary(g));
        }

        clock
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        let mut shrunk_clocks = Vec::default();
        for dot in self.clone().into_iter() {
            let clock_without_dot: Self = self.clone().into_iter().filter(|d| d != &dot).collect();

            for shrunk_dot in dot.shrink() {
                let mut clock = clock_without_dot.clone();
                clock.apply(shrunk_dot);
                shrunk_clocks.push(clock);
            }

            shrunk_clocks.push(clock_without_dot);
        }

        Box::new(shrunk_clocks.into_iter())
    }
}
