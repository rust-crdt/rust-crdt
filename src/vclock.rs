//! The `vclock` crate provides a generic vector clock implementation.
//!
//! # Examples
//!
//! ```
//! use crdts::VClock;
//! let (mut a, mut b) = (VClock::new(), VClock::new());
//! a.witness("A".to_string(), 2);
//! b.witness("A".to_string(), 1);
//! assert!(a > b);
//! ```

use super::*;

use std::cmp::Ordering;
use std::collections::BTreeMap;

/// A counter is used to track causality at a particular actor.
pub type Counter = u64;

trait AddableU64 {
    fn add_u64(&mut self, other: u64) -> Self;
}

/// A `VClock` is a standard vector clock.
/// It contains a set of "actors" and associated counters.
/// When a particular actor witnesses a mutation, their associated
/// counter in a `VClock` is incremented. `VClock` is typically used
/// as metadata for associated application data, rather than as the
/// container for application data. `VClock` just tracks causality.
/// It can tell you if something causally descends something else,
/// or if different replicas are "concurrent" (were mutated in
/// isolation, and need to be resolved externally).
#[serde(bound(deserialize = ""))]
#[derive(Debug, Clone, Ord, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct VClock<A: Ord + Clone + Serialize + DeserializeOwned> {
    /// dots is the mapping from actors to their associated counters
    pub dots: BTreeMap<A, Counter>,
}

impl<A: Ord + Clone + Serialize + DeserializeOwned> PartialOrd for VClock<A> {
    fn partial_cmp(&self, other: &VClock<A>) -> Option<Ordering> {
        if self == other {
            Some(Ordering::Equal)
        } else if other.dots.iter().all(|(w, c)| {
            self.contains_descendent_element(w, c)
        })
        {
            Some(Ordering::Greater)
        } else if self.dots.iter().all(|(w, c)| {
            other.contains_descendent_element(w, c)
        })
        {
            Some(Ordering::Less)
        } else {
            None
        }
    }
}

impl<A: Ord + Clone + Serialize + DeserializeOwned> VClock<A> {
    /// Returns a new `VClock` instance.
    pub fn new() -> VClock<A> {
        VClock { dots: BTreeMap::new() }
    }

    /// Returns the greatest lower bound of given clocks
    ///
    /// # Examples
    ///
    /// ``` rust
    /// use crdts::VClock;
    /// let (mut a, mut b) = (VClock::new(), VClock::new());
    /// a.witness("A".to_string(), 3);
    /// a.witness("B".to_string(), 6);
    /// b.witness("A".to_string(), 2);
    ///
    /// let glb = VClock::glb(&a, &b);
    ///
    /// assert_eq!(glb.get(&"A".to_string()), Some(2));
    /// assert_eq!(glb.get(&"B".to_string()), None);
    /// assert!(a >= glb);
    /// assert!(b >= glb);
    /// ```
    pub fn glb(a: &VClock<A>, b: &VClock<A>) -> VClock<A> {
        let mut glb_vclock = VClock::new();
        for (actor, a_cntr) in a.dots.iter() {
            if let Some(b_cntr) = b.get(actor){
                let min_cntr = if *a_cntr < b_cntr {
                    *a_cntr
                } else {
                    b_cntr
                };
                glb_vclock.dots.insert(actor.clone(), min_cntr);
            }
        }
        glb_vclock
    }

    /// For a particular actor, possibly store a new counter
    /// if it dominates.
    ///
    /// # Examples
    ///
    /// ```
    /// use crdts::VClock;
    /// let (mut a, mut b) = (VClock::new(), VClock::new());
    /// a.witness("A".to_string(), 2);
    /// a.witness("A".to_string(), 0); // ignored because 2 dominates 0
    /// b.witness("A".to_string(), 1);
    /// assert!(a > b);
    /// ```
    ///
    pub fn witness(&mut self, actor: A, counter: Counter) -> Result<(), ()> {
        if !self.contains_descendent_element(&actor, &counter) {
            self.dots.insert(actor, counter);
            Ok(())
        } else {
            Err(())
        }
    }

    /// For a particular actor, increment the associated counter.
    ///
    /// # Examples
    ///
    /// ```
    /// use crdts::VClock;
    /// let (mut a, mut b) = (VClock::new(), VClock::new());
    /// a.increment("A".to_string());
    /// a.increment("A".to_string());
    /// a.witness("A".to_string(), 0); // ignored because 2 dominates 0
    /// b.increment("A".to_string());
    /// assert!(a > b);
    /// ```
    ///
    pub fn increment(&mut self, actor: A) -> Counter {
        let next = self.dots.get(&actor).map(|c| *c).unwrap_or(0) + 1;
        self.dots.insert(actor, next);
        next
    }

    /// Merge another vector clock into this one, without
    /// regard to dominance.
    ///
    /// # Examples
    ///
    /// ```
    /// use crdts::VClock;
    /// let (mut a, mut b, mut c) = (VClock::new(), VClock::new(), VClock::new());
    /// a.increment("A".to_string());
    /// b.increment("B".to_string());
    /// c.increment("A".to_string());
    /// c.increment("B".to_string());
    /// a.merge(&b);
    /// assert_eq!(a, c);
    /// ```
    ///
    #[allow(unused_must_use)]
    pub fn merge(&mut self, other: &VClock<A>) {
        for (actor, counter) in other.dots.iter() {
            self.witness(actor.clone(), *counter);
        }
    }

    /// Determine if a single element is present and descendent.
    /// Generally prefer using the higher-level comparison operators
    /// between vclocks over this specific method.
    #[inline]
    pub fn contains_descendent_element(
        &self,
        actor: &A,
        counter: &Counter,
    ) -> bool {
        self.dots
            .get(actor)
            .map(|our_counter| our_counter >= counter)
            .unwrap_or(false)
    }

    /// True if two vector clocks have diverged.
    ///
    /// # Examples
    ///
    /// ```
    /// use crdts::VClock;
    /// let (mut a, mut b) = (VClock::new(), VClock::new());
    /// a.increment("A".to_string());
    /// b.increment("B".to_string());
    /// assert!(a.concurrent(&b));
    /// ```
    pub fn concurrent(&self, other: &VClock<A>) -> bool {
        self.partial_cmp(other).is_none()
    }

    /// Return the associated counter for this actor, if present.
    pub fn get(&self, actor: &A) -> Option<Counter> {
        self.dots.get(actor).map(|counter| *counter)
    }

    /// Returns `true` if this vector clock contains nothing.
    pub fn is_empty(&self) -> bool {
        self.dots.is_empty()
    }

    /// Return the dots that self dominates compared to another clock.
    pub fn dominating_dots(
        &self,
        dots: &BTreeMap<A, Counter>,
    ) -> BTreeMap<A, Counter> {
        let mut ret = BTreeMap::new();
        for (actor, counter) in self.dots.iter() {
            let other = dots.get(actor).map(|c| *c).unwrap_or(0);
            if *counter > other {
                ret.insert(actor.clone(), *counter);
            }
        }
        ret
    }

    /// Return a new `VClock` that contains the entries for which we have
    /// a counter that dominates another `VClock`.
    ///
    /// # Examples
    ///
    /// ```
    /// use crdts::VClock;
    /// let (mut a, mut b) = (VClock::new(), VClock::new());
    /// a.witness("A".to_string(), 3);
    /// a.witness("B".to_string(), 2);
    /// a.witness("D".to_string(), 14);
    /// a.witness("G".to_string(), 22);
    ///
    /// b.witness("A".to_string(), 4);
    /// b.witness("B".to_string(), 1);
    /// b.witness("C".to_string(), 1);
    /// b.witness("D".to_string(), 14);
    /// b.witness("E".to_string(), 5);
    /// b.witness("F".to_string(), 2);
    ///
    /// let dom = a.dominating_vclock(&b);
    /// assert_eq!(dom.get(&"B".to_string()), Some(2));
    /// assert_eq!(dom.get(&"G".to_string()), Some(22));
    /// ```
    pub fn dominating_vclock(&self, other: &VClock<A>) -> VClock<A> {
        let dots = self.dominating_dots(&other.dots);
        VClock { dots: dots }
    }

    /// Returns the common elements (same actor and counter)
    /// for two `VClock` instances.
    pub fn intersection(&self, other: &VClock<A>) -> VClock<A> {
        let mut dots = BTreeMap::new();
        for (actor, counter) in self.dots.iter() {
            if let Some(other_counter) = other.dots.get(actor) {
                if other_counter == counter {
                    dots.insert(actor.clone(), *counter);
                }
            }
        }
        VClock { dots: dots }
    }
}

#[cfg(test)]
mod tests {
    extern crate rand;
    extern crate quickcheck;

    use self::quickcheck::{Arbitrary, Gen};
    use super::*;

    impl Arbitrary for VClock<u16> {
        fn arbitrary<G: Gen>(g: &mut G) -> VClock<u16> {
            let mut v = VClock::new();
            for witness in 0..g.gen_range(0, 7) {
                v.witness(witness, g.gen_range(1, 7)).unwrap();
            }
            v
        }

        fn shrink(&self) -> Box<Iterator<Item = VClock<u16>>> {
            let mut smaller = vec![];
            for k in self.dots.keys() {
                let mut vc = self.clone();
                vc.dots.remove(k);
                smaller.push(vc)
            }
            Box::new(smaller.into_iter())
        }
    }

    #[test]
    fn test_merge() {
        let (mut a, mut b) = (VClock::new(), VClock::new());
        a.witness(1, 1).unwrap();
        a.witness(2, 2).unwrap();
        a.witness(4, 4).unwrap();

        b.witness(3, 3).unwrap();
        b.witness(4, 3).unwrap();

        a.merge(&b);
        assert_eq!(a.get(&1), Some(1));
        assert_eq!(a.get(&2), Some(2));
        assert_eq!(a.get(&3), Some(3));
        assert_eq!(a.get(&4), Some(4));
    }

    #[test]
    fn test_merge_less_left() {
        let (mut a, mut b) = (VClock::new(), VClock::new());
        a.witness(5, 5).unwrap();

        b.witness(6, 6).unwrap();
        b.witness(7, 7).unwrap();

        a.merge(&b);
        assert_eq!(a.get(&5), Some(5));
        assert_eq!(a.get(&6), Some(6));
        assert_eq!(a.get(&7), Some(7));
    }

    #[test]
    fn test_merge_less_right() {
        let (mut a, mut b) = (VClock::new(), VClock::new());
        a.witness(6, 6).unwrap();
        a.witness(7, 7).unwrap();

        b.witness(5, 5).unwrap();

        a.merge(&b);
        assert_eq!(a.get(&5), Some(5));
        assert_eq!(a.get(&6), Some(6));
        assert_eq!(a.get(&7), Some(7));
    }

    #[test]
    fn test_merge_same_id() {
        let (mut a, mut b) = (VClock::new(), VClock::new());
        a.witness(1, 1).unwrap();
        a.witness(2, 1).unwrap();

        b.witness(1, 1).unwrap();
        b.witness(3, 1).unwrap();

        a.merge(&b);
        assert_eq!(a.get(&1), Some(1));
        assert_eq!(a.get(&2), Some(1));
        assert_eq!(a.get(&3), Some(1));
    }

    #[test]
    fn test_vclock_ordering() {
        assert_eq!(VClock::<i8>::new(), VClock::new());

        let (mut a, mut b) = (VClock::new(), VClock::new());
        a.witness("A".to_string(), 1).unwrap();
        a.witness("A".to_string(), 2).unwrap();
        assert!(a.witness("A".to_string(), 0).is_err());
        b.witness("A".to_string(), 1).unwrap();

        // a {A:2}
        // b {A:1}
        // expect: a dominates
        assert!(a > b);
        assert!(b < a);
        assert!(a != b);

        b.witness("A".to_string(), 3).unwrap();
        // a {A:2}
        // b {A:3}
        // expect: b dominates
        assert!(b > a);
        assert!(a < b);
        assert!(a != b);

        a.witness("B".to_string(), 1).unwrap();
        // a {A:2, B:1}
        // b {A:3}
        // expect: concurrent
        assert!(a != b);
        assert!(!(a > b));
        assert!(!(b > a));

        a.witness("A".to_string(), 3).unwrap();
        // a {A:3, B:1}
        // b {A:3}
        // expect: a dominates
        assert!(a > b);
        assert!(b < a);
        assert!(a != b);

        b.witness("B".to_string(), 2).unwrap();
        // a {A:3, B:1}
        // b {A:3, B:2}
        // expect: b dominates
        assert!(b > a);
        assert!(a < b);
        assert!(a != b);

        a.witness("B".to_string(), 2).unwrap();
        // a {A:3, B:2}
        // b {A:3, B:2}
        // expect: equal
        assert!(!(b > a));
        assert!(!(a > b));
        assert_eq!(a, b);
    }
}
