//! The `vclock` crate provides a generic vector clock implementation.
//!
//! # Examples
//!
//! ```
//! use crdts::VClock;
//! let (mut a, mut b) = (VClock::new(), VClock::new());
//! a.witness("A", 2);
//! b.witness("A", 1);
//! assert!(a > b);
//! ```

use std::cmp::{Ordering};
use std::collections::BTreeMap;

pub type Counter = u64;

trait AddableU64 {
    fn add_u64(&mut self, other: u64) -> Self;
}

#[derive(Debug, Clone, Ord, PartialEq, Eq, Hash, RustcEncodable, RustcDecodable)]
pub struct VClock<A: Ord + Clone> {
    dots: BTreeMap<A, Counter>
}

impl<A: Ord + Clone> PartialOrd for VClock<A> {
    fn partial_cmp(&self, other: &VClock<A>) -> Option<Ordering> {
        if self == other {
            Some(Ordering::Equal)
        } else if other.dots.iter().all(|(w, c)| self.contains_descendent_element(w, c)) {
            Some(Ordering::Greater)
        } else if self.dots.iter().all(|(w, c)| other.contains_descendent_element(w, c)) {
            Some(Ordering::Less)
        } else {
            None
        }
    }
}

impl<A: Ord + Clone> VClock<A> {
    pub fn new() -> VClock<A> {
        VClock {
            dots: BTreeMap::new()
        }
    }

    /// For a particular actor, possibly store a new counter
    /// if it dominates.
    ///
    /// # Examples
    ///
    /// ```
    /// use crdts::VClock;
    /// let (mut a, mut b) = (VClock::new(), VClock::new());
    /// a.witness("A", 2);
    /// a.witness("A", 0); // ignored because 2 dominates 0
    /// b.witness("A", 1);
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
    /// a.increment("A");
    /// a.increment("A");
    /// a.witness("A", 0); // ignored because 2 dominates 0
    /// b.increment("A");
    /// assert!(a > b);
    /// ```
    ///
    pub fn increment(&mut self, actor: A) -> Counter {
        let next = self.dots.get(&actor)
                            .map(|c| *c)
                            .unwrap_or(0) + 1;
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
    /// a.increment("A");
    /// b.increment("B");
    /// c.increment("A");
    /// c.increment("B");
    /// a.merge(b);
    /// assert_eq!(a, c);
    /// ```
    ///
    #[allow(unused_must_use)]
    pub fn merge(&mut self, other: VClock<A>) {
        for (actor, counter) in other.dots.into_iter() {
            self.witness(actor, counter);
        }
    }

    /// Determine if a single element is present and descendent.
    /// Generally prefer using the higher-level comparison operators
    /// between vclocks over this specific method.
    #[inline]
    pub fn contains_descendent_element(&self, actor: &A, counter: &Counter) -> bool {
        self.dots.get(actor)
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
    /// a.increment("A");
    /// b.increment("B");
    /// assert!(a.concurrent(&b));
    /// ```
    pub fn concurrent(&self, other: &VClock<A>) -> bool {
        self.partial_cmp(other).is_none()
    }

    /// Return the associated counter for this actor, if present.
    pub fn get(&self, actor: &A) -> Option<Counter> {
        self.dots.get(actor).map(|counter| *counter)
    }

    pub fn is_empty(&self) -> bool {
        self.dots.is_empty()
    }

    /// Return the dots that self dominates compared to another clock.
    pub fn dominating_dots(&self, dots: BTreeMap<A, Counter>) -> BTreeMap<A, Counter> {
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
    /// a.witness("A", 3);
    /// a.witness("B", 2);
    /// a.witness("D", 14);
    /// a.witness("G", 22);
    ///
    /// b.witness("A", 4);
    /// b.witness("B", 1);
    /// b.witness("C", 1);
    /// b.witness("D", 14);
    /// b.witness("E", 5);
    /// b.witness("F", 2);
    ///
    /// let dom = a.dominating_vclock(b);
    /// assert_eq!(dom.get(&"B"), Some(2));
    /// assert_eq!(dom.get(&"G"), Some(22));
    /// ```
    pub fn dominating_vclock(&self, other: VClock<A>) -> VClock<A> {
        let dots = self.dominating_dots(other.dots);
        VClock {
            dots: dots
        }
    }

    pub fn intersection(&self, other: VClock<A>) -> VClock<A> {
        let mut dots = BTreeMap::new();
        for (actor, counter) in self.dots.iter() {
            if let Some(other_counter) = other.dots.get(actor) {
                if other_counter == counter {
                    dots.insert(actor.clone(), *counter);
                }
            }
        }
        VClock {
            dots: dots
        }
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_merge() {
        let (mut a, mut b) = (VClock::new(), VClock::new());
        a.witness(1, 1).unwrap();
        a.witness(2, 2).unwrap();
        a.witness(4, 4).unwrap();

        b.witness(3, 3).unwrap();
        b.witness(4, 3).unwrap();

        a.merge(b);
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

        a.merge(b);
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

        a.merge(b);
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

        a.merge(b);
        assert_eq!(a.get(&1), Some(1));
        assert_eq!(a.get(&2), Some(1));
        assert_eq!(a.get(&3), Some(1));
    }

    #[test]
    fn test_vclock_ordering() {
        assert_eq!(VClock::<i8>::new(), VClock::new());

        let (mut a, mut b) = (VClock::new(), VClock::new());
        a.witness("A", 1).unwrap();
        a.witness("A", 2).unwrap();
        assert!(a.witness("A", 0).is_err());
        b.witness("A", 1).unwrap();

        // a {A:2}
        // b {A:1}
        // expect: a dominates
        assert!(a > b);
        assert!(b < a);
        assert!(a != b);

        b.witness("A", 3).unwrap();
        // a {A:2}
        // b {A:3}
        // expect: b dominates
        assert!(b > a);
        assert!(a < b);
        assert!(a != b);

        a.witness("B", 1).unwrap();
        // a {A:2, B:1}
        // b {A:3}
        // expect: concurrent
        assert!(a != b);
        assert!(!(a > b));
        assert!(!(b > a));

        a.witness("A", 3).unwrap();
        // a {A:3, B:1}
        // b {A:3}
        // expect: a dominates
        assert!(a > b);
        assert!(b < a);
        assert!(a != b);

        b.witness("B", 2).unwrap();
        // a {A:3, B:1}
        // b {A:3, B:2}
        // expect: b dominates
        assert!(b > a);
        assert!(a < b);
        assert!(a != b);

        a.witness("B", 2).unwrap();
        // a {A:3, B:2}
        // b {A:3, B:2}
        // expect: equal
        assert!(!(b > a));
        assert!(!(a > b));
        assert_eq!(a, b);
    }
}