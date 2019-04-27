use std::collections::BTreeSet;
use std::fmt::Debug;

use serde::{Deserialize, Serialize};

use crate::traits::{CmRDT, CvRDT};

/// A `GSet` is a grow-only set.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct GSet<T: Ord> {
    value: BTreeSet<T>,
}

impl<T: Ord> Default for GSet<T> {
    fn default() -> Self {
        GSet::new()
    }
}

impl<T: Ord + Clone> CvRDT for GSet<T> {
    /// Merges another `GSet` into this one.
    ///
    /// # Examples
    ///
    /// ```
    /// use crdts::{GSet, CvRDT, CmRDT};
    /// let (mut a, mut b) = (GSet::new(), GSet::new());
    /// a.insert(1);
    /// b.insert(2);
    /// a.merge(b);
    /// assert!(a.contains(&1));
    /// assert!(a.contains(&2));
    /// ```
    fn merge(&mut self, other: Self) {
        other.value.into_iter().for_each(|e| self.insert(e))
    }
}

impl<T: Ord + Debug> CmRDT for GSet<T> {
    type Op = T;

    fn apply(&mut self, op: Self::Op) {
        self.insert(op);
    }
}

impl<T: Ord> GSet<T> {
    /// Instantiates an empty `GSet`.
    pub fn new() -> Self {
        GSet {
            value: BTreeSet::new(),
        }
    }

    /// Inserts an element into this `GSet`.
    ///
    /// # Examples
    ///
    /// ```
    /// use crdts::GSet;
    /// let mut a = GSet::new();
    /// a.insert(1);
    /// assert!(a.contains(&1));
    /// ```
    pub fn insert(&mut self, element: T) {
        self.value.insert(element);
    }

    /// Returns `true` if the `GSet` contains the element.
    ///
    /// # Examples
    ///
    /// ```
    /// use crdts::GSet;
    /// let mut a = GSet::new();
    /// a.insert(1);
    /// assert!(a.contains(&1));
    /// ```
    pub fn contains(&self, element: &T) -> bool {
        self.value.contains(element)
    }
}
