use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;

use crate::{CmRDT, CvRDT};

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

impl<T: Ord> From<GSet<T>> for BTreeSet<T> {
    fn from(gset: GSet<T>) -> BTreeSet<T> {
        gset.value
    }
}

impl<T: Ord + Clone> CvRDT for GSet<T> {
    type Validation = ();

    fn validate_merge(&self, other: &Self) -> Result<(), Self::Validation> {
        unimplemented!();
    }

    /// Merges another `GSet` into this one.
    ///
    /// # Examples
    ///
    /// ```rust
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

impl<T: Ord> CmRDT for GSet<T> {
    type Op = T;
    type Validation = ();

    fn validate_op(&self, op: &Self::Op) -> Result<(), Self::Validation> {
        unimplemented!();
    }

    fn apply(&mut self, op: Self::Op) {
        self.insert(op);
    }
}

impl<T: Ord> GSet<T> {
    /// Instantiates an empty `GSet`.
    pub fn new() -> Self {
        Self {
            value: BTreeSet::new(),
        }
    }

    /// Inserts an element into this `GSet`.
    ///
    /// # Examples
    ///
    /// ```rust
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
    /// ```rust
    /// use crdts::GSet;
    /// let mut a = GSet::new();
    /// a.insert(1);
    /// assert!(a.contains(&1));
    /// ```
    pub fn contains(&self, element: &T) -> bool {
        self.value.contains(element)
    }

    /// Returns the `BTreeSet` for this `GSet`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use crdts::GSet;
    /// use std::collections::BTreeSet;
    /// let mut a = GSet::new();
    /// let mut b = BTreeSet::new();
    /// for i in 1..10 {
    ///     a.insert(i);
    ///     b.insert(i);
    /// }
    ///
    /// assert_eq!(a.read(), b);
    /// ```
    pub fn read(&self) -> BTreeSet<T>
    where
        T: Clone,
    {
        self.value.clone()
    }
}
