//! # GList - Grow-only List CRDT

use core::convert::Infallible;
use core::fmt;
use core::iter::FromIterator;
use core::ops::Bound::*;
use std::collections::BTreeSet;

use num::{BigRational, One, Zero};
use quickcheck::{Arbitrary, Gen};
use serde::{Deserialize, Serialize};

use crate::{CmRDT, CvRDT};

/// Markers provide the main ordering component of our list.
/// Entries in the list are ordered by lexigraphic order
/// of (marker, elem). Elements themselves are tie-breakers
/// in the case of conflicting markers.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Entry<T>(pub Vec<(BigRational, T)>);

impl<T: Clone + Eq> Entry<T> {
    /// Get a reference to the value this entry represents.
    pub fn value(&self) -> &T {
        self.0.last().map(|(_, elem)| elem).unwrap() // TODO: remove this unwrap
    }

    /// Get the value this entry represents, consuming the entry.
    pub fn into_value(mut self) -> T {
        self.0.pop().map(|(_, elem)| elem).unwrap() // TODO: remove this unwrap
    }

    /// Construct an entry between low and high holding the given element.
    pub fn between(low: Option<&Self>, high: Option<&Self>, elem: T) -> Self {
        match (low, high) {
            (Some(low), Some(high)) => {
                // Walk both paths until we reach a fork, constructing the path between these
                // two entries as we go.

                let mut path: Vec<(BigRational, T)> = vec![];
                let low_path = low.0.iter().cloned();
                let high_path = high.0.iter();
                let mut lower_bound = None;
                let mut upper_bound = None;
                for (l, h) in low_path.zip(high_path) {
                    if &l.0 == &h.0 {
                        // The entry between low and high will share the common path between these two
                        // entries. We accumulate this common prefix path as we traverse.
                        path.push(l)
                    } else {
                        // We find a spot where the lower and upper paths fork.
                        // We can insert our elem between these two bounds.
                        lower_bound = Some(l.0);
                        upper_bound = Some(&h.0);
                        break;
                    }
                }
                path.push((rational_between(lower_bound.as_ref(), upper_bound), elem));
                Entry(path)
            }

            (low, high) => Entry(vec![(
                rational_between(
                    low.and_then(|low_entry| low_entry.0.first().map(|(r, _)| r)),
                    high.and_then(|high_entry| high_entry.0.first().map(|(r, _)| r)),
                ),
                elem,
            )]),
        }
    }
}

impl<T: fmt::Display> fmt::Display for Entry<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "E<")?;
        let mut iter = self.0.iter();
        if let Some((r, e)) = iter.next() {
            write!(f, "{}:{}", r, e)?;
        }
        for (r, e) in iter {
            write!(f, ", {}:{}", r, e)?;
        }
        write!(f, ">")
    }
}

/// Operations that can be performed on a List
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Op<T> {
    /// Insert an element.
    Insert {
        /// The Entry to insert.
        entry: Entry<T>,
    },
}

/// The GList is a grow-only list, that is, it allows inserts but not deletes.
/// Entries in the list are paths through an ordered tree, the tree grows deeper
/// when we try to insert between two elements who were inserted concurrently and
/// whose paths happen to have the same prefix.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct GList<T: Ord> {
    list: BTreeSet<Entry<T>>,
}

impl<T: fmt::Display + Ord> fmt::Display for GList<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "GList[")?;
        let mut iter = self.list.iter();
        if let Some(e) = iter.next() {
            write!(f, "{}", e)?;
        }
        for e in iter {
            write!(f, "{}", e)?;
        }
        write!(f, "]")
    }
}

impl<T: Ord> Default for GList<T> {
    fn default() -> Self {
        Self {
            list: Default::default(),
        }
    }
}

impl<T: Ord + Clone> GList<T> {
    /// Create an empty GList
    pub fn new() -> Self {
        Self::default()
    }

    /// Read the elements of the list into a user defined container
    pub fn read<'a, C: FromIterator<&'a T>>(&'a self) -> C {
        self.list.iter().map(|entry| entry.value()).collect()
    }

    /// Read the elements of the list into a user defined container, consuming the list in the process.
    pub fn read_into<C: FromIterator<T>>(self) -> C {
        self.list
            .into_iter()
            .map(|entry| entry.into_value())
            .collect()
    }

    /// Iterate over the elements of the list
    pub fn iter(&self) -> std::collections::btree_set::Iter<Entry<T>> {
        self.list.iter()
    }

    /// Return the element and it's marker at the specified index
    pub fn get(&self, idx: usize) -> Option<&Entry<T>> {
        self.list.iter().nth(idx)
    }

    /// Generate an Op to insert the given element before the given marker
    pub fn insert_before(&self, high_entry_opt: Option<&Entry<T>>, elem: T) -> Op<T> {
        let low_entry_opt = high_entry_opt.and_then(|high_entry| {
            self.list
                .range((Unbounded, Excluded(high_entry.clone())))
                .rev()
                .find(|entry| entry < &high_entry)
        });
        let entry = Entry::between(low_entry_opt, high_entry_opt, elem);
        Op::Insert { entry }
    }

    /// Generate an insert op to insert the given element after the given marker
    pub fn insert_after(&self, low_entry_opt: Option<&Entry<T>>, elem: T) -> Op<T> {
        let high_entry_opt = low_entry_opt.and_then(|low_entry| {
            self.list
                .range((Excluded(low_entry.clone()), Unbounded))
                .find(|entry| entry > &low_entry)
        });
        let entry = Entry::between(low_entry_opt, high_entry_opt, elem);
        Op::Insert { entry }
    }

    /// Get the length of the list.
    pub fn len(&self) -> usize {
        self.list.len()
    }

    /// Check if the list is empty.
    pub fn is_empty(&self) -> bool {
        self.list.is_empty()
    }

    /// Get first element of the sequence represented by the list.
    pub fn first(&self) -> Option<&Entry<T>> {
        self.iter().next()
    }

    /// Get last element of the sequence represented by the list.
    pub fn last(&self) -> Option<&Entry<T>> {
        self.iter().rev().next()
    }
}

impl<T: Ord> CmRDT for GList<T> {
    type Op = Op<T>;
    type Validation = Infallible;

    fn validate_op(&self, _: &Self::Op) -> Result<(), Self::Validation> {
        Ok(())
    }

    fn apply(&mut self, op: Self::Op) {
        match op {
            Op::Insert { entry } => self.list.insert(entry),
        };
    }
}

impl<T: Ord> CvRDT for GList<T> {
    type Validation = Infallible;

    fn validate_merge(&self, _: &Self) -> Result<(), Self::Validation> {
        Ok(())
    }

    fn merge(&mut self, other: Self) {
        self.list.extend(other.list)
    }
}

impl<T: Arbitrary> Arbitrary for Entry<T> {
    fn arbitrary<G: Gen>(g: &mut G) -> Self {
        let mut path = vec![];
        for _ in 0..(u8::arbitrary(g) % 7) {
            let ordering_index_material: Vec<(i64, i64)> = Arbitrary::arbitrary(g);
            let ordering_index = ordering_index_material
                .into_iter()
                .filter(|(_, d)| d != &0)
                .take(3)
                .map(|(n, d)| BigRational::new(n.into(), d.into()))
                .sum();
            path.push((ordering_index, T::arbitrary(g)));
        }
        Entry(path)
    }
}

impl<T: Arbitrary> Arbitrary for Op<T> {
    fn arbitrary<G: Gen>(g: &mut G) -> Self {
        let entry = Entry::arbitrary(g);
        Op::Insert { entry }
    }
}

fn rational_between(low: Option<&BigRational>, high: Option<&BigRational>) -> BigRational {
    match (low, high) {
        (None, None) => BigRational::zero(),
        (Some(low), None) => low + BigRational::one(),
        (None, Some(high)) => high - BigRational::one(),
        (Some(low), Some(high)) => (low + high) / BigRational::from_integer(2.into()),
    }
}
