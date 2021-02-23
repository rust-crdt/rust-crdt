//! # GList - Grow-only List CRDT

use core::convert::Infallible;
use core::fmt;
use core::iter::FromIterator;
use core::ops::Bound::*;
use std::collections::BTreeSet;

use num::{BigInt, BigRational, One, Zero};
use quickcheck::{Arbitrary, Gen};
use serde::{Deserialize, Serialize};

use crate::{CmRDT, CvRDT};

/// Markers provide the main ordering component of our list.
/// Entries in the list are ordered by lexigraphic order
/// of (marker, elem). Elements themselves are tie-breakers
/// in the case of conflicting markers.
#[derive(Clone, Serialize, Deserialize, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Marker(BigRational);

impl Marker {
    fn between(low: Option<&Self>, high: Option<&Self>) -> Self {
        match (low, high) {
            (None, None) => Default::default(),
            (Some(low), None) => Marker(&low.0 + &BigRational::one()),
            (None, Some(high)) => Marker(&high.0 - &BigRational::one()),
            (Some(low), Some(high)) => {
                Marker((&low.0 + &high.0) / BigRational::from_integer(2.into()))
            }
        }
    }
}

impl<N: Into<BigInt>> From<N> for Marker {
    fn from(n: N) -> Self {
        Marker(BigRational::from_integer(n.into()))
    }
}

impl fmt::Debug for Marker {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl fmt::Display for Marker {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "M{}", self.0)
    }
}

impl Default for Marker {
    fn default() -> Self {
        Marker(BigRational::zero())
    }
}

/// Operations that can be performed on a List
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Op<T> {
    /// Insert an element
    Insert {
        /// Ordering marker
        marker: Marker,
        /// Element to insert
        elem: T,
    },
}

/// The GList is a grow-only list, that is, it allows inserts but not deletes.
/// It is similar to the GSet, with each element tagged with an ordering marker.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct GList<T: Ord> {
    list: BTreeSet<(Marker, T)>,
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

    /// Read the elements of the list
    pub fn read<C: FromIterator<T>>(self) -> C {
        self.list.into_iter().map(|(_, e)| e).collect()
    }

    /// Iterate over the elements of the list
    pub fn iter(&self) -> std::collections::btree_set::Iter<(Marker, T)> {
        self.list.iter()
    }

    /// Return the element and it's marker at the specified index
    pub fn get(&self, idx: usize) -> Option<&(Marker, T)> {
        self.list.iter().nth(idx)
    }

    /// Generate an Op to insert the given element before the given marker
    pub fn insert_before(&self, high_marker_opt: Option<&Marker>, elem: T) -> Op<T> {
        let low_marker_opt = high_marker_opt.and_then(|high_marker| {
            self.list
                .range((Unbounded, Excluded((high_marker.clone(), elem.clone()))))
                .rev()
                .map(|(marker, _)| marker)
                .find(|marker| marker < &high_marker)
        });
        let marker = Marker::between(low_marker_opt, high_marker_opt);
        Op::Insert { marker, elem }
    }

    /// Generate an insert op to insert the given element after the given marker
    pub fn insert_after(&self, low_marker_opt: Option<&Marker>, elem: T) -> Op<T> {
        let high_marker_opt = low_marker_opt.and_then(|low_marker| {
            self.list
                .range((Excluded((low_marker.clone(), elem.clone())), Unbounded))
                .map(|(marker, _)| marker)
                .find(|marker| marker > &low_marker)
        });
        let marker = Marker::between(low_marker_opt, high_marker_opt);
        Op::Insert { marker, elem }
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
    pub fn first(&self) -> Option<&(Marker, T)> {
        self.iter().next()
    }

    /// Get last element of the sequence represented by the list.
    pub fn last(&self) -> Option<&(Marker, T)> {
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
            Op::Insert { marker, elem } => self.list.insert((marker, elem)),
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

impl Arbitrary for Marker {
    fn arbitrary<G: Gen>(g: &mut G) -> Self {
        let marker_material: Vec<(i64, i64)> = Arbitrary::arbitrary(g);
        let marker = marker_material
            .into_iter()
            .filter(|(_, d)| d != &0)
            .take(3)
            .map(|(n, d)| BigRational::new(n.into(), d.into()))
            .sum();
        Marker(marker)
    }
}

impl<T: Arbitrary> Arbitrary for Op<T> {
    fn arbitrary<G: Gen>(g: &mut G) -> Self {
        let marker = Marker::arbitrary(g);
        let elem = T::arbitrary(g);
        Op::Insert { marker, elem }
    }
}
