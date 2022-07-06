//! # GList - Grow-only List CRDT

use core::convert::Infallible;
use core::fmt;
use core::iter::FromIterator;
use core::ops::Bound::*;
use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};

use crate::{CmRDT, CvRDT, Identifier};

/// Operations that can be performed on a List
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Op<T> {
    /// Insert an element.
    Insert {
        /// The element identifier to insert.
        id: Identifier<T>,
    },
}

/// The GList is a grow-only list, that is, it allows inserts but not deletes.
/// Elements in the list are paths through an ordered tree, the tree grows deeper
/// when we try to insert between two elements who were inserted concurrently and
/// whose paths happen to have the same prefix.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct GList<T: Ord> {
    list: BTreeSet<Identifier<T>>,
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
        self.list.iter().map(|id| id.value()).collect()
    }

    /// Read the elements of the list into a user defined container, consuming the list in the process.
    pub fn read_into<C: FromIterator<T>>(self) -> C {
        self.list.into_iter().map(|id| id.into_value()).collect()
    }

    /// Iterate over the elements of the list
    pub fn iter(&self) -> std::collections::btree_set::Iter<Identifier<T>> {
        self.list.iter()
    }

    /// Return the element and it's marker at the specified index
    pub fn get(&self, idx: usize) -> Option<&Identifier<T>> {
        self.list.iter().nth(idx)
    }

    /// Generate an Op to insert the given element before the given marker
    pub fn insert_before(&self, high_id_opt: Option<&Identifier<T>>, elem: T) -> Op<T> {
        let low_id_opt = high_id_opt.and_then(|high_id| {
            self.list
                .range((Unbounded, Excluded(high_id.clone())))
                .rev()
                .find(|id| id < &high_id)
        });
        let id = Identifier::between(low_id_opt, high_id_opt, elem);
        Op::Insert { id }
    }

    /// Generate an insert op to insert the given element after the given marker
    pub fn insert_after(&self, low_id_opt: Option<&Identifier<T>>, elem: T) -> Op<T> {
        let high_id_opt = low_id_opt.and_then(|low_id| {
            self.list
                .range((Excluded(low_id.clone()), Unbounded))
                .find(|id| id > &low_id)
        });
        let id = Identifier::between(low_id_opt, high_id_opt, elem);
        Op::Insert { id }
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
    pub fn first(&self) -> Option<&Identifier<T>> {
        self.iter().next()
    }

    /// Get last element of the sequence represented by the list.
    pub fn last(&self) -> Option<&Identifier<T>> {
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
            Op::Insert { id } => self.list.insert(id),
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

#[cfg(feature = "quickcheck")]
use quickcheck::{Arbitrary, Gen};

#[cfg(feature = "quickcheck")]
impl<T: Arbitrary> Arbitrary for Op<T> {
    fn arbitrary<G: Gen>(g: &mut G) -> Self {
        let id = Identifier::arbitrary(g);
        Op::Insert { id }
    }
}
