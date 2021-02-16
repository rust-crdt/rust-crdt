//! # LSEQ
//!
//! An LSEQ tree is a CRDT for storing sequences of data (Strings, ordered lists).
//! It provides an efficient view of the stored sequence, with fast index, insertion and deletion
//! operations.
//!
//! LSEQ [1] is a member of the LOGOOT [2] family of algorithms for CRDT sequences. The major difference
//! with LOGOOT is in the _allocation strategy_ that LSEQ employs to handle insertions.
//!
//! Internally, LSEQ views the sequence as the nodes of an ordered, exponential tree. An
//! exponential tree is a tree where the number of childen grows exponentially with the depth of a
//! node. For LSEQ, each layer of the tree doubles the available space. Each child is numbered from
//! 0..2^(3+depth). The first and last child of a node cannot be turned into leaves.
//!
//! The path from the root of a tree to a node is called the _identifier_ of an element.
//!
//! The major challenge for LSEQs is the question of generating new identifiers for insertions.
//!
//! If we have the sequence of ordered pairs of identifiers and values `[ ix1: a , ix2: b , ix3: c ]`,
//! and we want to insert `d` at the second position, we must find an identifer ix4 such that
//! ix1 < ix4 < ix2. This ensures that every site will insert d in the same relative position in
//! the sequence even if they dont have ix2 or ix1 yet. The [`IdentGen`] encapsulates this identifier
//! generation, and ensures that the result is always between the two provided bounds.
//!
//! LSEQ is a CmRDT, to guarantee convergence it must see every operation. It also requires that
//! they are delivered in a _causal_ order. Every deletion _must_ be applied _after_ it's
//! corresponding insertion. To guarantee this property, use a causality barrier.
//!
//! [1] B. Nédelec, P. Molli, A. Mostefaoui, and E. Desmontils,
//! “LSEQ: an adaptive structure for sequences in distributed collaborative editing,”
//! in Proceedings of the 2013 ACM symposium on Document engineering - DocEng ’13,
//! Florence, Italy, 2013, p. 37, doi: 10.1145/2494266.2494278.
//!
//! [2] S. Weiss, P. Urso, and P. Molli,
//! “Logoot: A Scalable Optimistic Replication Algorithm for Collaborative Editing on P2P Networks,”
//! in 2009 29th IEEE International Conference on Distributed Computing Systems,
//! Montreal, Quebec, Canada, Jun. 2009, pp. 404–412, doi: 10.1109/ICDCS.2009.75.

use core::cmp::Ordering;
use std::collections::BTreeMap;
use std::fmt;

use num::{BigRational, One, Zero};
use serde::{Deserialize, Serialize};

use crate::{CmRDT, Dot, VClock};

/// Contains the implementation of the exponential tree for LSeq

/// A unique identifier for an element in the sequence.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub struct Index<A> {
    id: BigRational,
    dot: Dot<A>,
}

impl<A: Ord> PartialOrd for Index<A> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(&other))
    }
}

impl<A: Ord> Ord for Index<A> {
    fn cmp(&self, other: &Self) -> Ordering {
        (&self.id, &self.dot.actor, &self.dot.counter).cmp(&(
            &other.id,
            &other.dot.actor,
            &other.dot.counter,
        ))
    }
}

/// As described in the module documentation:
///
/// An LSEQ tree is a CRDT for storing sequences of data (Strings, ordered lists).
/// It provides an efficient view of the stored sequence, with fast index, insertion and deletion
/// operations.
#[derive(Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub struct LSeq<T, A: Ord> {
    seq: BTreeMap<Index<A>, T>,
    clock: VClock<A>,
}

/// Operations that can be performed on an LSeq tree
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Op<T, A> {
    /// Insert an element
    Insert {
        /// Then Index to insert at
        index: Index<A>,
        /// Element to insert
        val: T,
    },
    /// Delete an element
    Delete {
        /// The Index of the insertion we're removing
        index: Index<A>,
        /// id of site that issued delete
        dot: Dot<A>,
    },
}

impl<T, A> Op<T, A> {
    /// Returns the Index this operation is concerning.
    pub fn index(&self) -> &Index<A> {
        match self {
            Op::Insert { index, .. } | Op::Delete { index, .. } => index,
        }
    }

    /// Return the Dot originating the operation.
    pub fn dot(&self) -> &Dot<A> {
        match self {
            Op::Insert { index, .. } => &index.dot,
            Op::Delete { dot, .. } => dot,
        }
    }
}

impl<T, A: Ord> Default for LSeq<T, A> {
    fn default() -> Self {
        Self {
            seq: Default::default(),
            clock: Default::default(),
        }
    }
}

impl<T, A: Ord + Clone> LSeq<T, A> {
    /// Create an empty LSEQ
    pub fn new() -> Self {
        Self::default()
    }

    /// Perform a local insertion of an element at a given position.
    /// If `ix` is greater than the length of the LSeq then it is appended to the end.
    ///
    /// # Panics
    ///
    /// * If the allocation of a new index was not between `ix` and `ix - 1`.
    pub fn insert_index(&mut self, mut ix: usize, val: T, actor: A) -> Op<T, A> {
        ix = ix.min(self.seq.len());
        let zero = BigRational::zero();
        let one = BigRational::one();
        let two = BigRational::from_integer(2.into());

        // TODO: replace this logic with BTreeMap::range()
        let (prev, next) = match ix.checked_sub(1) {
            Some(indices_to_drop) => {
                let mut indices = self.seq.keys().skip(indices_to_drop);
                (indices.next(), indices.next())
            }
            None => {
                // Inserting at the front of the list
                let mut indices = self.seq.keys();
                (None, indices.next())
            }
        };

        let id = match (prev, next) {
            (Some(p), Some(q)) => (&p.id + &q.id) / two,
            (Some(p), None) => &p.id + &one,
            (None, Some(p)) => &p.id - &one,
            (None, None) => zero,
        };
        let dot = self.clock.inc(actor);
        let index = Index { id, dot };
        Op::Insert { index, val }
    }

    /// Perform a local insertion of an element at the end of the sequence.
    pub fn append(&mut self, c: T, actor: A) -> Op<T, A> {
        let ix = self.seq.len();
        self.insert_index(ix, c, actor)
    }

    /// Perform a local deletion at `ix`.
    ///
    /// If `ix` is out of bounds, i.e. `ix > self.len()`, then
    /// the `Op` is not performed and `None` is returned.
    pub fn delete_index(&mut self, ix: usize, actor: A) -> Option<Op<T, A>> {
        self.seq.keys().nth(ix).cloned().map(|index| {
            let dot = self.clock.inc(actor);
            Op::Delete { index, dot }
        })
    }

    /// Perform a local deletion at `ix`. If `ix` is out of bounds
    /// then the last element will be deleted, i.e. `self.len() - 1`.
    pub fn delete_index_or_last(&mut self, ix: usize, actor: A) -> Op<T, A> {
        match self.delete_index(ix, actor.clone()) {
            None => self
                .delete_index(self.len() - 1, actor)
                .expect("delete_index_or_last: 'self.len() - 1'"),
            Some(op) => op,
        }
    }

    /// Get the length of the LSEQ.
    pub fn len(&self) -> usize {
        self.seq.len()
    }

    /// Check if the LSEQ is empty.
    pub fn is_empty(&self) -> bool {
        self.seq.is_empty()
    }

    /// Get the elements represented by the LSEQ.
    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.seq.values()
    }

    /// Get each elements index and value from the LSEQ.
    pub fn iter_entries(&self) -> impl Iterator<Item = (&Index<A>, &T)> {
        self.seq.iter()
    }

    /// Get an element at a position in the sequence represented by the LSEQ.
    pub fn position(&self, ix: usize) -> Option<&T> {
        self.iter().nth(ix)
    }

    /// Finds an element by its Index.
    pub fn get(&self, index: &Index<A>) -> Option<&T> {
        self.seq.get(index)
    }

    /// Get first element of the sequence represented by the LSEQ.
    pub fn first(&self) -> Option<&T> {
        self.first_entry().map(|(_, val)| val)
    }

    /// Get the first Entry of the sequence represented by the LSEQ.
    pub fn first_entry(&self) -> Option<(&Index<A>, &T)> {
        self.seq.iter().next()
    }

    /// Get last element of the sequence represented by the LSEQ.
    pub fn last(&self) -> Option<&T> {
        self.last_entry().map(|(_, val)| val)
    }

    /// Get the last Entry of the sequence represented by the LSEQ.
    pub fn last_entry(&self) -> Option<(&Index<A>, &T)> {
        self.seq.iter().rev().next()
    }

    /// Insert an identifier and value in the LSEQ
    fn insert(&mut self, index: Index<A>, val: T) {
        // Inserts only have an impact if the identifier is not in the tree
        self.seq.entry(index).or_insert(val);
    }

    /// Remove an identifier from the LSEQ
    fn delete(&mut self, index: &Index<A>) {
        // Deletes only have an effect if the identifier is already in the tree
        self.seq.remove(index);
    }
}

impl<T, A: Ord + Clone + fmt::Debug> CmRDT for LSeq<T, A> {
    type Op = Op<T, A>;
    type Validation = crate::DotRange<A>;

    fn validate_op(&self, op: &Self::Op) -> Result<(), Self::Validation> {
        self.clock.validate_op(op.dot())
    }

    /// Apply an operation to an LSeq instance.
    ///
    /// If the operation is an insert and the identifier is **already** present in the LSEQ instance
    /// the result is a no-op
    ///
    /// If the operation is a delete and the identifier is **not** present in the LSEQ instance the
    /// result is a no-op
    fn apply(&mut self, op: Self::Op) {
        let op_dot = op.dot().clone();

        if op_dot.counter <= self.clock.get(&op_dot.actor) {
            return;
        }

        self.clock.apply(op_dot);
        match op {
            Op::Insert { index, val } => self.insert(index, val),
            Op::Delete { index, .. } => self.delete(&index),
        }
    }
}
