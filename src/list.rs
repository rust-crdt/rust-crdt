//! # List
//!
//! The List CRDT is an efficient structure for dealing with ordered sequences.
//! It provides an efficient view of the stored sequence with fast index,
//! insertion and deletion.
//!
//! List is based on the LSEQ[1] and LOGOOT[2] family of CRDT's. The major
//! differentiator in this family of CRDT's is in how we allocate identifiers
//! to elements in the sequence.
//!
//! LSEQ/LOGOOT views the sequence as the nodes of an ordered, exponential
//! tree. The element identifier becomes the path through the exponential
//! tree to reach the element.
//!
//! LSEQ differs from Logoot in that it adds the concept of randomized
//! boundary+/- allocation strategy to prevent the tree from growing too
//! deep too quickly.
//!
//! In contrast with the LSEQ/LOGOOT approach, we use rational numbers as
//! identifiers. Where LSEQ/LOGOOT constrain themselves to the interval (0,1),
//! we expand to the entire rational number line. This removes some edge
//! cases (literally) from the allocation logic since we don't have to worry
//! about bunching up our identifiers near the edges of the interval.

//! In addition, we remove the randomization and boundary+/- allocation logic
//! introduced by LSEQ, resorting instead to choosing the midpoint between
//! adjacent identifiers when inserting.
//!
//! List is a CmRDT, to guarantee convergence it must see every operation. It also requires that
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

/// Contains the implementation of the exponential tree for List

/// A unique identifier for an element in the sequence.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub struct Identifier<A> {
    /// The id is the main ordering component of the Identifier.
    pub id: BigRational,

    /// The dot is used to disambiguate Identifiers when the id's are identical.
    pub dot: Dot<A>,
}

impl<A: Ord> PartialOrd for Identifier<A> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(&other))
    }
}

impl<A: Ord> Ord for Identifier<A> {
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
/// An List tree is a CRDT for storing sequences of data (Strings, ordered lists).
/// It provides an efficient view of the stored sequence, with fast index, insertion and deletion
/// operations.
#[derive(Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub struct List<T, A: Ord> {
    seq: BTreeMap<Identifier<A>, T>,
    clock: VClock<A>,
}

/// Operations that can be performed on a List
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Op<T, A> {
    /// Insert an element
    Insert {
        /// The Identifier to insert at
        id: Identifier<A>,
        /// Element to insert
        val: T,
    },
    /// Delete an element
    Delete {
        /// The Identifier of the insertion we're removing
        id: Identifier<A>,
        /// id of site that issued delete
        dot: Dot<A>,
    },
}

impl<T, A> Op<T, A> {
    /// Returns the Identifier this operation is concerning.
    pub fn id(&self) -> &Identifier<A> {
        match self {
            Op::Insert { id, .. } | Op::Delete { id, .. } => id,
        }
    }

    /// Return the Dot originating the operation.
    pub fn dot(&self) -> &Dot<A> {
        match self {
            Op::Insert { id, .. } => &id.dot,
            Op::Delete { dot, .. } => dot,
        }
    }
}

impl<T, A: Ord> Default for List<T, A> {
    fn default() -> Self {
        Self {
            seq: Default::default(),
            clock: Default::default(),
        }
    }
}

impl<T, A: Ord + Clone> List<T, A> {
    /// Create an empty List
    pub fn new() -> Self {
        Self::default()
    }

    /// Perform a local insertion of an element at a given position.
    /// If `ix` is greater than the length of the List then it is appended to the end.
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
            (None, Some(q)) => &q.id - &one,
            (None, None) => zero,
        };
        let dot = self.clock.inc(actor);
        let id = Identifier { id, dot };
        Op::Insert { id, val }
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
        self.seq.keys().nth(ix).cloned().map(|id| {
            let dot = self.clock.inc(actor);
            Op::Delete { id, dot }
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

    /// Get the length of the List.
    pub fn len(&self) -> usize {
        self.seq.len()
    }

    /// Check if the List is empty.
    pub fn is_empty(&self) -> bool {
        self.seq.is_empty()
    }

    /// Get the elements represented by the List.
    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.seq.values()
    }

    /// Get each elements identifier and value from the List.
    pub fn iter_entries(&self) -> impl Iterator<Item = (&Identifier<A>, &T)> {
        self.seq.iter()
    }

    /// Get an element at a position in the sequence represented by the List.
    pub fn position(&self, ix: usize) -> Option<&T> {
        self.iter().nth(ix)
    }

    /// Finds an element by its Identifier.
    pub fn get(&self, id: &Identifier<A>) -> Option<&T> {
        self.seq.get(id)
    }

    /// Get first element of the sequence represented by the List.
    pub fn first(&self) -> Option<&T> {
        self.first_entry().map(|(_, val)| val)
    }

    /// Get the first Entry of the sequence represented by the List.
    pub fn first_entry(&self) -> Option<(&Identifier<A>, &T)> {
        self.seq.iter().next()
    }

    /// Get last element of the sequence represented by the List.
    pub fn last(&self) -> Option<&T> {
        self.last_entry().map(|(_, val)| val)
    }

    /// Get the last Entry of the sequence represented by the List.
    pub fn last_entry(&self) -> Option<(&Identifier<A>, &T)> {
        self.seq.iter().rev().next()
    }

    /// Insert value with at the given identifier in the List
    fn insert(&mut self, id: Identifier<A>, val: T) {
        // Inserts only have an impact if the identifier is not in the tree
        self.seq.entry(id).or_insert(val);
    }

    /// Remove the element with the given identifier from the List
    fn delete(&mut self, id: &Identifier<A>) {
        // Deletes only have an effect if the identifier is already in the tree
        self.seq.remove(id);
    }
}

impl<T, A: Ord + Clone + fmt::Debug> CmRDT for List<T, A> {
    type Op = Op<T, A>;
    type Validation = crate::DotRange<A>;

    fn validate_op(&self, op: &Self::Op) -> Result<(), Self::Validation> {
        self.clock.validate_op(op.dot())
    }

    /// Apply an operation to an List instance.
    ///
    /// If the operation is an insert and the identifier is **already** present in the List instance
    /// the result is a no-op
    ///
    /// If the operation is a delete and the identifier is **not** present in the List instance the
    /// result is a no-op
    fn apply(&mut self, op: Self::Op) {
        let op_dot = op.dot().clone();

        if op_dot.counter <= self.clock.get(&op_dot.actor) {
            return;
        }

        self.clock.apply(op_dot);
        match op {
            Op::Insert { id, val } => self.insert(id, val),
            Op::Delete { id, .. } => self.delete(&id),
        }
    }
}
