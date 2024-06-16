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

use alloc::collections::BTreeMap;
use core::fmt;
use core::iter::FromIterator;

use serde::{Deserialize, Serialize};

use crate::{
    serde_helper::{self, SerDe},
    CmRDT, Dot, Identifier, OrdDot, VClock,
};

/// As described in the module documentation:
///
/// A List is a CRDT for storing sequences of data (Strings, ordered lists).
/// It provides an efficient view of the stored sequence, with fast index, insertion and deletion
/// operations.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub struct List<T: SerDe, A: Ord> {
    #[serde(with = "serde_helper::btreemap_as_vec")]
    seq: BTreeMap<Identifier<OrdDot<A>>, T>,
    clock: VClock<A>,
}

/// Operations that can be performed on a List
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Op<T, A: Ord> {
    /// Insert an element
    Insert {
        /// The Identifier to insert at
        id: Identifier<OrdDot<A>>,
        /// Element to insert
        val: T,
    },
    /// Delete an element
    Delete {
        /// The Identifier of the insertion we're removing
        id: Identifier<OrdDot<A>>,
        /// id of site that issued delete
        dot: Dot<A>,
    },
}

impl<T, A: Ord + Clone + Eq> Op<T, A> {
    /// Returns the Identifier this operation is concerning.
    pub fn id(&self) -> &Identifier<OrdDot<A>> {
        match self {
            Op::Insert { id, .. } | Op::Delete { id, .. } => id,
        }
    }

    /// Return the Dot originating the operation.
    pub fn dot(&self) -> Dot<A> {
        match self {
            Op::Insert { id, .. } => id.value().clone().into(),
            Op::Delete { dot, .. } => dot.clone(),
        }
    }
}

impl<T: SerDe, A: Ord> Default for List<T, A> {
    fn default() -> Self {
        Self {
            seq: Default::default(),
            clock: Default::default(),
        }
    }
}

impl<T: SerDe, A: Ord + Clone> List<T, A> {
    /// Create an empty List
    pub fn new() -> Self {
        Self::default()
    }

    /// Generate an op to insert the given element at the given index.
    /// If `ix` is greater than the length of the List then it is appended to the end.
    pub fn insert_index(&self, mut ix: usize, val: T, actor: A) -> Op<T, A> {
        ix = ix.min(self.seq.len());
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

        let dot = self.clock.inc(actor);
        let id = Identifier::between(prev, next, dot.into());
        Op::Insert { id, val }
    }

    /// Create an op to insert an element at the end of the sequence.
    pub fn append(&self, c: T, actor: A) -> Op<T, A> {
        let ix = self.seq.len();
        self.insert_index(ix, c, actor)
    }

    /// Create an op to delete the element at the given index.
    ///
    /// Returns None if `ix` is out of bounds, i.e. `ix > self.len()`.
    pub fn delete_index(&self, ix: usize, actor: A) -> Option<Op<T, A>> {
        self.seq.keys().nth(ix).cloned().map(|id| {
            let dot = self.clock.inc(actor);
            Op::Delete { id, dot }
        })
    }

    /// Get the length of the List.
    pub fn len(&self) -> usize {
        self.seq.len()
    }

    /// Check if the List is empty.
    pub fn is_empty(&self) -> bool {
        self.seq.is_empty()
    }

    /// Read the List into a container of your choice
    ///
    /// ```rust
    /// use crdts::{List, CmRDT};
    ///
    /// let mut list = List::new();
    /// list.apply(list.append('a', 'A'));
    /// list.apply(list.append('b', 'A'));
    /// list.apply(list.append('c', 'A'));
    /// assert_eq!(list.read::<String>(), "abc");
    /// ```
    pub fn read<'a, C: FromIterator<&'a T>>(&'a self) -> C {
        self.seq.values().collect()
    }

    /// Read the List into a container of your choice, consuming it.
    ///
    /// ```rust
    /// use crdts::{List, CmRDT};
    ///
    /// let mut list = List::new();
    /// list.apply(list.append(1, 'A'));
    /// list.apply(list.append(2, 'A'));
    /// list.apply(list.append(3, 'A'));
    /// assert_eq!(list.read_into::<Vec<_>>(), vec![1, 2, 3]);
    /// ```
    pub fn read_into<C: FromIterator<T>>(self) -> C {
        self.seq.into_values().collect()
    }

    /// Get the elements represented by the List.
    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.seq.values()
    }

    /// Get each elements identifier and value from the List.
    pub fn iter_entries(&self) -> impl Iterator<Item = (&Identifier<OrdDot<A>>, &T)> {
        self.seq.iter()
    }

    /// Get an element at a position in the sequence represented by the List.
    pub fn position(&self, ix: usize) -> Option<&T> {
        self.iter().nth(ix)
    }

    /// Find an identifer by an index.
    pub fn position_entry(&self, id: &Identifier<OrdDot<A>>) -> Option<usize> {
        self.iter_entries()
            .enumerate()
            .find_map(|(ix, (ident, _))| if ident == id { Some(ix) } else { None })
    }

    /// Finds an element by its Identifier.
    pub fn get(&self, id: &Identifier<OrdDot<A>>) -> Option<&T> {
        self.seq.get(id)
    }

    /// Get first element of the sequence represented by the List.
    pub fn first(&self) -> Option<&T> {
        self.first_entry().map(|(_, val)| val)
    }

    /// Get the first Entry of the sequence represented by the List.
    pub fn first_entry(&self) -> Option<(&Identifier<OrdDot<A>>, &T)> {
        self.seq.iter().next()
    }

    /// Get last element of the sequence represented by the List.
    pub fn last(&self) -> Option<&T> {
        self.last_entry().map(|(_, val)| val)
    }

    /// Get the last Entry of the sequence represented by the List.
    pub fn last_entry(&self) -> Option<(&Identifier<OrdDot<A>>, &T)> {
        self.seq.iter().next_back()
    }

    /// Insert value with at the given identifier in the List
    fn insert(&mut self, id: Identifier<OrdDot<A>>, val: T) {
        // Inserts only have an impact if the identifier is not in the tree
        self.seq.entry(id).or_insert(val);
    }

    /// Remove the element with the given identifier from the List
    fn delete(&mut self, id: &Identifier<OrdDot<A>>) {
        // Deletes only have an effect if the identifier is already in the tree
        self.seq.remove(id);
    }
}

impl<T: SerDe, A: Ord + Clone + fmt::Debug> CmRDT for List<T, A> {
    type Op = Op<T, A>;
    type Validation = crate::DotRange<A>;

    fn validate_op(&self, op: &Self::Op) -> Result<(), Self::Validation> {
        self.clock.validate_op(&op.dot())
    }

    /// Apply an operation to an List instance.
    ///
    /// If the operation is an insert and the identifier is **already** present in the List instance
    /// the result is a no-op
    ///
    /// If the operation is a delete and the identifier is **not** present in the List instance the
    /// result is a no-op
    fn apply(&mut self, op: Self::Op) {
        let op_dot = op.dot();

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

impl<T: SerDe, A: Ord> IntoIterator for List<T, A> {
    type Item = T;

    type IntoIter = alloc::collections::btree_map::IntoValues<Identifier<OrdDot<A>>, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.seq.into_values()
    }
}
