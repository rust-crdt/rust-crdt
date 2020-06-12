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

/// Contains the implementation of the exponential tree for LSeq
pub mod ident;

use ident::{IdentGen, Identifier};
use serde::{Deserialize, Serialize};

use crate::{Actor, CmRDT, Dot};

/// An `Entry` to the LSEQ consists of:
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash, PartialOrd)]
pub struct Entry<T, A: Actor> {
    /// The identifier of the entry.
    pub id: Identifier<A>,
    /// The site id that inserted this entry.
    pub dot: Dot<A>,
    /// The element for the entry.
    pub val: T,
}

/// As described in the module documentation:
///
/// An LSEQ tree is a CRDT for storing sequences of data (Strings, ordered lists).
/// It provides an efficient view of the stored sequence, with fast index, insertion and deletion
/// operations.
#[derive(Clone, Serialize, Deserialize, PartialEq, Eq, Hash, PartialOrd)]
pub struct LSeq<T, A: Actor> {
    seq: Vec<Entry<T, A>>,
    gen: IdentGen<A>,
    dot: Dot<A>,
}

/// Operations that can be performed on an LSeq tree
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash, PartialOrd)]
pub enum Op<T, A: Actor> {
    /// Insert an element
    Insert {
        /// Identifier to insert at
        id: Identifier<A>,
        /// clock of site that issued insertion
        dot: Dot<A>,
        /// Element to insert
        val: T,
    },
    /// Delete an element
    Delete {
        /// The original clock information of the insertion we're removing
        remote: Dot<A>,
        /// Identifier to remove
        id: Identifier<A>,
        /// id of site that issued delete
        dot: Dot<A>,
    },
}

impl<T: Clone, A: Actor> LSeq<T, A> {
    /// Create an empty LSEQ
    pub fn new(id: A) -> Self {
        LSeq {
            seq: Vec::new(),
            gen: IdentGen::new(id.clone()),
            dot: Dot::new(id, 0),
        }
    }

    /// Create an empty LSEQ with custom base size
    pub fn new_with_args(id: A, base: u8, boundary: u64) -> Self {
        LSeq {
            seq: Vec::new(),
            gen: IdentGen::new_with_args(id.clone(), base, boundary),
            dot: Dot::new(id, 0),
        }
    }

    /// Perform a local insertion of an element at a given position.
    /// If `ix` is greater than the length of the LSeq then it is appended to the end.
    ///
    /// # Panics
    ///
    /// * If the allocation of a new index was not between `ix` and `ix - 1`.
    pub fn insert_index(&mut self, ix: usize, val: T) -> Op<T, A> {
        let min_id = self.gen.lower();
        let max_id = self.gen.upper();

        // If we're inserting past the length of the LSEQ then it's the same as appending.
        let (lower_id, upper_id) = if self.seq.len() <= ix {
            let prev = self.seq.last().map(|entry| &entry.id).unwrap_or(&min_id);
            (prev, &max_id)
        } else {
            // To insert an element at position ix, we want it to appear in the sequence between
            // ix - 1 and ix. To do this, retrieve each bound defaulting to the lower and upper
            // bounds respectively if they are not found.
            let prev = match ix.checked_sub(1) {
                Some(i) => &self.seq[i].id,
                None => &min_id,
            };
            let next = self.seq.get(ix).map(|entry| &entry.id).unwrap_or(&max_id);

            (prev, next)
        };

        let ix_ident = self.gen.alloc(&lower_id, &upper_id);

        assert!(lower_id < &ix_ident);
        assert!(&ix_ident < upper_id);

        let op = Op::Insert {
            id: ix_ident,
            dot: self.dot.clone(),
            val,
        };
        // TODO: refactor to follow the library API (don't apply ops immediately)
        self.dot.counter += 1;
        self.apply(op.clone());
        op
    }

    /// Perform a local insertion of an element at the end of the sequence.
    pub fn append(&mut self, c: T) -> Op<T, A> {
        let ix = self.seq.len();
        self.insert_index(ix, c)
    }

    /// Perform a local deletion at `ix`.
    ///
    /// If `ix` is out of bounds, i.e. `ix > self.len()`, then
    /// the `Op` is not performed and `None` is returned.
    pub fn delete_index(&mut self, ix: usize) -> Option<Op<T, A>> {
        if ix >= self.seq.len() {
            return None;
        }

        let data = self.seq[ix].clone();

        let op = Op::Delete {
            id: data.id,
            remote: data.dot,
            dot: self.dot.clone(),
        };

        self.dot.counter += 1;
        self.apply(op.clone());

        Some(op)
    }

    /// Perform a local deletion at `ix`. If `ix` is out of bounds
    /// then the last element will be deleted, i.e. `self.len() - 1`.
    pub fn delete_index_or_last(&mut self, ix: usize) -> Op<T, A> {
        match self.delete_index(ix) {
            None => self
                .delete_index(self.len() - 1)
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
    pub fn iter(&self) -> impl Iterator<Item = &T> + '_ {
        self.seq.iter().map(|Entry { val, .. }| val)
    }

    /// Get an element at an index from the sequence represented by the LSEQ.
    pub fn get(&self, ix: usize) -> Option<&T> {
        self.seq.get(ix).map(|Entry { val, .. }| val)
    }

    /// Get last element of the sequence represented by the LSEQ.
    pub fn last(&self) -> Option<&T> {
        self.seq.last().map(|Entry { val, .. }| val)
    }

    /// Actor who is initiating operations on this LSeq
    pub fn actor(&self) -> A {
        self.dot.actor.clone()
    }

    /// Insert an identifier and value in the LSEQ
    fn insert(&mut self, ix: Identifier<A>, dot: Dot<A>, val: T) {
        // Inserts only have an impact if the identifier is not in the tree
        if let Err(res) = self.seq.binary_search_by(|e| e.id.cmp(&ix)) {
            self.seq.insert(res, Entry { id: ix, dot, val });
        }
    }

    /// Remove an identifier from the LSEQ
    fn delete(&mut self, ix: Identifier<A>) {
        // Deletes only have an effect if the identifier is already in the tree
        if let Ok(i) = self.seq.binary_search_by(|e| e.id.cmp(&ix)) {
            self.seq.remove(i);
        }
    }
}

impl<T: Clone, A: Actor> CmRDT for LSeq<T, A> {
    type Op = Op<T, A>;
    /// Apply an operation to an LSeq instance.
    ///
    /// If the operation is an insert and the identifier is **already** present in the LSEQ instance
    /// the result is a no-op
    ///
    /// If the operation is a delete and the identifier is **not** present in the LSEQ instance the
    /// result is a no-op
    fn apply(&mut self, op: Self::Op) {
        match op {
            Op::Insert { id, dot, val } => self.insert(id, dot, val),
            Op::Delete { id, .. } => self.delete(id),
        }
    }
}
