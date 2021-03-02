use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use tiny_keccak::{Hasher, Sha3};

use crate::traits::CmRDT;

type Hash = [u8; 32];

/// A node in the Merkle DAG
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Node<T> {
    parents: BTreeSet<Hash>,
    value: T,
}

impl<T: Sha3Hash> Node<T> {
    /// Compute the hash name of this node.
    ///
    /// hash = sha3_256(parent1 <> parent2 <> .. <> parentN <> value)
    ///
    /// Where parents are ordered lexigraphically.
    pub fn hash(&self) -> Hash {
        let mut sha3 = Sha3::v256();

        self.parents.iter().for_each(|p| sha3.update(p));
        self.value.hash(&mut sha3);

        let mut hash = [0u8; 32];
        sha3.finalize(&mut hash);
        hash
    }
}

/// The contents of a MerkleReg.
///
/// Usually this is retrieved through a call to `MerkleReg::read`
pub struct Content<T> {
    hashes_and_values: BTreeMap<Hash, T>,
}

impl<T> Content<T> {
    /// Checks if the contents is empty
    pub fn is_empty(&self) -> bool {
        self.hashes_and_values.is_empty()
    }

    /// Iterate over the content values
    pub fn values(&self) -> impl Iterator<Item = &T> {
        self.hashes_and_values.values()
    }

    /// Iterate over the hashes of the content values.
    pub fn hashes(&self) -> BTreeSet<Hash> {
        self.hashes_and_values.keys().copied().collect()
    }

    /// The concurrent hashes and values stored in the register
    pub fn hashes_and_values(&self) -> &BTreeMap<Hash, T> {
        &self.hashes_and_values
    }
}

/// The MerkleReg is a Register CRDT that uses the Merkle DAG
/// structure to track the current value(s) held by this register.
/// The leaves of the Merkle DAG are the current values.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct MerkleReg<T> {
    leaves: BTreeSet<Hash>,
    dag: BTreeMap<Hash, Node<T>>,
    orphaned: BTreeMap<Hash, Node<T>>,
}

impl<T> Default for MerkleReg<T> {
    fn default() -> Self {
        Self {
            leaves: Default::default(),
            dag: Default::default(),
            orphaned: Default::default(),
        }
    }
}

impl<T> MerkleReg<T> {
    /// Return a new instance of the MerkleReg
    pub fn new() -> Self {
        Default::default()
    }

    /// Read the current values held by the register
    pub fn read(&self) -> Content<&T> {
        Content {
            hashes_and_values: self
                .leaves
                .iter()
                .copied()
                .filter_map(|leaf| self.dag.get(&leaf).map(|node| (leaf, &node.value)))
                .collect(),
        }
    }

    /// Write the given value on top of the given parents.
    pub fn write(&self, value: T, parents: BTreeSet<Hash>) -> Node<T> {
        Node { value, parents }
    }

    /// Returns the number of nodes who are not visible due to missing parents.
    pub fn num_orphaned(&self) -> usize {
        self.orphaned.len()
    }

    fn all_hashes_seen(&self, hashes: &BTreeSet<Hash>) -> bool {
        hashes.iter().all(|h| self.dag.contains_key(h))
    }
}

/// Validation errors that may occur when applying or merging MerkleReg
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ValidationError {
    /// The Op is attempting to insert a node with a parent we
    /// haven't seen yet.
    MissingParent(Hash),
}

impl fmt::Display for ValidationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self, f)
    }
}

impl std::error::Error for ValidationError {}

impl<T: Sha3Hash> CmRDT for MerkleReg<T> {
    type Op = Node<T>;
    type Validation = ValidationError;

    fn validate_op(&self, op: &Self::Op) -> Result<(), ValidationError> {
        for parent in op.parents.iter() {
            if !self.dag.contains_key(parent) {
                return Err(ValidationError::MissingParent(*parent));
            }
        }
        Ok(())
    }

    fn apply(&mut self, node: Self::Op) {
        let node_hash = node.hash();
        if self.dag.contains_key(&node_hash) || self.orphaned.contains_key(&node_hash) {
            return;
        }

        if self.all_hashes_seen(&node.parents) {
            // This node will supercede any parents who happen to be leaves.
            for parent in node.parents.iter() {
                self.leaves.remove(parent);
            }

            // Since we have never seen this node before, it's guaranteed to be a leaf.
            self.leaves.insert(node_hash);

            // It's safe to insert this node into the DAG since we've seen all parents already
            self.dag.insert(node_hash, node);

            // TODO: replace this logic with BTreeMap::drain_filter once it's stable.
            let hashes_that_are_now_ready_to_apply = self
                .orphaned
                .iter()
                .filter(|(_, node)| self.all_hashes_seen(&node.parents))
                .map(|(hash, _)| hash)
                .copied()
                .collect::<BTreeSet<_>>();

            let mut nodes_to_apply = Vec::new();
            for hash in hashes_that_are_now_ready_to_apply {
                if let Some(node) = self.orphaned.remove(&hash) {
                    nodes_to_apply.push(node);
                }
            }

            for node in nodes_to_apply {
                self.apply(node);
            }
        } else {
            self.orphaned.insert(node_hash, node);
        }
    }
}

/// Values in the MerkleReg must be hasheable
/// with tiny_keccak::Sha3.
pub trait Sha3Hash {
    /// Update the hasher with self's data
    fn hash(&self, hasher: &mut Sha3);
}

// Blanket implementation for anything that can be converted to &[u8]
impl<T: AsRef<[u8]>> Sha3Hash for T {
    fn hash(&self, hasher: &mut Sha3) {
        hasher.update(self.as_ref());
    }
}
