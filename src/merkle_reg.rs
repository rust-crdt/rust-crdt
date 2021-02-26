use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use tiny_keccak::{Hasher, Sha3};

use crate::traits::CmRDT;

type Hash = [u8; 32];

/// A node in the Merkle DAG
pub struct Node<T> {
    parents: BTreeSet<Hash>,
    value: T,
}

impl<T: Sha3Hash> Node<T> {
    fn hash(&self) -> Hash {
        let mut sha3 = Sha3::v256();

        self.parents.iter().for_each(|p| sha3.update(p));
        self.value.hash(&mut sha3);

        let mut hash = [0u8; 32];
        sha3.finalize(&mut hash);
        hash
    }
}

/// The MerkleReg is a Register CRDT that uses the Merkle DAG
/// structure to track the current value(s) held by this register.
/// The leaves of the Merkle DAG are the current values.
pub struct MerkleReg<T> {
    leaves: BTreeSet<Hash>,
    dag: BTreeMap<Hash, Node<T>>,
}

impl<T> Default for MerkleReg<T> {
    fn default() -> Self {
        Self {
            leaves: Default::default(),
            dag: Default::default(),
        }
    }
}

impl<T> MerkleReg<T> {
    /// Return a new instance of the MerkleReg
    pub fn new() -> Self {
        Default::default()
    }

    /// Read the current values held by the register
    pub fn read(&self) -> BTreeMap<Hash, &T> {
        self.leaves
            .iter()
            .copied()
            .filter_map(|leaf| self.dag.get(&leaf).map(|node| (leaf, &node.value)))
            .collect()
    }

    /// Write the given value on top of the given parents.
    pub fn write(&self, value: T, parents: BTreeSet<Hash>) -> Node<T> {
        Node { value, parents }
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
        if self.dag.contains_key(&node_hash) {
            return;
        }

        for parent in node.parents.iter() {
            self.leaves.remove(parent);
        }

        self.leaves.insert(node_hash);
        self.dag.insert(node_hash, node);
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
