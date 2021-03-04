use core::{convert::Infallible, fmt};
use quickcheck::{Arbitrary, Gen};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};
use tiny_keccak::{Hasher, Sha3};

use crate::traits::{CmRDT, CvRDT};

/// The hash of a node
pub type Hash = [u8; 32];

/// A node in the Merkle DAG
#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Node<T> {
    /// The parent nodes, addressed by their hash.
    pub parents: BTreeSet<Hash>,
    /// The value stored at this node.
    pub value: T,
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

/// The nodes of a MerkleReg.
pub struct ContentNode<'a, T> {
    reg: &'a MerkleReg<T>,
    node: &'a Node<T>,
}

impl<'a, T> ContentNode<'a, T> {
    /// Returns the parents of this node
    pub fn parents(&self) -> Content<T> {
        Content {
            reg: self.reg,
            nodes: self
                .node
                .parents
                .iter()
                .filter_map(|hash| self.reg.node(*hash).map(|parent| (*hash, parent)))
                .collect(),
        }
    }

    /// Returns the value held by this node
    pub fn value(&self) -> &T {
        &self.node.value
    }
}

/// The contents of a MerkleReg.
///
/// Usually this is retrieved through a call to `MerkleReg::read`
pub struct Content<'a, T> {
    reg: &'a MerkleReg<T>,
    nodes: BTreeMap<Hash, &'a Node<T>>,
}

impl<'a, T> Content<'a, T> {
    /// Checks if the contents is empty
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Returns the number of nodes referenced by this content
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Returns the list of Merkle DAG nodes holding their hashes and values.
    pub fn nodes(&self) -> Vec<ContentNode<'a, T>> {
        self.nodes
            .iter()
            .map(|(_, n)| ContentNode {
                reg: self.reg,
                node: n,
            })
            .collect()
    }

    /// Returns the set of hashes of the content values.
    pub fn hashes(&self) -> BTreeSet<Hash> {
        self.nodes.keys().copied().collect()
    }

    /// Iterate over the content values
    pub fn values(&self) -> impl Iterator<Item = &T> {
        self.nodes.values().map(|n| &n.value)
    }

    /// Iterate over the hashes of the content values.
    pub fn hashes_and_nodes(&self) -> impl Iterator<Item = (&Hash, &Node<T>)> {
        self.nodes.iter().map(|(hash, node)| (hash, *node))
    }
}

/// The MerkleReg is a Register CRDT that uses the Merkle DAG
/// structure to track the current value(s) held by this register.
/// The leaves of the Merkle DAG are the current values.
#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct MerkleReg<T> {
    leaves: BTreeSet<Hash>,
    dag: BTreeMap<Hash, Node<T>>,
    orphans: BTreeMap<Hash, Node<T>>,
}

impl<T> Default for MerkleReg<T> {
    fn default() -> Self {
        Self {
            leaves: Default::default(),
            dag: Default::default(),
            orphans: Default::default(),
        }
    }
}

impl<T> MerkleReg<T> {
    /// Return a new instance of the MerkleReg
    pub fn new() -> Self {
        Default::default()
    }

    /// Read the current values held by the register
    pub fn read(&self) -> Content<T> {
        Content {
            nodes: self
                .leaves
                .iter()
                .filter_map(|leaf| self.dag.get(leaf).map(|node| (*leaf, node)))
                .collect(),
            reg: self,
        }
    }

    /// Write the given value on top of the given parents.
    pub fn write(&self, value: T, parents: BTreeSet<Hash>) -> Node<T> {
        Node { value, parents }
    }

    /// Retrieve a node in the Merkle DAG by it's hash.
    ///
    /// Traverse the history the register by pair this method with the parents
    /// of the nodes retrieved in Content::nodes().
    pub fn node(&self, hash: Hash) -> Option<&Node<T>> {
        self.dag.get(&hash).or_else(|| self.orphans.get(&hash))
    }

    /// Returns the number of nodes who are visible, i.e. their parents have been seen.
    pub fn num_nodes(&self) -> usize {
        self.dag.len()
    }

    /// Returns the number of nodes who are not visible due to missing parents.
    pub fn num_orphans(&self) -> usize {
        self.orphans.len()
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

    fn validate_op(&self, op: &Self::Op) -> Result<(), Self::Validation> {
        for parent in op.parents.iter() {
            if !self.dag.contains_key(parent) {
                return Err(ValidationError::MissingParent(*parent));
            }
        }
        Ok(())
    }

    fn apply(&mut self, node: Self::Op) {
        let node_hash = node.hash();
        if self.dag.contains_key(&node_hash) || self.orphans.contains_key(&node_hash) {
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

            // Now check if inserting this node resolves any orphans nodes.
            // TODO: replace this logic with BTreeMap::drain_filter once it's stable.
            let hashes_that_are_now_ready_to_apply = self
                .orphans
                .iter()
                .filter(|(_, node)| self.all_hashes_seen(&node.parents))
                .map(|(hash, _)| hash)
                .copied()
                .collect::<Vec<_>>();

            let mut nodes_to_apply = Vec::new();
            for hash in hashes_that_are_now_ready_to_apply {
                // Remove the previously orphaned nodes that are now
                // ready to apply before we recurse, else we risk an
                // exponential growth in memory.
                if let Some(node) = self.orphans.remove(&hash) {
                    nodes_to_apply.push(node);
                }
            }

            for node in nodes_to_apply {
                self.apply(node);
            }
        } else {
            self.orphans.insert(node_hash, node);
        }
    }
}

impl<T: Sha3Hash> CvRDT for MerkleReg<T> {
    type Validation = Infallible;

    fn validate_merge(&self, _: &Self) -> Result<(), Self::Validation> {
        Ok(())
    }

    fn merge(&mut self, other: Self) {
        let MerkleReg { dag, orphans, .. } = other;
        for (_, node) in dag {
            self.apply(node);
        }
        for (_, node) in orphans {
            self.apply(node);
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

impl<T: Arbitrary + Sha3Hash> Arbitrary for MerkleReg<T> {
    fn arbitrary<G: Gen>(g: &mut G) -> Self {
        let mut reg = MerkleReg::new();
        let mut nodes: Vec<Node<_>> = Vec::new();

        let n_nodes = u8::arbitrary(g) % 12;
        for _ in 0..n_nodes {
            let value = T::arbitrary(g);
            let mut parents = BTreeSet::new();
            if !nodes.is_empty() {
                let n_parents = u8::arbitrary(g) % 12;
                for _ in 0..n_parents {
                    parents.insert(nodes[usize::arbitrary(g) % nodes.len()].hash());
                }
            }
            let op = reg.write(value, parents);
            nodes.push(op.clone());
            reg.apply(op)
        }

        reg
    }
}
