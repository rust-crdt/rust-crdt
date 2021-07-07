use core::convert::Infallible;
use core::fmt;
use std::collections::{BTreeMap, BTreeSet};

use quickcheck::{Arbitrary, Gen};
use serde::{Deserialize, Serialize};
use tiny_keccak::{Hasher, Sha3};

use crate::traits::{CmRDT, CvRDT};

/// The hash of a node
pub type Hash = [u8; 32];

/// A node in the Merkle DAG
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Node<T> {
    /// The child nodes, addressed by their hash.
    pub children: BTreeSet<Hash>,
    /// The value stored at this node.
    pub value: T,
}

impl<T: Sha3Hash> Node<T> {
    /// Compute the hash name of this node.
    ///
    /// hash = sha3_256(child1 <> child2 <> .. <> childN <> value)
    ///
    /// Where children are ordered lexigraphically.
    pub fn hash(&self) -> Hash {
        let mut sha3 = Sha3::v256();

        self.children.iter().for_each(|c| sha3.update(c));
        self.value.hash(&mut sha3);

        let mut hash = [0u8; 32];
        sha3.finalize(&mut hash);
        hash
    }
}

/// The contents of a MerkleReg.
///
/// Usually this is retrieved through a call to `MerkleReg::read`
pub struct Content<'a, T> {
    nodes: BTreeMap<Hash, &'a Node<T>>,
}

impl<'a, T> Content<'a, T> {
    /// Checks if the contents is empty
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Iterate over the content values
    pub fn values(&self) -> impl Iterator<Item = &T> {
        self.nodes.values().map(|n| &n.value)
    }

    /// Iterate over the Merkle DAG nodes holding the content values.
    pub fn nodes(&self) -> impl Iterator<Item = &Node<T>> {
        self.nodes.values().copied()
    }

    /// Iterate over the hashes of the content values.
    pub fn hashes(&self) -> BTreeSet<Hash> {
        self.nodes.keys().copied().collect()
    }

    /// Iterate over the hashes of the content values.
    pub fn hashes_and_nodes(&self) -> impl Iterator<Item = (Hash, &Node<T>)> {
        self.nodes.iter().map(|(hash, node)| (*hash, *node))
    }
}

/// The MerkleReg is a Register CRDT that uses the Merkle DAG
/// structure to track the current value(s) held by this register.
/// The roots of the Merkle DAG are the current concurrent values.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct MerkleReg<T> {
    roots: BTreeSet<Hash>,
    dag: BTreeMap<Hash, Node<T>>,
    orphans: BTreeMap<Hash, Node<T>>,
}

impl<T> Default for MerkleReg<T> {
    fn default() -> Self {
        Self {
            roots: Default::default(),
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
                .roots
                .iter()
                .copied()
                .filter_map(|root| self.dag.get(&root).map(|node| (root, node)))
                .collect(),
        }
    }

    /// Write the given value on top of the given children.
    pub fn write(&self, value: T, children: BTreeSet<Hash>) -> Node<T> {
        Node { value, children }
    }

    /// Retrieve a node in the Merkle DAG by it's hash.
    ///
    /// Traverse the history of the register by pairing this method
    /// with the children of the nodes retrieved in Content::nodes().
    pub fn node(&self, hash: Hash) -> Option<&Node<T>> {
        self.dag.get(&hash).or_else(|| self.orphans.get(&hash))
    }

    /// Returns the children of a node
    pub fn children(&self, hash: Hash) -> Content<T> {
        let nodes = self.dag.get(&hash).map(|node| {
            node.children
                .iter()
                .copied()
                .filter_map(|child| self.dag.get(&child).map(|node| (child, node)))
                .collect()
        });

        Content {
            nodes: nodes.unwrap_or_default(),
        }
    }

    /// Returns the parents of a node
    pub fn parents(&self, hash: Hash) -> Content<T> {
        let parents = self
            .dag
            .iter()
            .filter_map(|(h, node)| {
                if node.children.contains(&hash) {
                    Some((*h, node))
                } else {
                    None
                }
            })
            .collect();

        Content { nodes: parents }
    }

    /// Returns the number of nodes who are visible, i.e. their children have been seen.
    pub fn num_nodes(&self) -> usize {
        self.dag.len()
    }

    /// Returns the number of nodes who are not visible due to missing children.
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
    /// The Op is attempting to insert a node with a child we
    /// haven't seen yet.
    MissingChild(Hash),
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
        for child in op.children.iter() {
            if !self.dag.contains_key(child) {
                return Err(ValidationError::MissingChild(*child));
            }
        }
        Ok(())
    }

    fn apply(&mut self, node: Self::Op) {
        let node_hash = node.hash();
        if self.dag.contains_key(&node_hash) || self.orphans.contains_key(&node_hash) {
            return;
        }

        if self.all_hashes_seen(&node.children) {
            // Any children who happen to be roots will no longer be roots
            // after this node is inserted.
            for child in node.children.iter() {
                self.roots.remove(child);
            }

            // Since we have never seen this node before, it's guaranteed to be a root.
            self.roots.insert(node_hash);

            // It is now safe to insert this node into the DAG since we've seen its children.
            self.dag.insert(node_hash, node);

            // Now check if inserting this node resolves any orphans nodes.
            // TODO: replace this logic with BTreeMap::drain_filter once it's stable.
            let hashes_that_are_now_ready_to_apply = self
                .orphans
                .iter()
                .filter(|(_, node)| self.all_hashes_seen(&node.children))
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
            let mut children = BTreeSet::new();
            if !nodes.is_empty() {
                let n_children = u8::arbitrary(g) % 12;
                for _ in 0..n_children {
                    children.insert(nodes[usize::arbitrary(g) % nodes.len()].hash());
                }
            }
            let op = reg.write(value, children);
            nodes.push(op.clone());
            reg.apply(op)
        }

        reg
    }
}
