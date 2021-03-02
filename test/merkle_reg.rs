use std::collections::BTreeSet;

use crdts::merkle_reg::{MerkleReg, Node};
use crdts::{CmRDT, CvRDT};

use quickcheck_macros::quickcheck;

#[test]
fn test_write_resolves_fork() {
    let mut reg = MerkleReg::new();

    reg.apply(reg.write("a", Default::default()));
    reg.apply(reg.write("b", Default::default()));

    let contents = reg.read();
    assert_eq!(contents.values().collect::<Vec<_>>(), vec![&&"a", &&"b"]);

    let parents = contents.hashes();
    reg.apply(reg.write("c", parents));

    let contents = reg.read();
    assert_eq!(contents.values().collect::<Vec<_>>(), vec![&&"c"]);
}

#[test]
fn test_orphaned_nodes_grows_if_ops_are_applied_backwards() {
    let mut reg: MerkleReg<String> = MerkleReg::new();
    let mut ops = Vec::new();

    let mut parents = BTreeSet::new();
    for val in ["a", "b", "c", "d"].iter() {
        let op = reg.write(val.to_string(), parents);
        parents = vec![op.hash()].into_iter().collect();
        ops.push(op);
    }

    // As we apply op's back to front, the number of orphaned nodes increases and
    // the contents of the register remains empty.
    let op_d = ops.pop().unwrap();
    reg.apply(op_d);
    assert!(reg.read().is_empty());
    assert_eq!(reg.num_orphans(), 1);

    let op_c = ops.pop().unwrap();
    reg.apply(op_c);
    assert!(reg.read().is_empty());
    assert_eq!(reg.num_orphans(), 2);

    let op_b = ops.pop().unwrap();
    reg.apply(op_b);
    assert!(reg.read().is_empty());
    assert_eq!(reg.num_orphans(), 3);

    // Once the first node is applied, all other nodes will no longer be orphaned.
    let op_a = ops.pop().unwrap();
    reg.apply(op_a);
    assert_eq!(reg.read().values().collect::<Vec<_>>(), vec![&&"d"]);
    assert_eq!(reg.num_orphans(), 0);
}

#[quickcheck]
fn prop_op_reordering_converges(
    concurrent_writes: Vec<Vec<(String, Vec<usize>)>>,
    mut op_reordering: Vec<usize>,
) {
    let mut reg = MerkleReg::new();
    let mut ops: Vec<Node<_>> = Vec::new();

    for writes in concurrent_writes {
        let mut concurrent_ops = Vec::new();
        for (value, parent_indices) in writes {
            let mut parents = BTreeSet::new();
            if !ops.is_empty() {
                for parent_index in parent_indices {
                    parents.insert(ops[parent_index % ops.len()].hash());
                }
            }
            concurrent_ops.push(reg.write(value, parents));
        }
        for op in concurrent_ops {
            ops.push(op.clone());
            reg.apply(op);
        }
    }

    let mut reordered_reg = MerkleReg::new();
    op_reordering.push(0);
    let mut op_order = op_reordering.into_iter().cycle();
    while !ops.is_empty() {
        if let Some(idx) = op_order.next() {
            let op = ops.remove(idx % ops.len());
            reordered_reg.apply(op);
        }
    }

    assert_eq!(reg, reordered_reg);
    assert_eq!(reordered_reg.num_orphans(), 0);
}

#[quickcheck]
fn prop_merge_commute(mut reg_a: MerkleReg<String>, mut reg_b: MerkleReg<String>) {
    let reg_a_snapshot = reg_a.clone();

    // a * b
    reg_a.merge(reg_b.clone());

    // b * a
    reg_b.merge(reg_a_snapshot);

    assert_eq!(reg_a, reg_b);
}

#[quickcheck]
fn prop_merge_associative(
    mut reg_a: MerkleReg<String>,
    mut reg_b: MerkleReg<String>,
    reg_c: MerkleReg<String>,
) {
    let mut reg_a_snapshot = reg_a.clone();

    // (a * b) * c
    reg_a.merge(reg_b.clone());
    reg_a.merge(reg_c.clone());

    // a * (b * c)
    reg_b.merge(reg_c);
    reg_a_snapshot.merge(reg_b);

    // (a * b) * c == a * (b * c)
    assert_eq!(reg_a, reg_a_snapshot);
}
