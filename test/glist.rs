use num::BigRational;

use crdts::glist::{GList, Op};
use crdts::{CmRDT, CvRDT, Identifier};
use quickcheck_macros::quickcheck;

#[test]
fn test_concurrent_inserts_with_same_identifier_can_be_split() {
    let mut list = GList::new();
    let op_a = list.insert_after(None, 'a');
    let op_b = list.insert_after(None, 'b');

    list.apply(op_a);
    list.apply(op_b);

    assert_eq!(list.read::<String>(), "ab");
    let a_entry = list.get(0);
    assert_eq!(a_entry.map(|e| e.value()), Some(&'a'));
    let op_c = list.insert_after(a_entry, 'c');
    list.apply(op_c);

    println!("{}", list);
    assert_eq!(list.read::<String>(), "acb");
}

#[test]
fn test_append_increments_entry() {
    let mut glist: GList<char> = Default::default();

    glist.apply(glist.insert_after(glist.last(), 'a'));
    glist.apply(glist.insert_after(glist.last(), 'b'));
    glist.apply(glist.insert_after(glist.last(), 'c'));
    assert_eq!(
        vec![
            Identifier::from((BigRational::from_integer(0.into()), 'a')),
            Identifier::from((BigRational::from_integer(1.into()), 'b')),
            Identifier::from((BigRational::from_integer(2.into()), 'c')),
        ],
        glist.iter().cloned().collect::<Vec<_>>()
    );
    println!("{:?}", glist);
    assert_eq!("abc", glist.read::<String>());
}

#[test]
fn test_insert_at_front() {
    let mut glist: GList<u8> = Default::default();

    let op = glist.insert_before(glist.first(), 0);
    glist.apply(op);

    let op = glist.insert_before(glist.first(), 1);
    glist.apply(op);

    println!("{:?}", glist);
    assert_eq!(vec![&1, &0], glist.read::<Vec<_>>());
}

#[quickcheck]
fn prop_ops_commute(ops_a: Vec<Op<u8>>, ops_b: Vec<Op<u8>>) {
    let mut glist_a = GList::new();
    let mut glist_b = GList::new();

    for op in ops_a.clone() {
        assert!(glist_a.validate_op(&op).is_ok());
        glist_a.apply(op)
    }
    for op in ops_b.clone() {
        assert!(glist_b.validate_op(&op).is_ok());
        glist_b.apply(op)
    }
    // Deliver the ops to each other
    for op in ops_a {
        assert!(glist_b.validate_op(&op).is_ok());
        glist_b.apply(op)
    }
    for op in ops_b {
        assert!(glist_a.validate_op(&op).is_ok());
        glist_a.apply(op)
    }

    assert_eq!(glist_a, glist_b);
}

#[quickcheck]
fn prop_ops_are_associative(ops_a: Vec<Op<u8>>, ops_b: Vec<Op<u8>>, ops_c: Vec<Op<u8>>) {
    let mut glist_a = GList::new();
    let mut glist_b = GList::new();
    let mut glist_c = GList::new();

    for op in ops_a.clone() {
        assert!(glist_a.validate_op(&op).is_ok());
        glist_a.apply(op);
    }
    for op in ops_b.clone() {
        assert!(glist_b.validate_op(&op).is_ok());
        glist_b.apply(op);
    }
    for op in ops_c.clone() {
        assert!(glist_c.validate_op(&op).is_ok());
        glist_c.apply(op);
    }

    // a * b
    let mut glist_ab = glist_a;
    for op in ops_b.clone() {
        assert!(glist_ab.validate_op(&op).is_ok());
        glist_ab.apply(op);
    }

    // b * c
    let mut glist_bc = glist_b;
    for op in ops_c.clone() {
        assert!(glist_bc.validate_op(&op).is_ok());
        glist_bc.apply(op);
    }

    // (a * b) * c
    for op in ops_c {
        assert!(glist_ab.validate_op(&op).is_ok());
        glist_ab.apply(op)
    }

    // a * (b * c)
    for op in ops_a {
        assert!(glist_bc.validate_op(&op).is_ok());
        glist_bc.apply(op)
    }

    assert_eq!(glist_ab, glist_bc);
}

#[quickcheck]
fn prop_merge_commute(ops_a: Vec<Op<u8>>, ops_b: Vec<Op<u8>>) {
    let mut glist_a = GList::new();
    let mut glist_b = GList::new();

    for op in ops_a.clone() {
        assert!(glist_a.validate_op(&op).is_ok());
        glist_a.apply(op)
    }
    for op in ops_b.clone() {
        assert!(glist_b.validate_op(&op).is_ok());
        glist_b.apply(op)
    }

    let glist_a_snapshot = glist_a.clone();
    glist_a.merge(glist_b.clone());
    glist_b.merge(glist_a_snapshot);

    assert_eq!(glist_a, glist_b);
}

#[quickcheck]
fn prop_merge_associative(ops_a: Vec<Op<u8>>, ops_b: Vec<Op<u8>>, ops_c: Vec<Op<u8>>) {
    let mut glist_a = GList::new();
    let mut glist_b = GList::new();
    let mut glist_c = GList::new();

    for op in ops_a.clone() {
        assert!(glist_a.validate_op(&op).is_ok());
        glist_a.apply(op)
    }
    for op in ops_b {
        assert!(glist_b.validate_op(&op).is_ok());
        glist_b.apply(op)
    }
    for op in ops_c {
        assert!(glist_c.validate_op(&op).is_ok());
        glist_c.apply(op)
    }

    // (a * b) * c
    let mut glist_ab_first = glist_a.clone();
    glist_ab_first.merge(glist_b.clone());
    glist_ab_first.merge(glist_c.clone());

    // a * (b * c)
    let mut glist_bc_first = glist_b;
    glist_bc_first.merge(glist_c);
    glist_bc_first.merge(glist_a);

    assert_eq!(glist_ab_first, glist_bc_first);
}

#[quickcheck]
fn prop_validate_against_vec_model(plan: Vec<(usize, u8, bool)>) {
    let mut model: Vec<u8> = Default::default();
    let mut glist: GList<u8> = Default::default();

    for mut instruction in plan {
        instruction.0 = if !glist.is_empty() {
            instruction.0 % glist.len()
        } else {
            0
        };
        match instruction {
            (index, elem, true) => {
                // insert before
                model.insert(index, elem);
                let op = glist.insert_before(glist.get(index), elem);
                glist.apply(op);
            }
            (index, elem, false) => {
                // insert after
                if index + 1 == model.len() || model.is_empty() {
                    model.push(elem)
                } else {
                    model.insert(index + 1, elem);
                }
                let op = glist.insert_after(glist.get(index), elem);
                glist.apply(op);
            }
        }
    }
    assert_eq!(model, glist.read_into::<Vec<u8>>());
}
