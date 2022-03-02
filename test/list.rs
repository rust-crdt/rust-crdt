use crdts::list::{List, Op};
use crdts::CmRDT;
use rand::distributions::Alphanumeric;
use rand::Rng;

type SiteId = u32;
#[derive(Debug, Clone)]
struct OperationList(pub Vec<Op<char, SiteId>>);

use quickcheck::{Arbitrary, Gen, TestResult};
use quickcheck_macros::quickcheck;

impl Arbitrary for OperationList {
    fn arbitrary<G: Gen>(g: &mut G) -> OperationList {
        let size = {
            let s = g.size();
            if s == 0 {
                0
            } else {
                g.gen_range(0, s)
            }
        };

        let actor = g.gen();
        let mut site1 = List::new();
        let ops = (0..size)
            .filter_map(|_| {
                if g.gen() || site1.is_empty() {
                    let op = site1.delete_index(g.gen_range(0, site1.len() + 1), actor);
                    site1.apply(op.clone()?);
                    op
                } else {
                    let op = site1.delete_index(g.gen_range(0, site1.len()), actor);
                    site1.apply(op.clone()?);
                    op
                }
            })
            .collect();
        OperationList(ops)
    }
    // implement shrinking ://
}

#[test]
fn test_new() {
    let site1: List<char, SiteId> = List::new();
    assert_eq!(site1.len(), 0);
    assert!(site1.is_empty());
}

#[test]
fn test_is_empty() {
    let mut site1 = List::<_, _, u64>::new();
    assert!(site1.is_empty());

    let op = site1.insert_index(0, 'a', 'A');
    site1.apply(op);
    assert!(!site1.is_empty());
}

#[test]
fn test_append() {
    let mut site1 = List::<_, _, u64>::new();
    assert!(site1.is_empty());

    let op = site1.append('a', 0);
    site1.apply(op);
    let op = site1.append('b', 0);
    site1.apply(op);
    let op = site1.append('c', 0);
    site1.apply(op);

    assert_eq!(site1.iter().collect::<String>(), "abc");
}

#[test]
fn test_out_of_order_inserts() {
    let mut site1 = List::<_, _, u64>::new();
    let mut site2 = List::<_, _, u64>::new();
    let op1 = site1.insert_index(0, 'a', 0);
    site1.apply(op1.clone());

    let op2 = site1.insert_index(1, 'c', 0);
    site1.apply(op2.clone());

    let op3 = site1.insert_index(1, 'b', 0);
    site1.apply(op3.clone());

    let mut ops = vec![op1, op2, op3];
    let mut iterations = 0;
    while let Some(op) = ops.pop() {
        assert!(iterations < (3 * (3 + 1)) / 2);
        iterations += 1;
        if site2.validate_op(&op).is_ok() {
            site2.apply(op)
        } else {
            ops.insert(0, op);
        }
    }

    let site1_items = site1.iter().collect::<String>();
    assert_eq!(site1_items, "abc");
    assert_eq!(site1_items, site2.iter().collect::<String>());
}

#[test]
fn test_concurrent_inserts_with_same_identifier_can_be_split() {
    let mut list_a = List::<_, _, u64>::new();
    let mut list_b = List::<_, _, u64>::new();
    let mut list_c = List::<_, _, u64>::new();

    let op_a = list_a.insert_index(0, 'a', 'A');
    let op_b = list_b.insert_index(0, 'b', 'B');

    list_a.apply(op_a.clone());
    list_a.apply(op_b.clone());
    list_b.apply(op_a.clone());
    list_b.apply(op_b.clone());
    list_c.apply(op_a);
    list_c.apply(op_b);

    assert_eq!(list_a.read::<String>(), "ab");
    assert_eq!(list_b.read::<String>(), "ab");
    assert_eq!(list_c.read::<String>(), "ab");
    list_c.apply(list_c.insert_index(1, 'c', 'C'));
    assert_eq!(list_c.read::<String>(), "acb");
}

#[test]
fn test_append_mixed_with_inserts() {
    let mut site1 = List::<_, _, u64>::new();
    let op = site1.append('a', 0);
    site1.apply(op);

    let op = site1.insert_index(0, 'b', 0);
    site1.apply(op);

    let op = site1.append('c', 0);
    site1.apply(op);

    let op = site1.insert_index(1, 'd', 0);
    site1.apply(op);

    assert_eq!(site1.iter().collect::<String>(), "bdac");
}

#[test]
fn test_delete_of_index() {
    let mut site1 = List::<_, _, u64>::new();
    let op = site1.insert_index(0, 'a', 0);
    site1.apply(op);
    let op = site1.insert_index(1, 'b', 0);
    site1.apply(op);
    assert_eq!(site1.iter().collect::<String>(), "ab");

    let op = site1.delete_index(0, 0);
    site1.apply(op.unwrap());
    assert_eq!(site1.iter().collect::<String>(), "b");
}

#[test]
fn test_position() {
    let mut site1 = List::<_, _, u64>::new();
    let op = site1.append('a', 0);
    site1.apply(op);
    let op = site1.append('b', 0);
    site1.apply(op);

    assert_eq!(site1.position(0), Some(&'a'));
    assert_eq!(site1.position(1), Some(&'b'));
}

#[test]
fn test_reapply_list_ops() {
    let mut rng = rand::thread_rng();

    let mut s1 = rng.sample_iter(Alphanumeric);

    let mut site1 = List::<_, _, u64>::new();
    let mut site2 = List::<_, _, u64>::new();

    for _ in 0..5000 {
        let c = s1.next().unwrap();
        let ix = rng.gen_range(0, site1.len() + 1);
        let insert_op = site1.insert_index(ix, c, 0);
        site1.apply(insert_op.clone());

        site2.apply(insert_op.clone());
        site2.apply(insert_op.clone());

        let delete_op = site2.delete_index(ix, 1).unwrap();
        // apply op a coupel of times
        site2.apply(delete_op.clone());
        site2.apply(delete_op.clone());
        // apply op a coupel of times
        site1.apply(delete_op.clone());
        site1.apply(delete_op);

        // now try applying insert op again (even though delete already appled)
        site1.apply(insert_op.clone());
    }

    assert!(
        site1.is_empty(),
        "site1 was not empty: {}",
        site1.iter().collect::<String>()
    );
    assert!(
        site2.is_empty(),
        "site2 was not empty: {}",
        site2.iter().collect::<String>()
    );

    assert_eq!(
        site2.iter().collect::<Vec<_>>(),
        site1.iter().collect::<Vec<_>>()
    );
}

#[test]
fn test_insert_followed_by_deletes() {
    let mut rng = rand::thread_rng();

    let mut s1 = rng.sample_iter(Alphanumeric);

    let mut site1 = List::<_, _, u64>::new();
    let mut site2 = List::<_, _, u64>::new();

    for _ in 0..5000 {
        let c = s1.next().unwrap();
        let ix = rng.gen_range(0, site1.len() + 1);
        let insert_op = site1.insert_index(ix, c, 0);
        site1.apply(insert_op.clone());
        site2.apply(insert_op);

        let delete_op = site2.delete_index(ix, 1).unwrap();
        site2.apply(delete_op.clone());
        site1.apply(delete_op);
    }

    assert!(
        site1.is_empty(),
        "site1 was not empty: {}",
        site1.iter().collect::<String>()
    );
    assert!(
        site2.is_empty(),
        "site2 was not empty: {}",
        site2.iter().collect::<String>()
    );
}

#[test]
fn test_mutual_insert_qc1() {
    let mut site0 = List::<_, _, u64>::new();
    let mut site1 = List::<_, _, u64>::new();
    let plan = vec![
        (8, 24, false),
        (23, 1, true),
        (93, 94, false),
        (68, 30, false),
        (37, 27, true),
    ];

    for (elem, idx, source_is_site0) in plan {
        let ((source, source_actor), replica) = if source_is_site0 {
            ((&mut site0, 0), &mut site1)
        } else {
            ((&mut site1, 1), &mut site0)
        };
        let i = idx % (source.len() + 1);
        println!("{:?} inserting {} @ {}", source_actor, elem, i);
        let op = source.insert_index(i, elem, source_actor);
        source.apply(op.clone());
        replica.apply(op);
    }

    assert_eq!(
        site0.iter().collect::<Vec<_>>(),
        site1.iter().collect::<Vec<_>>()
    );
}

#[test]
fn test_deep_inserts() {
    // By inserting always at the middle of the array, we construct increasingly
    // complex identifiers.
    //
    // Previous implementations of the List depended on an exponential which would panic once the tree
    // reached a certain depth.

    let mut site = List::<_, _, u64>::new();

    let mut vec = Vec::new();
    let n = 1000;
    for v in 0..n {
        let i = site.len() / 2;
        println!("inserting {}/{}", i, site.len());
        vec.insert(i, v);
        let op = site.insert_index(i, v, 0);
        site.apply(op);
    }
    assert_eq!(site.len(), n);
    assert_eq!(site.iter().cloned().collect::<Vec<_>>(), vec);
}

#[quickcheck]
fn prop_mutual_inserting(plan: Vec<(u8, usize, bool)>) -> bool {
    let mut site0 = List::<_, _, u64>::new();
    let mut site1 = List::<_, _, u64>::new();
    for (elem, idx, source_is_site0) in plan {
        let ((source, source_actor), replica) = if source_is_site0 {
            ((&mut site0, 0), &mut site1)
        } else {
            ((&mut site1, 1), &mut site0)
        };
        let i = idx % (source.len() + 1);
        let op = source.insert_index(i, elem, source_actor);
        source.apply(op.clone());
        replica.apply(op);
    }

    assert_eq!(
        site0.iter().collect::<Vec<_>>(),
        site1.iter().collect::<Vec<_>>()
    );
    true
}

#[quickcheck]
fn prop_inserts_and_deletes(op1: OperationList, op2: OperationList) -> TestResult {
    let mut rng = quickcheck::StdThreadGen::new(1000);
    let mut op1 = op1.0.into_iter();
    let mut op2 = op2.0.into_iter();

    let mut site1 = List::new();
    let mut site2 = List::new();

    let mut s1_empty = false;
    let mut s2_empty = false;
    while !s1_empty && !s2_empty {
        if rng.gen() {
            match op1.next() {
                Some(o) => {
                    site1.apply(o.clone());
                    site2.apply(o);
                }
                None => {
                    s1_empty = true;
                }
            }
        } else {
            match op2.next() {
                Some(o) => {
                    site1.apply(o.clone());
                    site2.apply(o);
                }
                None => {
                    s2_empty = true;
                }
            }
        }
    }

    let site1_text = site1.iter().collect::<String>();
    let site2_text = site2.iter().collect::<String>();

    TestResult::from_bool(site1_text == site2_text)
}

#[quickcheck]
fn prop_ops_are_idempotent(ops: OperationList) -> TestResult {
    let mut site1 = List::new();
    let mut site2 = List::new();

    for op in ops.0.into_iter() {
        // Apply the same op twice to site1
        site1.apply(op.clone());
        site1.apply(op.clone());

        // But only apply that op once to site2
        site2.apply(op);
    }

    let site1_text = site1.iter().collect::<String>();
    let site2_text = site2.iter().collect::<String>();

    TestResult::from_bool(site1_text == site2_text)
}

#[quickcheck]
fn prop_len_is_proportional_to_ops(oplist: OperationList) -> TestResult {
    let mut expected_len = 0;
    let mut site1 = List::new();

    for op in oplist.0.into_iter() {
        match op {
            Op::Insert { .. } => expected_len += 1,
            Op::Delete { .. } => expected_len -= 1,
        };
        site1.apply(op);
    }

    TestResult::from_bool(site1.len() == expected_len)
}
