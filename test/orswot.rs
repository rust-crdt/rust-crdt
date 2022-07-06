extern crate crdts;
extern crate rand;

use crdts::{ctx::ReadCtx, orswot::Op, *};
use std::collections::HashSet;
use std::iter::once;

const ACTOR_MAX: u8 = 11;

type Member = u8;
type Actor = u8;

quickcheck! {
    fn prop_validate_op(ops: Vec<Op<Member, Actor>>, op: Op<Member, Actor>) -> bool {
        let mut orswot = Orswot::new();
        for op in ops.clone() {
            if orswot.validate_op(&op).is_ok() {
                orswot.apply(op)
            }
        }

        match op.clone() {
            Op::Add { dot, members } => {
                let expected_dot = orswot.clock().inc(dot.actor);
                if dot < expected_dot {
                    assert_eq!(orswot.validate_op(&op), Ok(()));
                    let orswot_clone = orswot.clone();
                    orswot.apply(op);
                    assert_eq!(orswot, orswot_clone);
                } else if dot == expected_dot {
                    assert_eq!(orswot.validate_op(&op), Ok(()));
                    orswot.apply(op);
                    for member in members {
                        let removed = ops.iter().any(|op| {
                            if let Op::Rm { clock, members } = op {
                                members.contains(&member) && clock.dot(dot.actor) >= dot
                            } else {
                                false
                            }
                        });

                        assert!(removed || orswot.contains(&member).val);
                    }
                } else {
                    assert_eq!(
                       orswot.validate_op(&op),
                       Err(DotRange {
                           actor: dot.actor,
                           counter_range: expected_dot.counter..dot.counter,
                       })
                    );
                }
            }
            Op::Rm { .. } => assert_eq!(orswot.validate_op(&op), Ok(()))
        }

        true
    }

    fn prop_validate_merge(ops_1: Vec<Op<Member, Actor>>, ops_2: Vec<Op<Member, Actor>>) -> bool {
        let mut orswot_1 = Orswot::new();
        let mut orswot_2 = Orswot::new();

        for op in ops_1.clone() {
            if orswot_1.validate_op(&op).is_ok() {
               orswot_1.apply(op)
            }
        }

        for op in ops_2.clone() {
            if orswot_2.validate_op(&op).is_ok() {
                orswot_2.apply(op)
            }
        }

        if orswot_1.validate_merge(&orswot_2).is_ok() {
            assert_eq!(orswot_2.validate_merge(&orswot_1), Ok(()));
        }

        if orswot_2.validate_merge(&orswot_1).is_ok() {
            assert_eq!(orswot_1.validate_merge(&orswot_2), Ok(()));
        }

        if orswot_1.validate_merge(&orswot_2).is_ok() {
            let mut merged = orswot_1.clone();
            merged.merge(orswot_2.clone());
            let merged_members = merged.read().val;

            for ReadCtx { val, rm_clock, .. } in orswot_1.iter() {
                if !merged_members.contains(val) {
                    let mut val_clock = rm_clock.clone();
                    for op in ops_2.iter() {
                        match op {
                            Op::Rm { clock, .. } => val_clock.reset_remove(clock),
                            Op::Add { members, dot } => {
                                if members.is_empty() {
                                    val_clock.reset_remove(&VClock::from(*dot));
                                }
                            }
                        }
                    }
                    assert_eq!(val_clock, VClock::new());
                }
            }

            for ReadCtx { val, rm_clock, .. } in orswot_2.iter() {
                if !merged_members.contains(val) {
                    let mut val_clock = rm_clock.clone();
                    for op in ops_1.iter() {
                        match op {
                            Op::Rm { clock, .. } => val_clock.reset_remove(clock),
                            Op::Add { members, dot } => {
                                if members.is_empty() {
                                    val_clock.reset_remove(&VClock::from(*dot));
                                }
                            }
                        }
                    }
                    assert_eq!(val_clock, VClock::new());
                }
            }
    }

        true
    }

    fn prop_merge_converges(ops: Vec<Op<Member, Actor>>) -> bool {
        // Different interleavings of ops applied to different
        // orswots should all converge when merged. Apply the
        // ops to increasing numbers of witnessing orswots,
        // then merge them together and make sure they have
        // all converged.
        let mut result = None;
        for i in 2..ACTOR_MAX {
            let mut witnesses: Vec<Orswot<Member, Actor>> =
                (0..i).map(|_| Orswot::new()).collect();
            for op in ops.iter() {
                let actor_opt = match op {
                    Op::Add { dot, ..} => Some(dot.actor),
                    Op::Rm { clock, ..} => clock.iter().next().map(|d| *d.actor) // any actor will do for Rm
                };

                if let Some(actor) = actor_opt {
                    let witness = &mut witnesses[(actor % i) as usize];
                    witness.apply(op.clone());
                }
            }

            let mut merged = Orswot::new();
            for witness in witnesses {
                merged.merge(witness);
            }

            if let Some(ref prev_res) = result {
                if prev_res != &merged {
                    println!("opvec: {:?}", ops);
                    println!("result: {:?}", result);
                    println!("merged: {:?}", merged);
                    return false;
                };
            } else {
                result = Some(merged);
            }
        }
        true
    }
}

/// When two orswots have identical clocks, but different elements,
/// any non-common elements will be dropped.  This highlights the
/// proper usage of orswots: don't use the same witness from different
/// copies of the orswot, or elements will be deleted upon merge.
#[test]
fn weird_highlight_1() {
    let mut a = Orswot::new();
    let mut b = Orswot::new();
    a.apply(a.add(1, a.read().derive_add_ctx("A")));
    b.apply(b.add(2, b.read().derive_add_ctx("A")));

    a.merge(b);
    assert!(a.read().val.is_empty());
}

///
#[test]
fn adds_dont_destroy_causality() {
    let mut a = Orswot::new();
    let mut b = a.clone();
    let mut c = a.clone();

    c.apply(c.add("element", c.read().derive_add_ctx("A")));
    c.apply(c.add("element", c.read().derive_add_ctx("B")));

    let c_element_ctx = c.contains(&"element");

    // If we want to remove this entry, the remove context
    // should descend from vclock { 1->1, 2->1 }
    assert_eq!(
        c_element_ctx.rm_clock,
        vec![Dot::new("A", 1), Dot::new("B", 1)]
            .into_iter()
            .collect()
    );

    a.apply(a.add("element", a.read().derive_add_ctx("C")));
    b.apply(c.rm("element", c_element_ctx.derive_rm_ctx()));
    a.apply(a.add("element", a.read().derive_add_ctx("A")));

    a.merge(b);
    assert_eq!(a.read().val, vec!["element"].into_iter().collect());
}

// a bug found with rust quickcheck where identical entries
// with different associated clocks were removed rather
// than merged.
#[test]
fn merge_clocks_of_identical_entries() {
    let mut a = Orswot::new();
    let mut b = a.clone();
    // add element 1 with witnesses 3 and 7
    a.apply(a.add(1, a.read().derive_add_ctx("A")));
    b.apply(a.add(1, b.read().derive_add_ctx("B")));
    a.merge(b);

    assert_eq!(a.read().val, vec![1].into_iter().collect());

    let mut final_clock = VClock::new();
    final_clock.apply(final_clock.inc("A"));
    final_clock.apply(final_clock.inc("B"));
    assert!(a.contains(&1).val);
    assert_eq!(a.contains(&1).rm_clock, final_clock);
}

// port from riak_dt
#[test]
fn test_disjoint_merge() {
    let mut a = Orswot::new();
    let mut b = a.clone();

    a.apply(a.add(0, a.read().derive_add_ctx("A")));
    assert_eq!(a.read().val, vec![0].into_iter().collect());

    b.apply(b.add(1, b.read().derive_add_ctx("B")));
    assert_eq!(b.read().val, vec![1].into_iter().collect());

    let mut c = a.clone();
    c.merge(b);
    assert_eq!(c.read().val, vec![0, 1].into_iter().collect());

    a.apply(a.rm(0, a.contains(&0).derive_rm_ctx()));

    let mut d = a.clone();
    d.merge(c);
    assert_eq!(d.read().val, vec![1].into_iter().collect());
}

// port from riak_dt
// A bug EQC found where dropping the dots in merge was not enough if
// you then store the value with an empty clock (derp).
#[test]
fn test_no_dots_left_test() {
    let mut a = Orswot::new();
    let mut b = Orswot::new();

    a.apply(a.add(0, a.read().derive_add_ctx("A")));
    b.apply(b.add(0, b.read().derive_add_ctx("B")));
    let c = a.clone();
    a.apply(a.rm(0, a.contains(&0).derive_rm_ctx()));

    // replicate B to A, now A has B's 'Z'
    a.merge(b.clone());
    assert_eq!(a.read().val, vec![0].into_iter().collect());

    let mut expected_clock = VClock::new();
    expected_clock.apply(expected_clock.inc("A"));
    expected_clock.apply(expected_clock.inc("B"));
    assert_eq!(a.read().add_clock, expected_clock);

    b.apply(b.rm(0, b.contains(&0).derive_rm_ctx()));
    assert!(b.read().val.is_empty());

    // Replicate C to B, now B has A's old 'Z'
    b.merge(c.clone());
    assert_eq!(b.read().val, vec![0].into_iter().collect());

    // Merge everything, without the fix You end up with 'Z' present,
    // with no dots
    b.merge(a);
    b.merge(c);
    assert!(b.read().val.is_empty());
}

// port from riak_dt
// A test I thought up
// - existing replica of ['A'] at a and b,
// - add ['B'] at b, but not communicated to any other nodes, context returned to client
// - b goes down forever
// - remove ['A'] at a, using the context the client got from b
// - will that remove happen?
//   case for shouldn't: the context at b will always be bigger than that at a
//   case for should: we have the information in dots that may allow us to realise it can be removed
//     without us caring.
//
// as the code stands, 'A' *is* removed, which is almost certainly correct. This behaviour should
// always happen, but may not. (ie, the test needs expanding)
#[test]
fn test_dead_node_update() {
    let mut a = Orswot::new();
    let a_op = a.add(0, a.read().derive_add_ctx("A"));
    assert_eq!(
        a_op,
        Op::Add {
            dot: Dot::new("A", 1),
            members: once(0).collect(),
        }
    );

    a.apply(a_op);
    assert_eq!(a.contains(&0).rm_clock, VClock::from(Dot::new("A", 1)));

    let mut b = a.clone();
    b.apply(b.add(1, b.read().derive_add_ctx("B")));
    let bctx = b.read();
    assert_eq!(
        bctx.add_clock,
        vec![Dot::new("A", 1), Dot::new("B", 1)]
            .into_iter()
            .collect()
    );

    a.apply(a.rm(0, bctx.derive_rm_ctx()));
    assert_eq!(a.read().val, HashSet::new());
}

#[test]
fn test_reset_remove_semantics() {
    let mut m1: Map<u8, Orswot<Member, &str>, &str> = Map::new();

    m1.apply(
        m1.update(101, m1.get(&101).derive_add_ctx("A"), |set, ctx| {
            set.add(1, ctx)
        }),
    );

    let mut m2 = m1.clone();

    m1.apply(m1.rm(101, m1.get(&101).derive_rm_ctx()));
    m2.apply(
        m2.update(101, m2.get(&101).derive_add_ctx("B"), |set, ctx| {
            set.add(2, ctx)
        }),
    );

    assert_eq!(m1.get(&101).val, None);
    assert_eq!(
        m2.get(&101).val.unwrap().read().val,
        vec![1, 2].into_iter().collect()
    );

    m1.merge(m2.clone());
    m2.merge(m1.clone());

    assert_eq!(m1, m2);
    assert_eq!(
        m1.get(&101).val.unwrap().read().val,
        vec![2].into_iter().collect()
    );
}
