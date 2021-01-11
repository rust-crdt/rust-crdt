use crdts::{map, mvreg, CmRDT, CvRDT, Dot, DotRange, MVReg, Map, ResetRemove, VClock};
use quickcheck::TestResult;

type TActor = u8;
type TKey = u8;
type TVal = MVReg<u8, TActor>;
type TOp = map::Op<TKey, Map<TKey, TVal, TActor>, TActor>;
type TMap = Map<TKey, Map<TKey, TVal, TActor>, TActor>;

fn build_ops(prims: (u8, Vec<(u8, u8, u8, u8, u8)>)) -> (TActor, Vec<TOp>) {
    let (actor, ops_data) = prims;

    let mut ops = Vec::new();
    for (i, op_data) in ops_data.into_iter().enumerate() {
        let (choice, inner_choice, key, inner_key, val) = op_data;
        let clock: VClock<_> = Dot::new(actor, i as u64).into();
        let dot = clock.inc(actor);
        let op = match choice % 2 {
            0 => map::Op::Up {
                dot,
                key,
                op: match inner_choice % 2 {
                    0 => map::Op::Up {
                        dot,
                        key: inner_key,
                        op: mvreg::Op::Put { clock, val },
                    },
                    1 => map::Op::Rm {
                        clock,
                        keyset: vec![inner_key].into_iter().collect(),
                    },
                    _ => unreachable!(),
                },
            },
            1 => map::Op::Rm {
                clock,
                keyset: vec![key].into_iter().collect(),
            },
            _ => unreachable!(),
        };
        ops.push(op);
    }
    (actor, ops)
}

#[test]
fn test_new() {
    let m: Map<u8, MVReg<u8, _>, u8> = Map::new();
    assert_eq!(m.len().val, 0);
    assert!(m.is_empty().val);
}

#[test]
fn test_is_empty() {
    let mut m: Map<&str, Map<&str, MVReg<&str, _>, _>, &str> = Map::new();
    let is_empty_read = m.is_empty();
    assert!(is_empty_read.val);

    m.apply(
        m.update("user_32", is_empty_read.derive_add_ctx("A"), |map, ctx| {
            map.update("name", ctx, |reg, ctx| reg.write("bob", ctx))
        }),
    );

    assert!(!m.is_empty().val);
}

#[test]
fn test_update() {
    let mut m: TMap = Map::new();

    // constructs a default value if does not exist
    let ctx = m.get(&101).derive_add_ctx(1);
    let op = m.update(101, ctx, |map, ctx| {
        map.update(110, ctx, |reg, ctx| reg.write(2, ctx))
    });

    assert_eq!(
        op,
        map::Op::Up {
            dot: Dot::new(1, 1),
            key: 101,
            op: map::Op::Up {
                dot: Dot::new(1, 1),
                key: 110,
                op: mvreg::Op::Put {
                    clock: Dot::new(1, 1).into(),
                    val: 2
                }
            }
        }
    );

    // update should not mutate the map
    assert_eq!(m, Map::new());

    m.apply(op);

    assert_eq!(
        m.get(&101)
            .val
            .and_then(|m2| m2.get(&110).val)
            .map(|r| r.read().val),
        Some(vec![2])
    );

    // the map should give the latest val to the closure
    m.apply(m.update(101, m.get(&101).derive_add_ctx(1), |map, ctx| {
        map.update(110, ctx, |reg, ctx| {
            assert_eq!(reg.read().val, vec![2]);
            reg.write(6, ctx)
        })
    }));

    assert_eq!(
        m.get(&101)
            .val
            .and_then(|m2| m2.get(&110).val)
            .map(|r| r.read().val),
        Some(vec![6])
    );
}

#[test]
fn test_remove() {
    let mut m: TMap = Map::new();

    let add_ctx = m.len().derive_add_ctx(1);
    let mut inner_map: Map<TKey, TVal, TActor> = Map::new();
    inner_map.apply(inner_map.update(110, add_ctx, |r, ctx| r.write(0, ctx)));

    let add_ctx = m.len().derive_add_ctx(1);
    m.apply(m.update(101, add_ctx, |m, ctx| {
        m.update(110, ctx, |r, ctx| r.write(0, ctx))
    }));

    assert_eq!(m.get(&101).val, Some(inner_map));
    assert_eq!(m.len().val, 1);

    m.apply(m.rm(101, m.get(&101).derive_rm_ctx()));

    assert_eq!(m.get(&101).val, None);
    assert_eq!(m.len().val, 0);
}

#[test]
fn test_reset_remove_semantics() {
    let mut m1 = TMap::new();

    m1.apply(m1.update(101, m1.get(&101).derive_add_ctx(74), |map, ctx| {
        map.update(110, ctx, |reg, ctx| reg.write(32, ctx))
    }));

    let mut m2 = m1.clone();

    m1.apply(m1.rm(101, m1.get(&101).derive_rm_ctx()));

    m2.apply(m2.update(101, m2.get(&101).derive_add_ctx(37), |map, ctx| {
        map.update(220, ctx, |reg, ctx| reg.write(5, ctx))
    }));

    let m1_snapshot = m1.clone();

    m1.merge(m2.clone());
    m2.merge(m1_snapshot);
    assert_eq!(m1, m2);

    let inner_map = m1.get(&101).val.unwrap();
    assert_eq!(inner_map.get(&220).val.map(|r| r.read().val), Some(vec![5]));
    assert_eq!(inner_map.get(&110).val, None);
    assert_eq!(inner_map.len().val, 1);
}

#[test]
fn test_updating_with_current_clock_should_be_a_nop() {
    let mut m1: TMap = Map::new();

    m1.apply(map::Op::Up {
        dot: Dot::new(1, 0),
        key: 0,
        op: map::Op::Up {
            dot: Dot::new(1, 0),
            key: 1,
            op: mvreg::Op::Put {
                clock: VClock::new(),
                val: 235,
            },
        },
    });

    // the update should have been ignored
    assert_eq!(m1, Map::new());
}

#[test]
fn test_concurrent_update_and_remove_add_bias() {
    let mut m1 = TMap::new();
    let mut m2 = TMap::new();

    let op1 = map::Op::Rm {
        clock: Dot::new(1, 1).into(),
        keyset: vec![102].into_iter().collect(),
    };

    let op2 = m2.update(102, m2.get(&102).derive_add_ctx(2), |map, ctx| {
        map.update(42, ctx, |reg, ctx| reg.write(7, ctx))
    });

    m1.apply(op1.clone());
    m2.apply(op2.clone());

    let mut m1_clone = m1.clone();
    let mut m2_clone = m2.clone();

    m1_clone.merge(m2.clone());
    m2_clone.merge(m1.clone());

    m1.apply(op2);
    m2.apply(op1);

    assert_eq!(m1_clone, m2_clone);
    assert_eq!(m1, m2);
    assert_eq!(m1, m1_clone);

    // we bias towards adds
    assert_eq!(
        m1.get(&102)
            .val
            .and_then(|map| map.get(&42).val)
            .map(|reg| reg.read().val),
        Some(vec![7])
    );
}

#[test]
fn test_op_exchange_commutes_quickcheck1() {
    // This will not pass if we swap out the mvreg with an lwwreg
    // we need a true causal register
    let mut m1: Map<u8, MVReg<u8, u8>, u8> = Map::new();
    let m1_op1 = m1.update(0, m1.get(&0).derive_add_ctx(1), |reg, ctx| {
        reg.write(0, ctx)
    });
    m1.apply(m1_op1.clone());
    let m1_op2 = m1.rm(0, m1.get(&0).derive_rm_ctx());
    m1.apply(m1_op2.clone());

    let mut m2: Map<u8, MVReg<u8, u8>, u8> = Map::new();
    let m2_op1 = m2.update(0, m2.get(&0).derive_add_ctx(2), |reg, ctx| {
        reg.write(0, ctx)
    });
    m2.apply(m2_op1.clone());

    // m1 <- m2
    m1.apply(m2_op1);

    // m2 <- m1
    m2.apply(m1_op1);
    m2.apply(m1_op2);

    assert_eq!(m1, m2);
}

#[test]
fn test_op_deferred_remove() {
    let mut m1: Map<u8, MVReg<u8, u8>, u8> = Map::new();
    let mut m2 = m1.clone();
    let mut m3 = m1.clone();

    let m1_up1 = m1.update(0, m1.get(&0).derive_add_ctx(1), |reg, ctx| {
        reg.write(0, ctx)
    });
    m1.apply(m1_up1.clone());

    let m1_up2 = m1.update(1, m1.get(&1).derive_add_ctx(1), |reg, ctx| {
        reg.write(1, ctx)
    });
    m1.apply(m1_up2.clone());

    m2.apply(m1_up1.clone());
    m2.apply(m1_up2.clone());

    let m2_rm = m2.rm(0, m2.get(&0).derive_rm_ctx());
    m2.apply(m2_rm.clone());

    assert_eq!(m2.get(&0).val, None);
    m3.apply(m2_rm.clone());
    m3.apply(m1_up1);
    m3.apply(m1_up2);

    m1.apply(m2_rm);

    assert_eq!(m2.get(&0).val, None);
    assert_eq!(m3.get(&1).val.map(|r| r.read().val), Some(vec![1]));

    assert_eq!(m2, m3);
    assert_eq!(m1, m2);
    assert_eq!(m1, m3);
}

#[test]
fn test_merge_deferred_remove() {
    let mut m1: Map<u8, MVReg<u8, u8>, u8> = Map::new();
    let mut m2: Map<u8, MVReg<u8, u8>, u8> = Map::new();
    let mut m3: Map<u8, MVReg<u8, u8>, u8> = Map::new();

    m1.apply(m1.update(0, m1.get(&0).derive_add_ctx(1), |reg, ctx| {
        reg.write(0, ctx)
    }));
    m1.apply(m1.update(1, m1.get(&1).derive_add_ctx(1), |reg, ctx| {
        reg.write(1, ctx)
    }));

    m2.merge(m1.clone());
    m2.apply(m2.rm(0, m2.get(&0).derive_rm_ctx()));

    assert_eq!(m2.get(&0).val, None);
    m3.merge(m2.clone());
    m3.merge(m1.clone());
    m1.merge(m2.clone());

    assert_eq!(m2.get(&0).val, None);
    assert_eq!(m3.get(&1).val.map(|r| r.read().val), Some(vec![1]));

    assert_eq!(m2, m3);
    assert_eq!(m1, m2);
    assert_eq!(m1, m3);
}

#[test]
fn test_commute_quickcheck_bug() {
    let ops = vec![
        map::Op::Rm {
            clock: Dot::new(45, 1).into(),
            keyset: vec![0].into_iter().collect(),
        },
        map::Op::Up {
            dot: Dot::new(45, 2),
            key: 0,
            op: map::Op::Up {
                dot: Dot::new(45, 1),
                key: 0,
                op: mvreg::Op::Put {
                    clock: VClock::new(),
                    val: 0,
                },
            },
        },
    ];

    let mut m = Map::new();
    apply_ops(&mut m, &ops);

    let m_snapshot = m.clone();

    let mut empty_m = Map::new();
    m.merge(empty_m.clone());
    empty_m.merge(m_snapshot);

    assert_eq!(m, empty_m);
}

#[test]
fn test_idempotent_quickcheck_bug1() {
    let ops = vec![
        map::Op::Up {
            dot: Dot::new(21, 5),
            key: 0,
            op: map::Op::Up {
                dot: Dot::new(21, 1),
                key: 32,
                op: mvreg::Op::Put {
                    clock: VClock::new(),
                    val: 42,
                },
            },
        },
        map::Op::Rm {
            clock: vec![Dot::new(21, 5)].into_iter().collect(),
            keyset: vec![0].into_iter().collect(),
        },
        map::Op::Up {
            dot: Dot::new(21, 6),
            key: 1,
            op: map::Op::Up {
                dot: Dot::new(21, 1),
                key: 0,
                op: mvreg::Op::Put {
                    clock: VClock::new(),
                    val: 0,
                },
            },
        },
    ];

    let mut m = Map::new();
    apply_ops(&mut m, &ops);

    let m_snapshot = m.clone();
    m.merge(m_snapshot.clone());

    assert_eq!(m, m_snapshot);
}

#[test]
fn test_idempotent_quickcheck_bug2() {
    let mut m: TMap = Map::new();

    m.apply(map::Op::Up {
        dot: Dot::new(32, 5),
        key: 0,
        op: map::Op::Up {
            dot: Dot::new(32, 5),
            key: 0,
            op: mvreg::Op::Put {
                clock: VClock::new(),
                val: 0,
            },
        },
    });

    let m_snapshot = m.clone();

    // m ^ m
    m.merge(m_snapshot.clone());

    // m ^ m = m
    assert_eq!(m, m_snapshot);
}

#[test]
fn test_op_exchange_same_as_merge_quickcheck1() {
    let op1 = map::Op::Up {
        dot: Dot::new(38, 4),
        key: 216,
        op: map::Op::Up {
            dot: Dot::new(38, 1),
            key: 37,
            op: mvreg::Op::Put {
                clock: Dot::new(38, 1).into(),
                val: 94,
            },
        },
    };
    let op2 = map::Op::Up {
        dot: Dot::new(91, 9),
        key: 216,
        op: map::Op::Up {
            dot: Dot::new(91, 1),
            key: 37,
            op: mvreg::Op::Put {
                clock: Dot::new(91, 1).into(),
                val: 94,
            },
        },
    };
    let mut m1: TMap = Map::new();
    let mut m2: TMap = Map::new();
    m1.apply(op1.clone());
    m2.apply(op2.clone());

    let mut m1_merge = m1.clone();
    m1_merge.merge(m2.clone());

    let mut m2_merge = m2.clone();
    m2_merge.merge(m1.clone());

    m1.apply(op2);
    m2.apply(op1);

    assert_eq!(m1, m2);
    assert_eq!(m1_merge, m2_merge);
    assert_eq!(m1, m1_merge);
    assert_eq!(m2, m2_merge);
    assert_eq!(m1, m2_merge);
    assert_eq!(m2, m1_merge);
}

#[test]
fn test_op_invalid_if_skipping_dot() {
    let map: TMap = Map::new();

    let op = map::Op::Up {
        dot: Dot::new(38, 4),
        key: 216,
        op: map::Op::Up {
            dot: Dot::new(38, 1),
            key: 37,
            op: mvreg::Op::Put {
                clock: Dot::new(38, 1).into(),
                val: 94,
            },
        },
    };

    assert_eq!(
        map.validate_op(&op),
        Err(map::CmRDTValidation::SourceOrder(DotRange {
            actor: 38,
            counter_range: 1..4
        }))
    );
}

#[test]
fn test_nested_op_invalid_if_skipping_dot() {
    let map: TMap = Map::new();

    let op = map::Op::Up {
        dot: Dot::new(38, 1),
        key: 216,
        op: map::Op::Up {
            dot: Dot::new(38, 2),
            key: 37,
            op: mvreg::Op::Put {
                clock: Dot::new(38, 1).into(),
                val: 94,
            },
        },
    };

    assert_eq!(
        map.validate_op(&op),
        Err(map::CmRDTValidation::Value(
            map::CmRDTValidation::SourceOrder(DotRange {
                actor: 38,
                counter_range: 1..2
            })
        ))
    );
}

#[test]
fn test_idempotent_quickcheck1() {
    let ops = vec![
        map::Op::Up {
            dot: Dot::new(62, 9),
            key: 47,
            op: map::Op::Up {
                dot: Dot::new(62, 1),
                key: 65,
                op: mvreg::Op::Put {
                    clock: Dot::new(62, 1).into(),
                    val: 240,
                },
            },
        },
        map::Op::Up {
            dot: Dot::new(62, 11),
            key: 60,
            op: map::Op::Up {
                dot: Dot::new(62, 1),
                key: 193,
                op: mvreg::Op::Put {
                    clock: Dot::new(62, 1).into(),
                    val: 28,
                },
            },
        },
    ];
    let mut m: TMap = Map::new();
    apply_ops(&mut m, &ops);
    let m_snapshot = m.clone();

    // m ^ m
    m.merge(m_snapshot.clone());

    // m ^ m = m
    assert_eq!(m, m_snapshot);
}

fn apply_ops(map: &mut TMap, ops: &[TOp]) {
    for op in ops.iter().cloned() {
        map.apply(op);
    }
}

quickcheck! {
    // TODO: add test to show equivalence of merge and Op exchange
    fn prop_op_exchange_same_as_merge(
        ops1_prim: (u8, Vec<(u8, u8, u8, u8, u8)>),
        ops2_prim: (u8, Vec<(u8, u8, u8, u8, u8)>)
    ) -> TestResult {
        let ops1 = build_ops(ops1_prim);
        let ops2 = build_ops(ops2_prim);

        if ops1.0 == ops2.0 {
            return TestResult::discard();
        }

        let mut m1: TMap = Map::new();
        let mut m2: TMap = Map::new();

        apply_ops(&mut m1, &ops1.1);
        apply_ops(&mut m2, &ops2.1);

        let mut m_merged = m1.clone();
        m_merged.merge(m2.clone());

        apply_ops(&mut m1, &ops2.1);
        apply_ops(&mut m2, &ops1.1);

        TestResult::from_bool(m1 == m_merged && m2 == m_merged)
    }

    fn prop_op_exchange_converges(
        ops1_prim: (u8, Vec<(u8, u8, u8, u8, u8)>),
        ops2_prim: (u8, Vec<(u8, u8, u8, u8, u8)>)
    ) -> TestResult {
        let ops1 = build_ops(ops1_prim);
        let ops2 = build_ops(ops2_prim);

        if ops1.0 == ops2.0 {
            return TestResult::discard();
        }

        let mut m1: TMap = Map::new();
        let mut m2: TMap = Map::new();

        apply_ops(&mut m1, &ops1.1);
        apply_ops(&mut m2, &ops2.1);

        // m1 <- m2
        apply_ops(&mut m1, &ops2.1);

        // m2 <- m1
        apply_ops(&mut m2, &ops1.1);

        // m1 <- m2 == m2 <- m1
        assert_eq!(m1, m2);
        TestResult::from_bool(true)
    }

    fn prop_op_exchange_associative(
        ops1_prim: (u8, Vec<(u8, u8, u8, u8, u8)>),
        ops2_prim: (u8, Vec<(u8, u8, u8, u8, u8)>),
        ops3_prim: (u8, Vec<(u8, u8, u8, u8, u8)>)
    ) -> TestResult {
        let ops1 = build_ops(ops1_prim);
        let ops2 = build_ops(ops2_prim);
        let ops3 = build_ops(ops3_prim);

        if ops1.0 == ops2.0 || ops1.0 == ops3.0 || ops2.0 == ops3.0 {
            return TestResult::discard();
        }

        let mut m1: TMap = Map::new();
        let mut m2: TMap = Map::new();
        let mut m3: TMap = Map::new();

        apply_ops(&mut m1, &ops1.1);
        apply_ops(&mut m2, &ops2.1);
        apply_ops(&mut m3, &ops3.1);

        // (m1 <- m2) <- m3
        apply_ops(&mut m1, &ops2.1);
        apply_ops(&mut m1, &ops3.1);

        // (m2 <- m3) <- m1
        apply_ops(&mut m2, &ops3.1);
        apply_ops(&mut m2, &ops1.1);

        // (m1 <- m2) <- m3 = (m2 <- m3) <- m1
        TestResult::from_bool(m1 == m2)
    }

    fn prop_op_idempotent(
        ops_prim: (u8, Vec<(u8, u8, u8, u8, u8)>)
    ) -> bool {
        let ops = build_ops(ops_prim);
        let mut m = TMap::new();

        apply_ops(&mut m, &ops.1);
        let m_snapshot = m.clone();
        apply_ops(&mut m, &ops.1);

        m == m_snapshot
    }

    fn prop_op_associative(
        ops1_prim: (u8, Vec<(u8, u8, u8, u8, u8)>),
        ops2_prim: (u8, Vec<(u8, u8, u8, u8, u8)>),
        ops3_prim: (u8, Vec<(u8, u8, u8, u8, u8)>)
    ) -> TestResult {
        let ops1 = build_ops(ops1_prim);
        let ops2 = build_ops(ops2_prim);
        let ops3 = build_ops(ops3_prim);

        if ops1.0 == ops2.0 || ops1.0 == ops3.0 || ops2.0 == ops3.0 {
            return TestResult::discard();
        }

        let mut m1: TMap = Map::new();
        let mut m2: TMap = Map::new();
        let mut m3: TMap = Map::new();

        apply_ops(&mut m1, &ops1.1);
        apply_ops(&mut m2, &ops2.1);
        apply_ops(&mut m3, &ops3.1);

        // (m1 <- m2) <- m3
        apply_ops(&mut m1, &ops2.1);
        apply_ops(&mut m1, &ops3.1);

        // (m2 <- m3) <- m1
        apply_ops(&mut m2, &ops3.1);
        apply_ops(&mut m2, &ops1.1);

        // (m1 ^ m2) ^ m3 = m1 ^ (m2 ^ m3)
        TestResult::from_bool(m1 == m2)
    }


    fn prop_merge_associative(
        ops1_prim: (u8, Vec<(u8, u8, u8, u8, u8)>),
        ops2_prim: (u8, Vec<(u8, u8, u8, u8, u8)>),
        ops3_prim: (u8, Vec<(u8, u8, u8, u8, u8)>)
    ) -> TestResult {
        let ops1 = build_ops(ops1_prim);
        let ops2 = build_ops(ops2_prim);
        let ops3 = build_ops(ops3_prim);
        if ops1.0 == ops2.0 || ops1.0 == ops3.0 || ops2.0 == ops3.0 {
            return TestResult::discard();
        }

        let mut m1: TMap = Map::new();
        let mut m2: TMap = Map::new();
        let mut m3: TMap = Map::new();

        apply_ops(&mut m1, &ops1.1);
        apply_ops(&mut m2, &ops2.1);
        apply_ops(&mut m3, &ops3.1);

        let mut m1_snapshot = m1.clone();

        // (m1 ^ m2) ^ m3
        m1.merge(m2.clone());
        m1.merge(m3.clone());

        // m1 ^ (m2 ^ m3)
        m2.merge(m3);
        m1_snapshot.merge(m2);

        // (m1 ^ m2) ^ m3 = m1 ^ (m2 ^ m3)
        TestResult::from_bool(m1 == m1_snapshot)
    }

    fn prop_merge_commutative(
        ops1_prim: (u8, Vec<(u8, u8, u8, u8, u8)>),
        ops2_prim: (u8, Vec<(u8, u8, u8, u8, u8)>)
    ) -> TestResult {
        let ops1 = build_ops(ops1_prim);
        let ops2 = build_ops(ops2_prim);

        if ops1.0 == ops2.0 {
            return TestResult::discard();
        }

        let mut m1: TMap = Map::new();
        let mut m2: TMap = Map::new();

        apply_ops(&mut m1, &ops1.1);
        apply_ops(&mut m2, &ops2.1);

        let m1_snapshot = m1.clone();
        // m1 ^ m2
        m1.merge(m2.clone());

        // m2 ^ m1
        m2.merge(m1_snapshot);

        // m1 ^ m2 = m2 ^ m1
        TestResult::from_bool(m1 == m2)
    }


    fn prop_merge_followed_by_merge(
        ops1_prim: (u8, Vec<(u8, u8, u8, u8, u8)>),
        ops2_prim: (u8, Vec<(u8, u8, u8, u8, u8)>)
    ) -> TestResult {
        let ops1 = build_ops(ops1_prim);
        let ops2 = build_ops(ops2_prim);

        if ops1.0 == ops2.0 {
            return TestResult::discard();
        }

        let mut m1: TMap = Map::new();
        let mut m2: TMap = Map::new();

        apply_ops(&mut m1, &ops1.1);
        apply_ops(&mut m2, &ops2.1);

        // m1 ^ m2
        m1.merge(m2.clone());

        // m2 ^ m1
        m2.merge(m1.clone());

        // m1 ^ m2 = m2 ^ m1
        TestResult::from_bool(m1 == m2)
    }

    fn prop_merge_idempotent(
        ops_prim: (u8, Vec<(u8, u8, u8, u8, u8)>)
    ) -> bool {
        let ops = build_ops(ops_prim);

        let mut m: TMap = Map::new();
        apply_ops(&mut m, &ops.1);
        let m_snapshot = m.clone();

        // m ^ m
        m.merge(m_snapshot.clone());

        // m ^ m = m
        m == m_snapshot
    }

    fn prop_reset_remove_with_empty_vclock_is_nop(
        ops_prim: (u8, Vec<(u8, u8, u8, u8, u8)>)
    ) -> bool {
        let ops = build_ops(ops_prim);

        let mut m: TMap = Map::new();
        apply_ops(&mut m, &ops.1);

        let m_snapshot = m.clone();
        m.reset_remove(&VClock::new());

        m == m_snapshot
    }

    fn prop_reset_remove_with_map_clock_is_empty_map(
        ops_prim: (u8, Vec<(u8, u8, u8, u8, u8)>)
    ) -> bool {
        let mut m = TMap::new();
        apply_ops(&mut m, &build_ops(ops_prim).1);

        m.reset_remove(&m.len().rm_clock);

        // Map may still have some deferred removes
        // stored, so it's not neccessarily true that
        // m == TestMap::new()
        m.len().val == 0
    }

    fn prop_reset_remove_than_merge_same_as_merge_than_reset_remove(
        ops1_prim: (u8, Vec<(u8, u8, u8, u8, u8)>),
        ops2_prim: (u8, Vec<(u8, u8, u8, u8, u8)>),
        vclock: VClock<u8>
    ) -> TestResult {
        let ops1 = build_ops(ops1_prim);
        let ops2 = build_ops(ops2_prim);

        if ops1.0 == ops2.0 {
            return TestResult::discard();
        }

        let mut m1: TMap = Map::new();
        let mut m2: TMap = Map::new();

        apply_ops(&mut m1, &ops1.1);
        apply_ops(&mut m2, &ops2.1);

        let mut m1_reset_remove_after = m1.clone();
        let m2_reset_remove_after = m2.clone();

        m1.reset_remove(&vclock);
        m2.reset_remove(&vclock);

        m1.merge(m2);

        m1_reset_remove_after.merge(m2_reset_remove_after);
        m1_reset_remove_after.reset_remove(&vclock);

        TestResult::from_bool(m1_reset_remove_after == m1)
    }
}
