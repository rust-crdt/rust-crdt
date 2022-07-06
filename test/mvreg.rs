use crdts::{mvreg::Op, *};

use quickcheck::TestResult;

#[derive(Debug, Clone)]
struct TestReg {
    reg: MVReg<u8, u8>,
    ops: Vec<Op<u8, u8>>,
}

#[test]
fn test_apply() {
    let mut reg = MVReg::new();
    let clock = VClock::from(Dot::new(2, 1));
    reg.apply(Op::Put {
        clock: clock.clone(),
        val: 71,
    });
    assert_eq!(reg.read().add_clock, clock);
    assert_eq!(reg.read().val, vec![71]);
}

#[test]
fn test_write_should_not_mutate_reg() {
    let reg = MVReg::new();
    let ctx = reg.read().derive_add_ctx("A");
    let op = reg.write(32, ctx);
    assert_eq!(reg, MVReg::new());

    let mut reg = reg;
    reg.apply(op);
    assert_eq!(reg.read().val, vec![32]);
    assert_eq!(reg.read().add_clock, VClock::from(Dot::new("A", 1)));
}

#[test]
fn test_concurrent_update_with_same_value_dont_collapse_on_merge() {
    // this is important to prevent because it breaks commutativity
    let mut r1 = MVReg::new();
    let mut r2 = MVReg::new();
    r1.apply(r1.write(23, r1.read().derive_add_ctx("A")));
    r2.apply(r2.write(23, r2.read().derive_add_ctx("B")));

    r1.merge(r2);

    assert_eq!(r1.read().val, vec![23, 23]);
    assert_eq!(
        r1.read().add_clock,
        vec![Dot::new("A", 1), Dot::new("B", 1)]
            .into_iter()
            .collect()
    );
}

#[test]
fn test_concurrent_update_with_same_value_dont_collapse_on_apply() {
    // this is important to prevent because it breaks commutativity
    let mut r1 = MVReg::new();
    let r2 = MVReg::new();

    r1.apply(r1.write(23, r1.read().derive_add_ctx("A")));
    r1.apply(r2.write(23, r2.read().derive_add_ctx("B")));

    assert_eq!(r1.read().val, vec![23, 23]);
    assert_eq!(
        r1.read().add_clock,
        vec![Dot::new("A", 1), Dot::new("B", 1)]
            .into_iter()
            .collect()
    );
}

#[test]
fn test_multi_val() {
    let mut r1 = MVReg::new();
    let mut r2 = MVReg::new();

    r1.apply(r1.write(32, r1.read().derive_add_ctx("A")));
    r2.apply(r2.write(82, r2.read().derive_add_ctx("B")));

    r1.merge(r2);
    assert!(r1.read().val == vec![32, 82] || r1.read().val == vec![82, 32]);
}

#[test]
fn test_op_commute_quickcheck1() {
    let mut reg1 = MVReg::new();
    let mut reg2 = MVReg::new();

    let op1 = Op::Put {
        clock: Dot::new("A", 1).into(),
        val: 1,
    };
    let op2 = Op::Put {
        clock: Dot::new("B", 1).into(),
        val: 2,
    };

    reg2.apply(op2.clone());
    reg2.apply(op1.clone());
    reg1.apply(op1);
    reg1.apply(op2);

    assert_eq!(reg1, reg2);
}

fn ops_are_not_compatible(opss: &[&Vec<(u8, u8)>]) -> bool {
    // We need to make sure that we never insert two different values with
    // the same actor version.
    for a_ops in opss.iter() {
        for b_ops in opss.iter().filter(|o| o != &a_ops) {
            let mut a_clock = VClock::new();
            let mut b_clock = VClock::new();
            for ((_, a_actor), (_, b_actor)) in a_ops.iter().zip(b_ops.iter()) {
                a_clock.apply(a_clock.inc(*a_actor));
                b_clock.apply(b_clock.inc(*b_actor));

                if b_clock.get(a_actor) == a_clock.get(a_actor) {
                    // this check is a bit broad as it's not a failure
                    // to insert the same value with the same actor version
                    // but for simplicity we reject those ops as well
                    return true;
                }
            }
        }
    }
    false
}

fn build_test_reg(prim_ops: Vec<(u8, u8)>) -> TestReg {
    let mut reg = MVReg::default();
    let mut ops = Vec::new();
    for (val, actor) in prim_ops {
        let ctx = reg.read().derive_add_ctx(actor);
        let op = reg.write(val, ctx);
        reg.apply(op.clone());
        ops.push(op);
    }
    TestReg { reg, ops }
}

quickcheck! {
    fn prop_set_with_ctx_from_read(r_ops: Vec<(u8, u8)>, a: u8) -> bool {
        let mut reg = build_test_reg(r_ops).reg;
        let write_ctx = reg.read().derive_add_ctx(a);
        reg.apply(reg.write(23, write_ctx));

        let next_read_ctx = reg.read();
        next_read_ctx.val == vec![23]
    }

    fn prop_merge_idempotent(r_ops: Vec<(u8, u8)>) -> bool {
        let mut r = build_test_reg(r_ops).reg;
        let r_snapshot = r.clone();

        r.merge(r_snapshot.clone());

        assert_eq!(r, r_snapshot);
        true
    }

    fn prop_merge_commutative(
        r1_ops: Vec<(u8, u8)>,
        r2_ops: Vec<(u8, u8)>
    ) -> TestResult {
        if ops_are_not_compatible(&[&r1_ops, &r2_ops]) {
            return TestResult::discard();
        }
        let r1 = build_test_reg(r1_ops);
        let r2 = build_test_reg(r2_ops);
        let mut r1 = r1.reg;
        let mut r2 = r2.reg;

        let r1_snapshot = r1.clone();
        r1.merge(r2.clone());
        r2.merge(r1_snapshot);

        assert_eq!(r1, r2);
        TestResult::from_bool(true)
    }

    fn prop_merge_associative(
        r1_ops: Vec<(u8, u8)>,
        r2_ops: Vec<(u8, u8)>,
        r3_ops: Vec<(u8, u8)>
    ) -> TestResult {
        if ops_are_not_compatible(&[&r1_ops, &r2_ops, &r3_ops]) {
            return TestResult::discard();
        }
        let mut r1 = build_test_reg(r1_ops).reg;
        let mut r2 = build_test_reg(r2_ops).reg;
        let r3 = build_test_reg(r3_ops).reg;
        let r1_snapshot = r1.clone();

        // r1 ^ r2
        r1.merge(r2.clone());

        // (r1 ^ r2) ^ r3
        r1.merge(r3.clone());

        // r2 ^ r3
        r2.merge(r3);

        // r1 ^ (r2 ^ r3)
        r2.merge(r1_snapshot);

        assert_eq!(r1, r2);
        TestResult::from_bool(true)
    }

    fn prop_reset_remove(r_ops: Vec<(u8, u8)>) -> bool {
        let mut r = build_test_reg(r_ops).reg;
        let r_snapshot = r.clone();

        // truncating with the empty clock should be a nop
        r.reset_remove(&VClock::new());
        assert_eq!(r, r_snapshot);

        // truncating with the merge of all val clocks should give us
        // an empty register
        let clock = r.read().add_clock;
        r.reset_remove(&clock);
        assert_eq!(r, MVReg::new());
        true
    }

    fn prop_op_idempotent(r_ops: Vec<(u8, u8)>) -> TestResult {
        let test = build_test_reg(r_ops);
        let mut r = test.reg;
        let r_snapshot = r.clone();
        for op in test.ops.into_iter() {
            r.apply(op);
        }

        assert_eq!(r, r_snapshot);
        TestResult::from_bool(true)
    }


    fn prop_op_commutative(
        o1_ops: Vec<(u8, u8)>,
        o2_ops: Vec<(u8, u8)>
    ) -> TestResult {
        if ops_are_not_compatible(&[&o1_ops, &o2_ops]) {
            return TestResult::discard();
        }
        let o1 = build_test_reg(o1_ops);
        let o2 = build_test_reg(o2_ops);

        let mut r1 = o1.reg;
        let mut r2 = o2.reg;

        for op in o2.ops.into_iter() {
            r1.apply(op);
        }

        for op in o1.ops.into_iter() {
            r2.apply(op);
        }

        assert_eq!(r1, r2);
        TestResult::from_bool(true)
    }


    fn prop_op_associative(
        o1_ops: Vec<(u8, u8)>,
        o2_ops: Vec<(u8, u8)>,
        o3_ops: Vec<(u8, u8)>
    ) -> TestResult {
        if ops_are_not_compatible(&[&o1_ops, &o2_ops, &o3_ops]) {
            return TestResult::discard();
        }
        let o1 = build_test_reg(o1_ops);
        let o2 = build_test_reg(o2_ops);
        let o3 = build_test_reg(o3_ops);
        let mut r1 = o1.reg;
        let mut r2 = o2.reg;


        // r1 <- r2
        for op in o2.ops.into_iter() {
            r1.apply(op);
        }

        // (r1 <- r2) <- r3
        for op in o3.ops.iter().cloned() {
            r1.apply(op);
        }

        // r2 <- r3
        for op in o3.ops.into_iter() {
            r2.apply(op);
        }

        // (r2 <- r3) <- r1
        for op in o1.ops.into_iter() {
            r2.apply(op);
        }

        assert_eq!(r1, r2);
        TestResult::from_bool(true)
    }
}
