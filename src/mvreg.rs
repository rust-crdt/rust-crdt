use serde::de::DeserializeOwned;
use serde::Serialize;

use std::fmt::Debug;

use error::{Error, Result};
use vclock::{VClock, Dot, Actor};
use traits::{Causal, CmRDT, CvRDT};

pub trait Val: Debug + Eq + Clone + Send + Serialize + DeserializeOwned {}
impl<T: Debug + Eq + Clone + Send + Serialize + DeserializeOwned> Val for T {}

#[serde(bound(deserialize = ""))]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MVReg<A: Actor, V: Val> {
    pub vals: Vec<(VClock<A>, V)>
}

// TODO: to be consistent, should be <V, A> not <A, V>
#[serde(bound(deserialize = ""))]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Op<A: Actor, V: Val> {
    Put { context: VClock<A>, val: V }
}

impl<A: Actor, V: Val> PartialEq for MVReg<A, V> {
    fn eq(&self, other: &Self) -> bool {
        for dot in self.vals.iter() {
            let mut num_found = other.vals.iter().filter(|d| d == &dot).count();

            if num_found == 0 {
                return false
            }
            // sanity check
            assert_eq!(num_found, 1);
        }
        for dot in other.vals.iter() {
            let mut num_found = self.vals.iter().filter(|d| d == &dot).count();

            if num_found == 0 {
                return false
            }
            // sanity check
            assert_eq!(num_found, 1);
        }
        true
    }
}

impl<A: Actor, V: Val> Eq for MVReg<A, V> {}

impl<A: Actor, V: Val> Causal<A> for MVReg<A, V> {
    fn truncate(&mut self, clock: &VClock<A>) {
        self.vals = self.vals.clone().into_iter()
            .filter_map(|(mut val_clock, val)| {
                val_clock.subtract(&clock);
                if val_clock.is_empty() {
                    None
                } else {
                    Some((val_clock, val))
                }
            })
            .collect()
    }
}

impl<A: Actor, V: Val> Default for MVReg<A, V> {
    fn default() -> Self {
        MVReg { vals: Vec::new() }
    }
}

impl<A: Actor, V: Val> CvRDT for MVReg<A, V> {
    type Error = Error;

    fn merge(&mut self, other: &Self) -> Result<()> {
        let mut vals = Vec::new();
        for (clock, val) in self.vals.iter() {
            let num_dominating = other.vals
                .iter()
                .filter(|(c, _)| clock < c)
                .count();
            if num_dominating == 0 {
                vals.push((clock.clone(), val.clone()));
            }
        }
        for (clock, val) in other.vals.iter() {
            let num_dominating = self.vals
                .iter()
                .filter(|(c, _)| clock < c)
                .count();
            if num_dominating == 0 {
                let mut is_new = true;
                for (existing_c, existing_v) in vals.iter() {
                    if existing_c == clock {
                        // sanity check
                        assert_eq!(val, existing_v);
                        is_new = false;
                        break;
                    }
                }
                if is_new {
                    vals.push((clock.clone(), val.clone()));
                }
            }
        }
        self.vals = vals;
        Ok(())
    }
}

impl<A: Actor, V: Val> CmRDT for MVReg<A, V> {
    type Op = Op<A, V>;
    type Error = Error;

    fn apply(&mut self, op: Self::Op) -> Result<()> {
        match op {
            Op::Put { context, val } => {
                if context.is_empty() {
                    return Ok(());
                }
                // first filter out all values that are dominated by the Op context
                self.vals.retain(|(val_context, _)| !(val_context < &context));

                // now check if we've already seen this op
                let mut should_add = true;
                for (existing_ctx, existing_val) in self.vals.iter() {

                    if existing_ctx == &context && existing_val != &val {
                        return Err(Error::ConflictingDot);
                    } else if existing_ctx >= &context {
                        // we've found an entry that descends this op
                        should_add = false;
                        // don't break out of this loop!
                        // we need to finish our conflicting dot check
                    }
                }
                if should_add {
                    self.vals.push((context, val));
                }
            }
        }
        Ok(())
    }
}

impl<A: Actor, V: Val> MVReg<A, V> {
    pub fn new() -> Self {
        MVReg::default()
    }

    pub fn set(&self, val: V, dot: Dot<A>) -> Op<A, V> {
        let mut context = self.context();
        context.apply(dot).unwrap();
        Op::Put { context, val }
    }

    pub fn get(&self) -> (Vec<&V>, VClock<A>) {
        let concurrent_vals = self.vals.iter().map(|(_, v)| v).collect();
        let context = self.context();
        (concurrent_vals, context)
    }

    pub fn context(&self) -> VClock<A> {
        self.vals.iter()
            .fold(VClock::new(), |mut accum_clock, (c, _)| {
                accum_clock.merge(&c);
                accum_clock
            })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::fmt;
    use quickcheck::{Arbitrary, Gen, TestResult};

    #[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
    struct TActor(u8);
    
    #[derive(Debug, Clone)]
    struct TestReg<A: Actor, V: Val> {
        reg: MVReg<A, V>,
        ops: Vec<Op<A, V>>
    }

    impl<A: Actor, V: Val> TestReg<A, V> {
        fn incompat(&self, other: &Self) -> bool {
            for (c1, v1) in self.reg.vals.iter() {
                for (c2, v2) in other.reg.vals.iter() {
                    if c1 == c2 && v1 != v2 {
                        return true;
                    }
                }
            }

            for Op::Put { context: c, val: v } in self.ops.iter() {
                for Op::Put { context: other_c, val: other_v } in other.ops.iter() {
                    if c == other_c && v != other_v {
                        return true;
                    }
                }
            }

            return false;
        }
    }

    impl Arbitrary for TActor {
        fn arbitrary<G: Gen>(g: &mut G) -> Self {
            let actor: u8 = g.gen_range(0, 10);
            TActor(actor)
        }
        fn shrink(&self) -> Box<Iterator<Item = Self>> {
            Box::new(vec![].into_iter())
        }
    }

    impl Debug for TActor {
        fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
            write!(formatter, "A{}", self.0)
        }
    }
    
    impl<A: Actor + Arbitrary, V: Val + Arbitrary>  Arbitrary for TestReg<A, V> {
        fn arbitrary<G: Gen>(g: &mut G) -> Self {
            let mut reg: MVReg<A, V> = MVReg::default();
            let num_ops = g.gen::<u8>() % 20;
            let mut ops = Vec::with_capacity(num_ops as usize);
            for _ in 0..num_ops {
                let val = V::arbitrary(g);
                let actor = A::arbitrary(g);
                let dot = Dot {
                    actor: actor.clone(),
                    counter: reg.context().increment(actor)
                };
                let op = reg.set(val, dot);
                reg.apply(op.clone());
                ops.push(op);
            }
            TestReg { reg, ops }
        }

        fn shrink(&self) -> Box<Iterator<Item = Self>> {
            let mut shrunk = vec![];

            for i in (0..self.ops.len()).into_iter().rev() {
                let mut reg = MVReg::new();
                let mut ops = Vec::with_capacity(self.ops.len() - 1);
                
                for (j, op) in self.ops.iter().cloned().enumerate() {
                    if i == j {
                        continue;
                    }

                    reg.apply(op.clone()).unwrap();
                    ops.push(op);
                }

                shrunk.push(TestReg { reg, ops });

                let Op::Put { context, val } = self.ops[i].clone();
                for dot in context.clone().into_iter() {
                    let shrunk_context: VClock<A> = context.clone()
                        .into_iter()
                        .filter(|d| d != &dot)
                        .collect();

                    if shrunk_context.is_empty() {
                        continue;
                    }
                    
                    let mut reg = MVReg::new();
                    let mut ops = self.ops.clone();
                    ops[i] = Op::Put {
                        context: shrunk_context,
                        val: val.clone()
                    };
                    let mut conflict = false;
                    for op in ops.iter() {
                        conflict = reg.apply(op.clone()).is_err();
                        if conflict { break; }
                    }
                    if !conflict {
                        shrunk.push(TestReg { reg, ops });
                    }
                }
            }
            Box::new(shrunk.into_iter())
        }
    }

    #[test]
    fn test_apply() {
        let mut reg = MVReg::new();
        let context = VClock::from(Dot { actor: 2, counter: 1 });
        reg.apply(Op::Put { context: context.clone(), val: 71 }).unwrap();
        assert_eq!(reg, MVReg { vals: vec![(context, 71)] });
    }

    #[test]
    fn test_set_should_not_mutate_reg() {
        let reg = MVReg::new();
        let op = reg.set(32, Dot { actor: 1, counter: 2 });
        assert_eq!(reg, MVReg::new());
        let mut reg = reg;
        reg.apply(op);

        let (vals, ctx) = reg.get();
        assert_eq!(vals, vec![&32]);
        assert_eq!(ctx, VClock::from(Dot { actor: 1, counter: 2 }));
    }

    #[test]
    fn test_concurrent_update_with_same_value_dont_collapse_on_merge() {
        // this is important to prevent because it breaks commutativity
        let mut r1 = MVReg::new();
        let mut r2 = MVReg::new();

        let op1 = r1.set(23, Dot { actor: 4, counter: 1 });
        let op2 = r2.set(23, Dot { actor: 7, counter: 1 });
        r1.apply(op1);
        r2.apply(op2);

        r1.merge(&r2).unwrap();
        assert_eq!(r1.get(), (vec![&23, &23], VClock::from(vec![(4, 1), (7, 1)])));
    }

    #[test]
    fn test_concurrent_update_with_same_value_collapse_on_apply() {
        // this is important to prevent because it breaks commutativity
        let mut r1 = MVReg::new();
        let r2 = MVReg::new();

        let op1 = r1.set(23, Dot { actor: 4, counter: 1 });
        r1.apply(op1);
        let op2 = r2.set(23, Dot { actor: 7, counter: 1 });

        r1.apply(op2).unwrap();
        assert_eq!(r1.get(), (vec![&23, &23], VClock::from(vec![(4, 1), (7, 1)])));
    }

    #[test]
    fn test_multi_get() {
        let mut r1 = MVReg::new();
        let mut r2 = MVReg::new();
        let op1 = r1.set(32, Dot { actor: 1, counter: 1 });
        let op2 = r2.set(82, Dot { actor: 2, counter: 1 });
        r1.apply(op1).unwrap();
        r2.apply(op2).unwrap();

        r1.merge(&r2).unwrap();
        let (vals, _) = r1.get();
        assert!(vals == vec![&32, &82] || vals == vec![&82, &32]);
    }

    #[test]
    fn test_op_commute_quickcheck1() {
        let mut reg1 = MVReg::new();
        let mut reg2 = MVReg::new();

        let op1 = Op::Put { context: Dot { actor: 1, counter: 1 }.into(), val: 1 };
        let op2 = Op::Put { context: Dot { actor: 2, counter: 1 }.into(), val: 2 };

        reg2.apply(op2.clone()).unwrap();
        reg2.apply(op1.clone()).unwrap();
        reg1.apply(op1).unwrap();
        reg1.apply(op2).unwrap();

        assert_eq!(reg1, reg2);
    }

    quickcheck! {
        fn prop_sanity_check_arbitrary(r: TestReg<TActor, u8>) -> bool {
            let mut reg = MVReg::new();
            for op in r.ops {
                reg.apply(op).unwrap();
            }

            assert_eq!(reg, r.reg);
            true
        }

        fn prop_set_with_dot_from_get_context(r: TestReg<TActor, u8>, a: TActor) -> bool {
            let mut reg = r.reg;
            let (_, ctx) = reg.get();
            let counter = ctx.get(&a) + 1;
            let dot = Dot {
                actor: a,
                counter
            };
            let op = reg.set(23, dot);
            reg.apply(op);

            let (vals, _) = reg.get();
            vals == vec![&23]
        }
        
        fn prop_merge_idempotent(r: TestReg<TActor, u8>) -> bool {
            let mut r = r.reg;
            let r_snapshot = r.clone();

            assert!(r.merge(&r_snapshot).is_ok());

            assert_eq!(r, r_snapshot);
            true
        }

        fn prop_merge_commutative(r1: TestReg<TActor, u8>, r2: TestReg<TActor, u8>) -> TestResult {
            if r1.incompat(&r2) {
                return TestResult::discard();
            }
            let mut r1 = r1.reg;
            let mut r2 = r2.reg;

            let r1_snapshot = r1.clone();
            assert!(r1.merge(&r2).is_ok());
            assert!(r2.merge(&r1_snapshot).is_ok());

            assert_eq!(r1, r2);
            TestResult::from_bool(true)
        }

        fn prop_merge_associative(r1: TestReg<TActor, u8>, r2: TestReg<TActor, u8>, r3: TestReg<TActor, u8>) -> TestResult {
            if r1.incompat(&r2) || r1.incompat(&r3) || r2.incompat(&r3) {
                return TestResult::discard();
            }
            let mut r1 = r1.reg;
            let mut r2 = r2.reg;
            let r3 = r3.reg;
            let r1_snapshot = r1.clone();
            
            // r1 ^ r2
            assert!(r1.merge(&r2).is_ok());

            // (r1 ^ r2) ^ r3
            assert!(r1.merge(&r3).is_ok());

            // r2 ^ r3
            assert!(r2.merge(&r3).is_ok());

            // r1 ^ (r2 ^ r3)
            assert!(r2.merge(&r1_snapshot).is_ok());

            assert_eq!(r1, r2);
            TestResult::from_bool(true)
        }

        fn prop_truncate(r: TestReg<TActor, u8>) -> bool{
            let mut r = r.reg;
            let r_snapshot = r.clone();

            // truncating with the empty clock should be a nop
            r.truncate(&VClock::new());
            assert_eq!(r, r_snapshot);

            // truncating with the merge of all val clocks should give us
            // an empty register
            let clock = r.vals
                .iter()
                .fold(VClock::new(), |mut accum_clock, (c, _)| {
                    accum_clock.merge(&c);
                    accum_clock
                });

            r.truncate(&clock);
            assert_eq!(r, MVReg::new());
            true
        }

        fn prop_op_idempotent(test: TestReg<TActor, u8>) -> TestResult {
            let mut r = test.reg;
            let r_snapshot = r.clone();
            for op in test.ops {
                assert!(r.apply(op).is_ok());
            }

            assert_eq!(r, r_snapshot);
            TestResult::from_bool(true)
        }

        fn prop_op_commutative(o1: TestReg<TActor, u8>, o2: TestReg<TActor, u8>) -> TestResult {
            if o1.incompat(&o2) {
                return TestResult::discard();
            }

            let mut r1 = o1.reg;
            let mut r2 = o2.reg;

            for op in o2.ops {
                r1.apply(op).unwrap();
            }
            
            for op in o1.ops {
                r2.apply(op).unwrap();
            }

            assert_eq!(r1, r2);
            TestResult::from_bool(true)
        }

        fn prop_op_associative(o1: TestReg<TActor, u8>, o2: TestReg<TActor, u8>, o3: TestReg<TActor, u8>) -> TestResult {
            if o1.incompat(&o2) || o1.incompat(&o3) || o2.incompat(&o3) {
                return TestResult::discard();
            }

            let mut r1 = o1.reg;
            let mut r2 = o2.reg;


            // r1 <- r2
            for op in o2.ops {
                r1.apply(op).unwrap();
            }

            // (r1 <- r2) <- r3
            for op in o3.ops.iter().cloned() {
                r1.apply(op).unwrap();
            }

            // r2 <- r3
            for op in o3.ops {
                r2.apply(op).unwrap();
            }

            // (r2 <- r3) <- r1
            for op in o1.ops {
                r2.apply(op).unwrap();
            }

            assert_eq!(r1, r2);
            TestResult::from_bool(true)
        }
    }
}