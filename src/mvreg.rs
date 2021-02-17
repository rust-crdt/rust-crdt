use core::cmp::Ordering;
use core::convert::Infallible;
use core::fmt::{self, Debug, Display};
use core::mem;

use serde::{Deserialize, Serialize};

use crate::ctx::{AddCtx, ReadCtx};
use crate::{CmRDT, CvRDT, ResetRemove, VClock};

/// MVReg (Multi-Value Register)
/// On concurrent writes, we will keep all values for which
/// we can't establish a causal history.
///
/// ```rust
/// use crdts::{CmRDT, MVReg, Dot, VClock};
/// let mut r1 = MVReg::new();
/// let mut r2 = r1.clone();
/// let r1_read_ctx = r1.read();
/// let r2_read_ctx = r2.read();
///
/// r1.apply(r1.write("bob", r1_read_ctx.derive_add_ctx(123)));
///
/// let op = r2.write("alice", r2_read_ctx.derive_add_ctx(111));
/// r2.apply(op.clone());
///
/// r1.apply(op); // we replicate op to r1
///
/// // Since "bob" and "alice" were added concurrently, we see both on read
/// assert_eq!(r1.read().val, vec!["bob", "alice"]);
/// ```
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MVReg<V, A: Ord> {
    vals: Vec<(VClock<A>, V)>,
}

/// Defines the set of operations over the MVReg
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Op<V, A: Ord> {
    /// Put a value
    Put {
        /// context of the operation
        clock: VClock<A>,
        /// the value to put
        val: V,
    },
}

impl<V: Display, A: Ord + Display> Display for MVReg<V, A> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "|")?;
        for (i, (ctx, val)) in self.vals.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}@{}", val, ctx)?;
        }
        write!(f, "|")
    }
}

impl<V: PartialEq, A: Ord> PartialEq for MVReg<V, A> {
    fn eq(&self, other: &Self) -> bool {
        for dot in self.vals.iter() {
            let num_found = other.vals.iter().filter(|d| d == &dot).count();

            if num_found == 0 {
                return false;
            }
            // sanity check
            assert_eq!(num_found, 1);
        }
        for dot in other.vals.iter() {
            let num_found = self.vals.iter().filter(|d| d == &dot).count();

            if num_found == 0 {
                return false;
            }
            // sanity check
            assert_eq!(num_found, 1);
        }
        true
    }
}

impl<V: Eq, A: Ord> Eq for MVReg<V, A> {}

impl<V, A: Ord> ResetRemove<A> for MVReg<V, A> {
    fn reset_remove(&mut self, clock: &VClock<A>) {
        self.vals = mem::take(&mut self.vals)
            .into_iter()
            .filter_map(|(mut val_clock, val)| {
                val_clock.reset_remove(&clock);
                if val_clock.is_empty() {
                    None // remove this value from the register
                } else {
                    Some((val_clock, val))
                }
            })
            .collect()
    }
}

impl<V, A: Ord> Default for MVReg<V, A> {
    fn default() -> Self {
        Self { vals: Vec::new() }
    }
}

impl<V, A: Ord> CvRDT for MVReg<V, A> {
    type Validation = Infallible;

    fn validate_merge(&self, _other: &Self) -> Result<(), Self::Validation> {
        Ok(())
    }

    fn merge(&mut self, other: Self) {
        self.vals = mem::take(&mut self.vals)
            .into_iter()
            .filter(|(clock, _)| other.vals.iter().filter(|(c, _)| clock < c).count() == 0)
            .collect();

        self.vals.extend(
            other
                .vals
                .into_iter()
                .filter(|(clock, _)| self.vals.iter().filter(|(c, _)| clock < c).count() == 0)
                .filter(|(clock, _)| self.vals.iter().all(|(c, _)| clock != c))
                .collect::<Vec<_>>(),
        );
    }
}

impl<V, A: Ord> CmRDT for MVReg<V, A> {
    type Op = Op<V, A>;
    type Validation = Infallible;

    fn validate_op(&self, _op: &Self::Op) -> Result<(), Self::Validation> {
        Ok(())
    }

    fn apply(&mut self, op: Self::Op) {
        match op {
            Op::Put { clock, val } => {
                if clock.is_empty() {
                    return;
                }
                // first filter out all values that are dominated by the Op clock
                self.vals.retain(|(val_clock, _)| {
                    matches!(
                        val_clock.partial_cmp(&clock),
                        None | Some(Ordering::Greater)
                    )
                });

                // TAI: in the case were the Op has a context that already was present,
                //      the above line would remove that value, the next lines would
                //      keep the val from the Op, so.. a malformed Op could break
                //      commutativity.

                // now check if we've already seen this op
                let mut should_add = true;
                for (existing_clock, _) in self.vals.iter() {
                    if existing_clock > &clock {
                        // we've found an entry that dominates this op
                        should_add = false;
                    }
                }

                if should_add {
                    self.vals.push((clock, val));
                }
            }
        }
    }
}

impl<V, A: Ord + Clone + Debug> MVReg<V, A> {
    /// Construct a new empty MVReg
    pub fn new() -> Self {
        Default::default()
    }

    /// Set the value of the register
    pub fn write(&self, val: V, ctx: AddCtx<A>) -> Op<V, A> {
        Op::Put {
            clock: ctx.clock,
            val,
        }
    }

    /// Consumes the register and returns the values
    pub fn read(&self) -> ReadCtx<Vec<V>, A>
    where
        V: Clone,
    {
        let clock = self.clock();
        let concurrent_vals = self.vals.iter().cloned().map(|(_, v)| v).collect();

        ReadCtx {
            add_clock: clock.clone(),
            rm_clock: clock,
            val: concurrent_vals,
        }
    }

    /// Retrieve the current read context
    pub fn read_ctx(&self) -> ReadCtx<(), A> {
        let clock = self.clock();
        ReadCtx {
            add_clock: clock.clone(),
            rm_clock: clock,
            val: (),
        }
    }

    /// A clock with latest versions of all actors operating on this register
    fn clock(&self) -> VClock<A> {
        self.vals
            .iter()
            .fold(VClock::new(), |mut accum_clock, (c, _)| {
                accum_clock.merge(c.clone());
                accum_clock
            })
    }
}
