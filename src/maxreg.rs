use crate::traits::{CmRDT, CvRDT};
use serde::{Deserialize, Serialize};
use std::convert::Infallible;

/// `MaxReg` Holds a monotonically increasing value that implements the Ord trait. For use of floating-point values,
/// you must create a wrapper (or use a crate like `float-ord`)
/// For modelling as a `CvRDT`:
/// ```rust
/// use crdts::{CvRDT,MaxReg};
/// let mut a = MaxReg{ val: 3 };
/// let b = MaxReg{ val: 2 };
///
/// a.merge(b);
/// assert_eq!(a.val, 3);
/// ```
/// and `CmRDT`:
/// ```rust
/// use crdts::{CmRDT, MaxReg};
/// let mut a = MaxReg{ val: 3 };
/// let b = 2;
/// a.apply(b);
/// assert_eq!(a.val, 3);
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct MaxReg<V> {
    /// `val` is the opaque element contained within this CRDT
    /// Because `val` is monotonic, it also serves as a marker and preserves causality
    pub val: V,
}

impl<V: Default> Default for MaxReg<V> {
    fn default() -> Self {
        Self { val: V::default() }
    }
}

impl<V: Ord> CvRDT for MaxReg<V> {
    /// Validates whether a merge is safe to perfom (it always is)
    type Validation = Infallible;

    /// Always returns Ok(()) since a validation error is Infallible
    fn validate_merge(&self, _other: &Self) -> Result<(), Self::Validation> {
        Ok(())
    }

    /// Combines two `MaxReg` instances according to the value that is greatest
    fn merge(&mut self, MaxReg { val }: Self) {
        self.update(val)
    }
}

impl<V: Ord> CmRDT for MaxReg<V> {
    // MaxRegs's are small enough that we can replicate
    // the entire state as an Op
    type Op = V;

    // No operation is invalid so we can safely return `Ok(())`
    type Validation = Infallible;

    /// Just returns Ok(())
    fn validate_op(&self, _op: &Self::Op) -> Result<(), Self::Validation> {
        Ok(())
    }

    /// Applies an operation to a MaxReg CmRDT
    fn apply(&mut self, op: Self::Op) {
        // Since type Op = V, we need to wrap MaxReg around op.
        // If more fields are added to the MaxReg struct, change Op to Self
        self.update(op)
    }
}

impl<V: Ord> MaxReg<V> {
    /// Constructs a MaxReg initialized with the specified value `val`.
    pub fn new(&mut self, val: V) -> Self {
        MaxReg { val }
    }

    /// Updates the value of the MaxReg. `val` is always monotonically increasing.
    pub fn update(&mut self, val: V) {
        if val > self.val {
            self.val = val
        }
    }

    /// Generates a write op (i.e: a val: V)
    pub fn write(&self, val: V) -> <MaxReg<V> as CmRDT>::Op {
        val
    }

    /// Reads the current value of the register.
    pub fn read(&self) -> &V {
        &self.val
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    /// TODO: I feel like the default should be -Inf??
    fn test_default() {
        let reg = MaxReg::default();
        assert_eq!(reg, MaxReg { val: 0 });
    }

    #[test]
    fn test_update() {
        // Create a `MaxReg` with initial value of 1
        let mut reg = MaxReg { val: 1 };
        reg.update(2);

        // normal update: the value of the register increases to some other value
        // EXPECTED: success, the val is updated since the current value of the register is less than 2
        assert_eq!(reg, MaxReg { val: 2 });

        // stale update: the value of the register is greater than the incoming one
        // EXPECTED: success, the val is not updated since the current value is already greater than 1
        reg.update(1);
        assert_eq!(reg, MaxReg { val: 2 });

        // Idempotency: Applying the same update is a no-op
        // EXPECTED: success, the val is still equal to 2 because 2 ≯ 2
        reg.update(2);
        assert_eq!(reg, MaxReg { val: 2 });

        // Test validate_op and validate_merge returns Ok(())
        // EXPECTED: success, the validation callers only return Ok(())
        let op = reg.write(3);
        assert_eq!(reg.validate_op(&op), Ok(()));

        let other = MaxReg { val: 4 };
        assert_eq!(reg.validate_merge(&other), Ok(()));
    }
    #[test]
    fn test_read() {
        // Create a `MaxReg` with initial value of 1
        let reg = MaxReg { val: 1 };
        let val = reg.read();
        assert_eq!(*val, reg.val);
    }

    #[test]
    fn test_write() {
        // Create a `MinReg` with initial value of 6
        let a = MaxReg { val: 6 };

        // Create a `MinReg` with initial value of 5
        let mut b = MaxReg { val: 5 };

        // Create a write op:
        let op = b.write(a.val);

        // Apply the op:
        b.apply(op);

        assert_eq!(b.val, 6);
    }
}
