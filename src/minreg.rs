use crate::traits::{CmRDT, CvRDT};
use serde::{Deserialize, Serialize};
use std::convert::Infallible;

/// `MinReg` Holds a monotonically decreasing value that implements the Ord trait. For use of floating-point values,
/// you must create a wrapper (or use a crate like `float-ord`).
/// For modelling as a `CvRDT`:
/// ```rust
/// use crdts::{CvRDT,MinReg}
/// let mut a = MinReg{ 3 };
/// let b = MinReg{ 2 };
///
/// a.merge(b);
/// asserteq!(a.val, 2);
/// ```
/// and `CmRDT`:
/// ```rust
/// use crdts::{CmRDT, MinReg}
/// let mut a = MinReg{ 3 };
/// let b = 2;
/// a.apply(b);
/// asserteq!(a.val, 2)
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct MinReg<V> {
    /// `val` is the opaque element contained within this CRDT
    /// Because `val` is monotonic, it also serves as a marker and preserves causality
    pub val: V,
}

impl<V: Default> Default for MinReg<V> {
    fn default() -> Self {
        Self { val: V::default() }
    }
}

impl<V: Ord> CvRDT for MinReg<V> {
    /// Validates whether a merge is safe to perfom (it always is)
    type Validation = Infallible;

    /// Always returns Ok(()) since a validation error is Infallible
    fn validate_merge(&self, _other: &Self) -> Result<(), Self::Validation> {
        Ok(())
    }

    /// Combines two `MinReg` instances according to the value that is smallest
    fn merge(&mut self, MinReg { val }: Self) {
        self.update(val)
    }
}

impl<V: Ord> CmRDT for MinReg<V> {
    // MinRegs's are small enough that we can replicate
    // the entire state as an Op
    type Op = V;

    // No operation is invalid so we can safely return `Ok(())`
    type Validation = Infallible;

    /// Just return Ok(())
    fn validate_op(&self, _op: &Self::Op) -> Result<(), Self::Validation> {
        Ok(())
    }

    /// Applies an operation to a MinReg CmRDT
    fn apply(&mut self, op: Self::Op) {
        // Since type Op = V, we need to wrap MinReg around op.
        // If more fields are added to the MinReg struct, change Op to Self
        self.update(op)
    }
}

impl<V: Ord> MinReg<V> {
    /// Constructs a MinReg initialized with the specified value `val`.
    pub fn new(&mut self, val: V) -> Self {
        MinReg { val }
    }

    /// Updates the value of the MinReg. `val` is always monotonically decreasing.
    pub fn update(&mut self, val: V) {
        if val < self.val {
            self.val = val
        }
    }

    /// Generates a write op (i.e: a val: V)
    pub fn write(&self, val: V) -> <MinReg<V> as CmRDT>::Op {
        val
    }

    /// Reads the current value of the registers:
    pub fn read(&self) -> &V {
        &self.val
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    /// TODO: I feel like the default should be Inf??
    fn test_default() {
        let reg = MinReg::default();
        assert_eq!(reg, MinReg { val: 0 });
    }

    #[test]
    fn test_update() {
        // Create a `MinReg` with initial value of 1
        let mut reg = MinReg { val: 1 };
        reg.update(0);

        // normal update: the value of the register decreases to some other value
        // EXPECTED: success, the val is updated since the current value of the register is greater than 0
        assert_eq!(reg, MinReg { val: 0 });

        // stale update: the value of the register is less than the incoming one
        // EXPECTED: success, the val is not updated since the current value is already less than 1
        reg.update(1);
        assert_eq!(reg, MinReg { val: 0 });

        // Idempotency: Applying the same update is a no-op
        // EXPECTED: success, the val is still equal to 0 because 0 ≮ 0
        reg.update(0);
        assert_eq!(reg, MinReg { val: 0 });

        // Test validate_op and validate_merge returns Ok(())
        // EXPECTED: success, the validation callers only return Ok(())
        let op = reg.write(-1);
        assert_eq!(reg.validate_op(&op), Ok(()));

        let other = MinReg { val: -2 };
        assert_eq!(reg.validate_merge(&other), Ok(()));
    }
    #[test]
    fn test_read() {
        // Create a `MinReg` with initial value of 1
        let reg = MinReg { val: 1 };
        let val = reg.read();
        assert_eq!(*val, reg.val);
    }

    #[test]
    fn test_write() {
        // Create a `MinReg` with initial value of 5
        let a = MinReg { val: 5 };

        // Create a `MinReg` with initial value of 6
        let mut b = MinReg { val: 6 };

        // Create a write op:
        let op = b.write(a.val);

        // Apply the op:
        b.apply(op);

        assert_eq!(b.val, 5);
    }
}
