use crate::traits::{CmRDT, CvRDT};
use serde::{Deserialize, Serialize};
use std::{error, fmt};

/// `MaxReg` Holds a monotonically increasing value that implements the Ord trait. For use of floating-point values,
/// you must create a wrapper (or use a crate like `float-ord`)
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct MaxReg<V: Ord + Copy> {
    /// `val` is the opaque element contained within this CRDT
    /// Because `val` is monotonic, it also serves as a marker and preserves causality
    pub val: V,
}

impl<V: Default + Ord + Copy> Default for MaxReg<V> {
    fn default() -> Self {
        Self { val: V::default() }
    }
}

/// The Type of validation errors that may occur for an MaxReg.
#[derive(Debug, PartialEq)]
pub enum Validation {
    /// A conflicting change to a MaxReg CRDT is when the value being validated is less-than self.val
    ConflictingValue,
}

impl error::Error for Validation {
    fn description(&self) -> &str {
        match self {
            Validation::ConflictingValue => {
                "Comparison failed! `val` should be monotonically increasing."
            }
        }
    }
}

impl fmt::Display for Validation {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl<V: Ord + Copy> CvRDT for MaxReg<V> {
    type Validation = Validation;
    /// Validates whether a merge is safe to perfom
    ///
    /// Returns an error if `val` is greater than the proposed new value
    /// ```
    /// use crdts::{maxreg, MaxReg, CvRDT};
    /// let mut ub_1 = MaxReg { val: 1};
    /// let ub_2 = MaxReg { val: 0 };
    /// // errors!
    /// assert_eq!(ub_1.validate_merge(&ub_2), Err(maxreg::Validation::ConflictingVal));
    /// ```
    fn validate_merge(&self, other: &Self) -> Result<(), Self::Validation> {
        self.validate_update(&other.val)
    }

    /// Combines two `MaxReg` instances according to the value that is greatest
    fn merge(&mut self, MaxReg { val }: Self) {
        self.update(val)
    }
}

impl<V: Ord + Copy> CmRDT for MaxReg<V> {
    // MaxRegs's are small enough that we can replicate
    // the entire state as an Op
    type Op = Self;
    type Validation = Validation;

    fn validate_op(&self, op: &Self::Op) -> Result<(), Validation> {
        self.validate_update(&op.val)
    }

    fn apply(&mut self, op: Self::Op) {
        self.merge(op)
    }
}

impl<V: Ord + Copy> MaxReg<V> {
    /// Constructs a MaxReg initialized with the specified value `val`.
    pub fn new(&mut self, val: V) -> Self {
        MaxReg { val }
    }

    /// Updates the value of the MaxReg. `val` is always monotonically increasing.
    pub fn update(&mut self, val: V) {
        self.val = std::cmp::max(self.val, val);
    }

    /// Since `val` is a monotonic value, validation is simply to call update
    pub fn validate_update(&self, val: &V) -> Result<(), Validation> {
        if &self.val > val {
            Err(Validation::ConflictingValue)
        } else {
            Ok(())
        }
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

        //bad update: validating an incoming value throws an error
        //EXPECTED: Err()
        assert_eq!(reg.validate_update(&1), Err(Validation::ConflictingValue));

        // Applying the update despite the validation error is a no-op (i.e: idempotency)
        reg.update(1);
        assert_eq!(reg, MaxReg { val: 2 });
    }
}
