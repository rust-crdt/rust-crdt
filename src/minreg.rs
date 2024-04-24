use crate::traits::{CmRDT, CvRDT};
use serde::{Deserialize, Serialize};
use std::{error, fmt};

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
/// let b = MinReg{ 2 };
/// a.apply(b); // MinReg is also an Op
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct MinReg<V: Ord + Copy> {
    /// `val` is the opaque element contained within this CRDT
    /// Because `val` is monotonic, it also serves as a marker and preserves causality
    pub val: V,
}

impl<V: Default + Ord + Copy> Default for MinReg<V> {
    fn default() -> Self {
        Self { val: V::default() }
    }
}

/// The Type of validation errors that may occur for an MinReg.
#[derive(Debug, PartialEq)]
pub enum Validation {
    /// A conflicting change to a MinReg CRDT is when the value being validated is greater-than self.val
    ConflictingValue,
}

impl error::Error for Validation {
    fn description(&self) -> &str {
        match self {
            Validation::ConflictingValue => {
                "Comparison failed! `val` should be monotonically decreasing."
            }
        }
    }
}

impl fmt::Display for Validation {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl<V: Ord + Copy> CvRDT for MinReg<V> {
    type Validation = Validation;
    /// Validates whether a merge is safe to perfom
    ///
    /// Returns an error if `val` is greater than the proposed new value
    /// ```
    /// use crdts::{minreg, MinReg, CvRDT};
    /// let mut lb_1 = MinReg { val: 1};
    /// let lb_2 = MinReg { val: 2 };
    /// // errors!
    /// assert_eq!(ub_1.validate_merge(&ub_2), Err(minreg::Validation::ConflictingVal));
    /// ```
    fn validate_merge(&self, other: &Self) -> Result<(), Self::Validation> {
        self.validate_update(&other.val)
    }

    /// Combines two `MinReg` instances according to the value that is smallest
    fn merge(&mut self, MinReg { val }: Self) {
        self.update(val)
    }
}

impl<V: Ord + Copy> CmRDT for MinReg<V> {
    // MinRegs's are small enough that we can replicate
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

impl<V: Ord + Copy> MinReg<V> {
    /// Constructs a MinReg initialized with the specified value `val`.
    pub fn new(&mut self, val: V) -> Self {
        MinReg { val }
    }

    /// Updates the value of the MinReg. `val` is always monotonically decreasing.
    pub fn update(&mut self, val: V) {
        self.val = std::cmp::min(self.val, val)
    }

    /// Since `val` is a monotonic value, validation is simply to call update
    /// TODO: confirm if this is correct behavior?
    pub fn validate_update(&self, val: &V) -> Result<(), Validation> {
        if &self.val < val {
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

        // bad update: validating an incoming value throws an `ConflictingValue`
        // EXPECTED: Err()
        assert_eq!(reg.validate_update(&1), Err(Validation::ConflictingValue));

        // Applying the update despite the validation error is a no-op
        reg.update(1);
        assert_eq!(reg, MinReg { val: 0 });
    }
}
