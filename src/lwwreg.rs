use serde::{Deserialize, Serialize};

use crate::{error::Result, Error, FunkyCmRDT, FunkyCvRDT};

/// `LWWReg` is a simple CRDT that contains an arbitrary value
/// along with an `Ord` that tracks causality. It is the responsibility
/// of the user to guarantee that the source of the causal element
/// is monotonic. Don't use timestamps unless you are comfortable
/// with divergence.
///
/// `M` is a marker. It must grow monotonically *and* must be globally unique
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct LWWReg<V, M> {
    /// `val` is the opaque element contained within this CRDT
    pub val: V,
    /// `marker` should be a monotonic value associated with this val
    pub marker: M,
}

impl<V: Default, M: Ord + Default> Default for LWWReg<V, M> {
    fn default() -> Self {
        Self {
            val: V::default(),
            marker: M::default(),
        }
    }
}

impl<V: PartialEq, M: Ord> FunkyCvRDT for LWWReg<V, M> {
    /// Combines two `LWWReg` instances according to the marker that
    /// tracks causality. Returns an error if the marker is identical but the
    /// contained element is different.
    /// ```
    /// use crdts::{LWWReg, FunkyCvRDT};
    /// let mut l1 = LWWReg { val: 1, marker: 2 };
    /// let l2 = LWWReg { val: 3, marker: 2 };
    /// // errors!
    /// assert!(l1.merge(l2).is_err());
    /// ```
    fn merge(&mut self, LWWReg { val, marker }: Self) -> Result<()> {
        self.update(val, marker)
    }
}

impl<V: PartialEq, M: Ord> FunkyCmRDT for LWWReg<V, M> {
    // LWWReg's are small enough that we can replicate
    // the entire state as an Op
    type Op = Self;

    fn apply(&mut self, op: Self::Op) -> Result<()> {
        self.merge(op)
    }
}

impl<V: PartialEq, M: Ord> LWWReg<V, M> {
    /// Updates value witnessed by the given marker.
    /// An Err is returned if the given marker is exactly
    /// equal to the current marker
    ///
    /// ```
    /// use crdts::LWWReg;
    /// let mut reg = LWWReg { val: 1, marker: 2 };
    ///
    /// // updating with a smaller marker is a no-op
    /// assert!(reg.update(2, 1).is_ok());
    /// assert_eq!(reg.val, 1);
    ///
    /// // updating with existing marker fails
    /// assert!(reg.update(2, 2).is_err());
    /// assert_eq!(reg, LWWReg { val: 1, marker: 2 });
    ///
    /// // updating with same val and marker succeeds
    /// assert!(reg.update(1, 2).is_ok());
    /// assert_eq!(reg, LWWReg { val: 1, marker: 2 });
    ///
    /// // updating with descendent marker succeeds
    /// assert!(reg.update(2, 3).is_ok());
    /// assert_eq!(reg, LWWReg { val: 2, marker: 3 });
    /// ```
    pub fn update(&mut self, val: V, marker: M) -> Result<()> {
        if self.marker < marker {
            self.val = val;
            self.marker = marker;
            Ok(())
        } else if self.marker == marker && val != self.val {
            Err(Error::ConflictingMarker)
        } else {
            // Either the given marker is smaller than the marker in the
            // register (meaning we've seen this update already) or the marker
            // and val are the same as is currently stored, either way:
            // this is a no-op.
            Ok(())
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use quickcheck::{quickcheck, TestResult};

    #[test]
    fn test_default() {
        let reg = LWWReg::default();
        assert_eq!(reg, LWWReg { val: "", marker: 0 });
    }

    #[test]
    fn test_update() {
        let mut reg = LWWReg {
            val: 123,
            marker: 0,
        };

        // normal update: new marker is a descended of current marker
        // EXPECTED: success, the val and marker are update
        assert!(reg.update(32, 2).is_ok());
        assert_eq!(reg, LWWReg { val: 32, marker: 2 });

        // stale update: new marker is an ancester of the current marker
        // EXPECTED: succes, no-op
        assert!(reg.update(57, 1).is_ok());
        assert_eq!(reg, LWWReg { val: 32, marker: 2 });

        // redundant update: new marker and val is same as of the current state
        // EXPECTED: success, no-op
        assert!(reg.update(32, 2).is_ok());
        assert_eq!(reg, LWWReg { val: 32, marker: 2 });

        // bad update: new marker same as of the current marker but not value
        // EXPECTED: error
        assert_eq!(reg.update(4000, 2), Err(Error::ConflictingMarker));
        assert_eq!(reg, LWWReg { val: 32, marker: 2 });
    }

    fn build_from_prim(prim: (u8, u16)) -> LWWReg<u8, (u16, u8)> {
        // we make the marker a tuple so that we avoid conflicts
        LWWReg {
            val: prim.0,
            marker: (prim.1, prim.0),
        }
    }

    quickcheck! {
        fn prop_associative(r1_prim: (u8, u16), r2_prim: (u8, u16), r3_prim: (u8, u16)) -> TestResult {
            let mut r1 = build_from_prim(r1_prim);
            let mut r2 = build_from_prim(r2_prim);
            let r3 = build_from_prim(r3_prim);

            let has_conflicting_marker = (r1.marker == r2.marker && r1.val != r2.val)
                || (r1.marker == r3.marker && r1.val != r3.val)
                || (r2.marker == r3.marker && r2.val != r3.val);

            if has_conflicting_marker {
                return TestResult::discard();
            }

            let mut r1_snapshot = r1.clone();

            // (r1 ^ r2) ^ r3
            assert!(r1.merge(r2.clone()).is_ok());
            assert!(r1.merge(r3.clone()).is_ok());

            // r1 ^ (r2 ^ r3)
            assert!(r2.merge(r3).is_ok());
            assert!(r1_snapshot.merge(r2).is_ok());

            // (r1 ^ r2) ^ r3 = r1 ^ (r2 ^ r3)
            TestResult::from_bool(r1 == r1_snapshot)
        }

        fn prop_commutative(r1_prim: (u8, u16), r2_prim: (u8, u16)) -> TestResult {
            let mut r1 = build_from_prim(r1_prim);
            let mut r2 = build_from_prim(r2_prim);

            if r1.marker == r2.marker && r1.val != r2.val {
                return TestResult::discard();
            }
            let r1_snapshot = r1.clone();

            // r1 ^ r2
            assert!(r1.merge(r2.clone()).is_ok());

            // r2 ^ r1
            assert!(r2.merge(r1_snapshot).is_ok());

            // r1 ^ r2 = r2 ^ r1
            TestResult::from_bool(r1 == r2)
        }

        fn prop_idempotent(r_prim: (u8, u16)) -> bool {
            let mut r = build_from_prim(r_prim);
            let r_snapshot = r.clone();

            // r ^ r
            assert!(r.merge(r_snapshot.clone()).is_ok());
            // r ^ r = r
            r == r_snapshot
        }
    }
}
