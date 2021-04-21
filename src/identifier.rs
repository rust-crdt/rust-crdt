//! Dense Identifiers.
//!
//! It's sometimes usefult to be able to create identifiers for which we know there
//! is always space between values to create another.

//! That is, if we have identifiers `a`, `b` with `a != b` then we can always construct
//! an  identifier `c` s.t. `a < c < b` or `a > c > b`.
//!
//! The GList and List CRDT's rely on this property so that we may always insert elements
//! between any existing elements.
use core::cmp::Ordering;
use core::fmt;

use num::{BigRational, One, Zero};
use quickcheck::{Arbitrary, Gen};
use serde::{Deserialize, Serialize};

fn rational_between(low: Option<&BigRational>, high: Option<&BigRational>) -> BigRational {
    match (low, high) {
        (None, None) => BigRational::zero(),
        (Some(low), None) => low + BigRational::one(),
        (None, Some(high)) => high - BigRational::one(),
        (Some(low), Some(high)) => (low + high) / BigRational::from_integer(2.into()),
    }
}

/// A dense Identifier, if you have two identifiers that are different, we can
/// always construct an identifier between them.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub struct Identifier<T>(Vec<(BigRational, T)>);

impl<T: Ord> PartialOrd for Identifier<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T: Ord> Ord for Identifier<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        let mut self_path = self.0.iter();
        let mut other_path = other.0.iter();
        loop {
            match (self_path.next(), other_path.next()) {
                (Some(self_node), Some(other_node)) => match self_node.cmp(other_node) {
                    Ordering::Equal => continue,
                    ord => return ord,
                },
                (None, Some(_)) => return Ordering::Greater,
                (Some(_), None) => return Ordering::Less,
                (None, None) => return Ordering::Equal,
            }
        }
    }
}

impl<T> From<(BigRational, T)> for Identifier<T> {
    fn from((rational, value): (BigRational, T)) -> Self {
        Self(vec![(rational, value)])
    }
}

impl<T: Clone + Eq> Identifier<T> {
    /// Get a reference to the value this entry represents.
    pub fn value(&self) -> &T {
        self.0.last().map(|(_, elem)| elem).unwrap() // TODO: remove this unwrap
    }

    /// Get the value this entry represents, consuming the entry.
    pub fn into_value(mut self) -> T {
        self.0.pop().map(|(_, elem)| elem).unwrap() // TODO: remove this unwrap
    }

    /// Construct an entry between low and high holding the given element.
    pub fn between(low: Option<&Self>, high: Option<&Self>, marker: T) -> Self {
        match (low, high) {
            (Some(low), Some(high)) => {
                if low > high {
                    return Self::between(Some(high), Some(low), marker);
                } else if low == high {
                    return high.clone();
                }
                // Walk both paths until we reach a fork, constructing the path between these
                // two entries as we go.

                let mut path: Vec<(BigRational, T)> = vec![];
                let mut low_path: Box<dyn std::iter::Iterator<Item = &(BigRational, T)>> =
                    Box::new(low.0.iter());
                let mut high_path: Box<dyn std::iter::Iterator<Item = &(BigRational, T)>> =
                    Box::new(high.0.iter());
                loop {
                    match (low_path.next(), high_path.next()) {
                        (Some((l_ratio, l_marker)), Some((h_ratio, h_marker))) => {
                            match l_ratio.cmp(h_ratio) {
                                Ordering::Equal => {
                                    if &marker > l_marker && &marker < h_marker {
                                        path.push((h_ratio.clone(), marker));
                                        break;
                                    } else if l_marker == h_marker {
                                        path.push((l_ratio.clone(), l_marker.clone()));
                                    } else {
                                        // Otherwise, the two paths diverge.
                                        // Choose one path and clear out the other.
                                        //
                                        // TODO: randomize the choice here instead of always
                                        // choosing the  lower path
                                        path.push((l_ratio.clone(), l_marker.clone()));
                                        high_path = Box::new(std::iter::empty());
                                    }
                                }
                                _ => {
                                    path.push((
                                        rational_between(Some(l_ratio), Some(h_ratio)),
                                        marker,
                                    ));
                                    break;
                                }
                            }
                        }
                        (low_node, high_node) => {
                            path.push((
                                rational_between(low_node.map(|n| &n.0), high_node.map(|n| &n.0)),
                                marker,
                            ));
                            break;
                        }
                    }
                }
                Self(path)
            }

            (low, high) => Self(vec![(
                rational_between(
                    low.and_then(|low_entry| low_entry.0.first().map(|(r, _)| r)),
                    high.and_then(|high_entry| high_entry.0.first().map(|(r, _)| r)),
                ),
                marker,
            )]),
        }
    }
}

impl<T: fmt::Display> fmt::Display for Identifier<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ID[")?;
        let mut iter = self.0.iter();
        if let Some((r, e)) = iter.next() {
            write!(f, "{}:{}", r, e)?;
        }
        for (r, e) in iter {
            write!(f, ", {}:{}", r, e)?;
        }
        write!(f, "]")
    }
}

impl<T: Arbitrary> Arbitrary for Identifier<T> {
    fn arbitrary<G: Gen>(g: &mut G) -> Self {
        let mut path = vec![];
        for _ in 0..(u8::arbitrary(g) % 7) {
            let ordering_index_material: Vec<(i64, i64)> = Arbitrary::arbitrary(g);
            let ordering_index = ordering_index_material
                .into_iter()
                .filter(|(_, d)| d != &0)
                .take(3)
                .map(|(n, d)| BigRational::new(n.into(), d.into()))
                .sum();
            path.push((ordering_index, T::arbitrary(g)));
        }
        Self(path)
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        let mut path = self.0.clone();
        if let Some(_) = path.pop() {
            Box::new(std::iter::once(Self(path)))
        } else {
            Box::new(std::iter::empty())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use quickcheck::TestResult;
    use quickcheck_macros::quickcheck;

    #[test]
    fn test_adding_zero_node_makes_identifier_smaller() {
        let id_a = Identifier(vec![
            (BigRational::new(0.into(), 1.into()), 0),
            (BigRational::new(0.into(), 1.into()), 0),
        ]);
        let id_b = Identifier(vec![(BigRational::new(0.into(), 1.into()), 0)]);
        assert!(id_a < id_b);
    }

    #[test]
    fn test_id_is_dense_qc1() {
        let id_a = Identifier(vec![
            (BigRational::new(0i64.into(), 1i64.into()), 0),
            (BigRational::new(0i64.into(), 1.into()), 0),
        ]);
        let id_b = Identifier(vec![(BigRational::new(0i64.into(), 1i64.into()), 0)]);
        println!("id_a: {}", id_a);
        println!("id_b: {}", id_b);
        println!("id_a < id_b: {:?}", id_a < id_b);
        println!("id_b < id_a: {:?}", id_b < id_a);
        assert!(id_a < id_b);

        let id_mid = Identifier::between(Some(&id_a), Some(&id_b), 0);
        println!("minmax: {}, {}", id_a, id_b);
        assert!(id_a < id_mid, "{} < {}", id_a, id_mid);
        assert!(id_mid < id_b, "{} < {}", id_mid, id_b);
    }

    #[test]
    fn test_id_is_dense_qc2() {
        let id_a = Identifier(vec![
            (BigRational::new(0.into(), 1.into()), 1),
            (BigRational::new((-1).into(), 1.into()), 0),
        ]);
        let id_b = Identifier(vec![
            (BigRational::new(0.into(), 1.into()), 0),
            (BigRational::new(0.into(), 1.into()), 0),
        ]);
        let marker = 0;

        let (id_min, id_max) = if id_a < id_b {
            (id_a, id_b)
        } else {
            (id_b, id_a)
        };

        let id_mid = Identifier::between(Some(&id_min), Some(&id_max), marker);

        if id_min == id_max {
            assert_eq!(id_min, id_mid);
            assert_eq!(id_max, id_mid);
        } else {
            assert!(id_min < id_mid, "{} < {}", id_min, id_mid);
            assert!(id_mid < id_max, "{} < {}", id_mid, id_max);
        }
    }

    #[test]
    fn test_id_is_dense_qc3() {
        let (id_a, id_b, marker) = (
            Identifier(vec![(BigRational::new(0.into(), 1.into()), 96)]),
            Identifier(vec![(BigRational::new(0.into(), 1.into()), 69)]),
            0,
        );
        let (id_min, id_max) = if id_a < id_b {
            (id_a, id_b)
        } else {
            (id_b, id_a)
        };

        let id_mid = Identifier::between(Some(&id_min), Some(&id_max), marker);

        if id_min == id_max {
            assert_eq!(id_min, id_mid);
            assert_eq!(id_max, id_mid);
        } else {
            assert!(id_min < id_mid, "{} < {}", id_min, id_mid);
            assert!(id_mid < id_max, "{} < {}", id_mid, id_max);
        }
    }

    #[quickcheck]
    fn prop_id_is_dense(id_a: Identifier<u8>, id_b: Identifier<u8>, marker: u8) -> TestResult {
        let (id_min, id_max) = if id_a < id_b {
            (id_a, id_b)
        } else {
            (id_b, id_a)
        };

        let id_mid = Identifier::between(Some(&id_min), Some(&id_max), marker);

        if id_min == id_max {
            assert_eq!(id_min, id_mid);
            assert_eq!(id_max, id_mid);
        } else {
            assert!(id_min < id_mid, "{} < {}", id_min, id_mid);
            assert!(id_mid < id_max, "{} < {}", id_mid, id_max);
        }

        TestResult::passed()
    }

    #[quickcheck]
    fn prop_id_ord_is_transitive(id_a: Identifier<u8>, id_b: Identifier<u8>, id_c: Identifier<u8>) {
        let a_b_ord = id_a.cmp(&id_b);
        let a_c_ord = id_a.cmp(&id_c);
        let b_c_ord = id_b.cmp(&id_c);

        if a_b_ord == b_c_ord {
            assert_eq!(a_b_ord, a_c_ord);
        }
        if id_a == id_b {
            assert_eq!(a_c_ord, b_c_ord);
        }
    }

    #[test]
    fn test_id_is_dense_with_empty_identifier() {
        let id_min = Identifier(vec![(BigRational::from_integer((-1000).into()), 65)]);
        let id_max = Identifier(vec![]);
        let marker = 0;

        assert!(id_min < id_max);

        let id_mid = Identifier::between(Some(&id_min), Some(&id_max), marker);
        println!("mid: {}", id_mid);
        assert!(id_min < id_mid);
        assert!(id_mid < id_max);
    }
}
