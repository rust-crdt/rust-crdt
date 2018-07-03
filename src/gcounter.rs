use super::*;

use std::cmp::Ordering;

/// `GCounter` is a grow-only witnessed counter.
///
/// # Examples
///
/// ```
/// use crdts::GCounter;
/// let (mut a, mut b) = (GCounter::new(), GCounter::new());
/// a.increment("A".to_string());
/// b.increment("B".to_string());
/// assert_eq!(a.value(), b.value());
/// assert!(a == b);
/// a.increment("A".to_string());
/// assert!(a > b);
/// ```
#[serde(bound(deserialize = ""))]
#[derive(Debug, Eq, Clone, Hash, Serialize, Deserialize)]
pub struct GCounter<A: Ord + Clone + Serialize + DeserializeOwned> {
    inner: VClock<A>,
}

impl<A: Ord + Clone + Serialize + DeserializeOwned> Ord for GCounter<A> {
    fn cmp(&self, other: &GCounter<A>) -> Ordering {
        let (c, oc) = (self.value(), other.value());
        c.cmp(&oc)
    }
}

impl<A: Ord + Clone + Serialize + DeserializeOwned> PartialOrd for GCounter<A> {
    fn partial_cmp(&self, other: &GCounter<A>) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<A: Ord + Clone + Serialize + DeserializeOwned> PartialEq for GCounter<A> {
    fn eq(&self, other: &GCounter<A>) -> bool {
        let (c, oc) = (self.value(), other.value());
        c == oc
    }
}

impl<A: Ord + Clone + Serialize + DeserializeOwned> GCounter<A> {
    /// Produces a new `GCounter`.
    pub fn new() -> GCounter<A> {
        GCounter { inner: VClock::new() }
    }

    /// Increments a particular actor's counter.
    pub fn increment(&mut self, actor: A) {
        self.inner.increment(actor);
    }

    /// Returns the current sum of this counter.
    pub fn value(&self) -> u64 {
        self.inner.dots.values().fold(0, |acc, count| acc + count)
    }

    /// Merge another gcounter into this one, without
    /// regard to dominance.
    ///
    /// # Examples
    ///
    /// ```
    /// use crdts::GCounter;
    /// let (mut a, mut b, mut c) = (GCounter::new(), GCounter::new(), GCounter::new());
    /// a.increment("A".to_string());
    /// b.increment("B".to_string());
    /// c.increment("A".to_string());
    /// c.increment("B".to_string());
    /// a.merge(b);
    /// assert_eq!(a, c);
    pub fn merge(&mut self, other: GCounter<A>) {
        self.inner.merge(&other.inner);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic() {
        let (mut a, mut b) = (GCounter::new(), GCounter::new());
        a.increment("A".to_string());
        b.increment("B".to_string());
        assert_eq!(a.value(), b.value());
        assert!(a == b);
        a.increment("A".to_string());
        assert!(a > b);
    }
}
