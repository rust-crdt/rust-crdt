// Causality barrier
// For each known peer, keeps track of the latest clock seen
// and a set of messages that are from the future
// and outputs the full-in-order sequence of messages
//
//
#![allow(missing_docs)]

use std::cmp::Ordering;
use std::collections::*;
use std::hash::Hash;

use serde::{self, Deserialize, Serialize};

use crate::Dot;

/// Version Vector with Exceptions
#[derive(Debug, Serialize, Deserialize)]
struct CausalityBarrier<A: Hash + Eq, T: CausalOp<A>> {
    peers: HashMap<A, VectorEntry>,
    // TODO: this dot here keying the T comes from `T::happens_after()`
    //       Why do we need to store this,
    buffer: HashMap<Dot<A>, T>,
}

type LogTime = u64;

#[derive(Serialize, Deserialize, Clone, Debug, Default)]
struct VectorEntry {
    // The version of the next message we'd like to see
    next_version: LogTime,
    exceptions: HashSet<LogTime>,
}

impl VectorEntry {
    fn new() -> Self {
        VectorEntry::default()
    }

    fn increment(&mut self, clk: LogTime) {
        match clk.cmp(&self.next_version) {
            // We've resolved an exception
            Ordering::Less => {
                self.exceptions.remove(&clk);
            }
            // This is what we expected to see as the next op
            Ordering::Equal => self.next_version += 1,
            // We've just found an exception
            Ordering::Greater => (self.next_version + 1..clk).for_each(|i| {
                self.exceptions.insert(i);
            }),
        };
    }

    fn is_ready(&self, clk: LogTime) -> bool {
        clk < self.next_version && self.no_exceptions(clk)
    }

    /// Calculate the difference between a remote VectorEntry and ours.
    /// Specifically, we want the set of operations we've seen that the remote hasn't
    fn diff_from(&self, other: &Self) -> HashSet<LogTime> {
        // 1. Find (new) operations that we've seen locally that the remote hasn't
        let local_ops =
            (other.next_version..self.next_version).filter(|ix: &LogTime| self.no_exceptions(*ix));

        // 2. Find exceptions that we've seen.
        let mut local_exceptions = other.exceptions.difference(&self.exceptions).cloned();

        local_ops.chain(&mut local_exceptions).collect()
    }

    fn no_exceptions(&self, clk: LogTime) -> bool {
        !self.exceptions.contains(&clk)
    }
}

trait CausalOp<A> {
    /// TODO: result should be a VClock<A> since an op could be dependant on a few different msgs
    /// If the result is Some(dot) then this operation cannot occur until the operation that
    /// occured at dot has.
    fn happens_after(&self) -> Option<Dot<A>>;

    /// The time that the current operation occured at
    fn dot(&self) -> Dot<A>;
}

impl<A: Hash + Eq, T: CausalOp<A>> Default for CausalityBarrier<A, T> {
    fn default() -> Self {
        CausalityBarrier {
            peers: HashMap::new(),
            buffer: HashMap::new(),
        }
    }
}

impl<A: Hash + Clone + Eq, T: CausalOp<A>> CausalityBarrier<A, T> {
    fn new() -> Self {
        CausalityBarrier::default()
    }

    fn ingest(&mut self, op: T) -> Option<T> {
        let v = self.peers.entry(op.dot().actor).or_default();
        // Have we already seen this op?
        if v.is_ready(op.dot().counter) {
            return None;
        }

        v.increment(op.dot().counter);

        // Ok so it's an exception but maybe we can still integrate it if it's not constrained
        // by a happens-before relation.
        // For example: we can always insert into most CRDTs but we can only delete if the
        // corresponding insert happened before!
        match op.happens_after() {
            // Dang! we have a happens after relation!
            Some(dot) => {
                // Let's buffer this operation then.
                if !self.saw_site_dot(&dot) {
                    self.buffer.insert(dot, op);
                    // and do nothing
                    None
                } else {
                    Some(op)
                }
            }
            None => {
                // Ok so we're not causally constrained, but maybe we already saw an associated
                // causal operation? If so let's just delete the pair
                match self.buffer.remove(&op.dot()) {
                    Some(_) => None, // we are dropping the dependent op! that can't be right
                    None => Some(op),
                }
            }
        }
    }

    fn saw_site_dot(&self, dot: &Dot<A>) -> bool {
        // TODO: shouldn't need to deconstruct a dot like this
        match self.peers.get(&dot.actor) {
            Some(ent) => ent.is_ready(dot.counter),
            None => false,
        }
    }

    fn expel(&mut self, op: T) -> T {
        let v = self.peers.entry(op.dot().actor).or_default();
        v.increment(op.dot().counter);
        op
    }

    fn diff_from(&self, other: &HashMap<A, VectorEntry>) -> HashMap<A, HashSet<LogTime>> {
        let mut ret = HashMap::new();
        for (site_id, entry) in self.peers.iter() {
            let e_diff = match other.get(site_id) {
                Some(remote_entry) => entry.diff_from(remote_entry),
                None => (0..entry.next_version).collect(),
            };
            ret.insert(site_id.clone(), e_diff);
        }
        ret
    }

    fn vvwe(&self) -> HashMap<A, VectorEntry> {
        self.peers.clone()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    type SiteId = u32;

    #[derive(PartialEq, Debug, Hash, Clone)]
    enum Op {
        Insert(u64),
        Delete(SiteId, LogTime),
    }

    #[derive(PartialEq, Debug, Hash, Clone)]
    struct CausalMessage {
        time: LogTime,
        local_id: SiteId,
        op: Op,
    }

    impl CausalOp<SiteId> for CausalMessage {
        fn happens_after(&self) -> Option<Dot<SiteId>> {
            match self.op {
                Op::Insert(_) => None,
                Op::Delete(s, l) => Some(Dot::new(s, l)),
            }
        }

        fn dot(&self) -> Dot<SiteId> {
            Dot::new(self.local_id, self.time)
        }
    }

    #[test]
    fn delete_before_insert() {
        let mut barrier = CausalityBarrier::new();

        let ins = CausalMessage {
            time: 0,
            local_id: 1,
            op: Op::Insert(0),
        };

        let del = CausalMessage {
            time: 1,
            local_id: 1,
            op: Op::Delete(1, 0),
        };

        assert_eq!(barrier.ingest(ins.clone()), Some(ins));
        assert_eq!(barrier.ingest(del.clone()), Some(del));
    }

    #[test]
    fn out_of_order() {
        let mut barrier = CausalityBarrier::new();

        let ins = CausalMessage {
            time: 0,
            local_id: 1,
            op: Op::Insert(0),
        };

        let del = CausalMessage {
            time: 1,
            local_id: 1,
            op: Op::Delete(1, 0),
        };

        assert_eq!(barrier.ingest(del), None);
        assert_eq!(barrier.ingest(ins), None);
    }

    #[test]
    fn insert() {
        let mut barrier = CausalityBarrier::new();

        let ins = CausalMessage {
            time: 1,
            local_id: 1,
            op: Op::Insert(0),
        };
        assert_eq!(barrier.ingest(ins.clone()), Some(ins));
    }

    #[test]
    fn insert_then_delete() {
        let mut barrier = CausalityBarrier::new();

        let ins = CausalMessage {
            time: 0,
            local_id: 1,
            op: Op::Insert(0),
        };
        let del = CausalMessage {
            time: 1,
            local_id: 1,
            op: Op::Delete(1, 1),
        };
        assert_eq!(barrier.ingest(ins.clone()), Some(ins));
        assert_eq!(barrier.ingest(del.clone()), Some(del));
    }

    #[test]
    fn delete_before_insert_multiple_sites() {
        let mut barrier = CausalityBarrier::new();

        let del = CausalMessage {
            time: 0,
            local_id: 2,
            op: Op::Delete(1, 5),
        };
        let ins = CausalMessage {
            time: 5,
            local_id: 1,
            op: Op::Insert(0),
        };
        assert_eq!(barrier.ingest(del), None);
        assert_eq!(barrier.ingest(ins), None);
    }

    #[test]
    fn entry_diff_new_entries() {
        let a = VectorEntry::new();
        let b = VectorEntry {
            next_version: 10,
            exceptions: HashSet::new(),
        };

        let c: HashSet<LogTime> = (0..10).into_iter().collect();
        assert_eq!(b.diff_from(&a), c);
    }

    #[test]
    fn entry_diff_found_exceptions() {
        let a = VectorEntry {
            next_version: 10,
            exceptions: [1, 2, 3, 4].iter().cloned().collect(),
        };
        let b = VectorEntry {
            next_version: 5,
            exceptions: HashSet::new(),
        };

        let c: HashSet<LogTime> = [1, 2, 3, 4].iter().cloned().collect();
        assert_eq!(b.diff_from(&a), c);
    }

    #[test]
    fn entry_diff_complex() {
        // a has seen 0, 5
        let a = VectorEntry {
            next_version: 6,
            exceptions: [1, 2, 3, 4].iter().cloned().collect(),
        };
        // b has seen 0, 1, 5,6,7,8
        let b = VectorEntry {
            next_version: 9,
            exceptions: [2, 3, 4].iter().cloned().collect(),
        };

        // c should be 1,6,7,8
        let c: HashSet<LogTime> = [1, 6, 7, 8].iter().cloned().collect();
        assert_eq!(b.diff_from(&a), c);
    }
}
