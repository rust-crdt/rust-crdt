use std::cmp::Ordering;
use std::collections::HashMap;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::{self, Debug, Display};
use std::hash::Hash;
use std::mem;

use num::Num;
use serde::{Deserialize, Serialize};

use crate::ctx::{AddCtx, ReadCtx, RmCtx};
use crate::{CmRDT, CvRDT, Dot, ResetRemove, VClock};

/// Val Trait alias to reduce redundancy in type decl.
pub trait Val<A: Ord, C = u64>: Clone + Default + ResetRemove<A, C> + CmRDT {}

impl<A, T, C> Val<A, C> for T
where
    A: Ord,
    T: Clone + Default + ResetRemove<A, C> + CmRDT,
{
}

/// Map CRDT - Supports Composition of CRDT's with reset-remove semantics.
///
/// Reset-remove means that if one replica removes an entry while another
/// actor concurrently edits that entry, once we sync these two maps, we
/// will see that the entry is still in the map but all edits seen by the
/// removing actor will be gone.
///
/// See examples/reset_remove.rs for an example of reset-remove semantics
/// in action.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Map<K: Ord, V: Val<A, C>, A: Ord + Hash, C: Hash + Eq = u64> {
    // This clock stores the current version of the Map, it should
    // be greator or equal to all Entry.clock's in the Map.
    clock: VClock<A, C>,
    entries: BTreeMap<K, Entry<V, A, C>>,
    deferred: HashMap<VClock<A, C>, BTreeSet<K>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
struct Entry<V: Val<A, C>, A: Ord, C = u64> {
    // The entry clock tells us which actors edited this entry.
    clock: VClock<A, C>,

    // The nested CRDT
    val: V,
}

/// Operations which can be applied to the Map CRDT
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Op<K: Ord, V: Val<A, C>, A: Ord, C = u64> {
    /// Remove a key from the map
    Rm {
        /// The clock under which we will perform this remove
        clock: VClock<A, C>,
        /// Key to remove
        keyset: BTreeSet<K>,
    },
    /// Update an entry in the map
    Up {
        /// Actors version at the time of the update
        dot: Dot<A, C>,
        /// Key of the value to update
        key: K,
        /// The operation to apply on the value under `key`
        op: V::Op,
    },
}

impl<V: Val<A, C>, A: Ord, C> Default for Entry<V, A, C> {
    fn default() -> Self {
        Self {
            clock: VClock::default(),
            val: V::default(),
        }
    }
}

impl<K: Ord, V: Val<A, C>, A: Ord + Hash, C: Hash + Eq> Default for Map<K, V, A, C> {
    fn default() -> Self {
        Self {
            clock: Default::default(),
            entries: Default::default(),
            deferred: Default::default(),
        }
    }
}

impl<K: Ord, V: Val<A, C>, A: Ord + Hash, C: Ord + Clone + Hash + Eq + Num> ResetRemove<A, C>
    for Map<K, V, A, C>
{
    fn reset_remove(&mut self, clock: &VClock<A, C>) {
        self.entries = mem::take(&mut self.entries)
            .into_iter()
            .filter_map(|(key, mut entry)| {
                entry.clock.reset_remove(&clock);
                entry.val.reset_remove(&clock);
                if entry.clock.is_empty() {
                    None // remove this entry since its been forgotten
                } else {
                    Some((key, entry))
                }
            })
            .collect();

        self.deferred = mem::take(&mut self.deferred)
            .into_iter()
            .filter_map(|(mut rm_clock, key)| {
                rm_clock.reset_remove(&clock);
                if rm_clock.is_empty() {
                    None // this deferred remove has been forgotten
                } else {
                    Some((rm_clock, key))
                }
            })
            .collect();

        self.clock.reset_remove(&clock);
    }
}

/// The various validation errors that may occur when using a Map CRDT.
#[derive(Debug, PartialEq, Eq)]
pub enum CmRDTValidation<V: CmRDT, A, C = u64> {
    /// We are missing dots specified in the DotRange
    SourceOrder(crate::DotRange<A, C>),

    /// There is a validation error in the nested CRDT.
    Value(V::Validation),
}

impl<V: CmRDT + Debug, A: Debug, C: Debug> Display for CmRDTValidation<V, A, C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Debug::fmt(&self, f)
    }
}

impl<V: CmRDT + Debug, A: Debug, C: Debug> std::error::Error for CmRDTValidation<V, A, C> {}

/// The various validation errors that may occur when using a Map CRDT.
#[derive(Debug, PartialEq, Eq)]
pub enum CvRDTValidation<K, V: CvRDT, A, C = u64> {
    /// We've detected that two different members were inserted with the same dot.
    /// This can break associativity.
    DoubleSpentDot {
        /// The dot that was double spent
        dot: Dot<A, C>,
        /// Our member inserted with this dot
        our_key: K,
        /// Their member inserted with this dot
        their_key: K,
    },

    /// There is a validation error in the nested CRDT.
    Value(V::Validation),
}

impl<K: Debug, V: CvRDT + Debug, A: Debug, C: Debug> Display for CvRDTValidation<K, V, A, C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Debug::fmt(&self, f)
    }
}

impl<K: Debug, V: CvRDT + Debug, A: Debug, C: Debug> std::error::Error
    for CvRDTValidation<K, V, A, C>
{
}

impl<
        K: Ord,
        V: Val<A, C> + Debug,
        A: Ord + Hash + Clone + Debug,
        C: Ord + Clone + Debug + Display + Hash + Eq + Num,
    > CmRDT for Map<K, V, A, C>
{
    type Op = Op<K, V, A, C>;
    type Validation = CmRDTValidation<V, A, C>;

    fn validate_op(&self, op: &Self::Op) -> Result<(), Self::Validation> {
        match op {
            Op::Rm { .. } => Ok(()),
            Op::Up { dot, key, op } => {
                self.clock
                    .validate_op(&dot)
                    .map_err(CmRDTValidation::SourceOrder)?;
                let entry = self.entries.get(&key).cloned().unwrap_or_default();
                entry
                    .clock
                    .validate_op(&dot)
                    .map_err(CmRDTValidation::SourceOrder)?;
                entry.val.validate_op(&op).map_err(CmRDTValidation::Value)
            }
        }
    }

    fn apply(&mut self, op: Self::Op) {
        match op {
            Op::Rm { clock, keyset } => self.apply_keyset_rm(keyset, clock),
            Op::Up { dot, key, op } => {
                if self.clock.get(&dot.actor) >= dot.counter {
                    // we've seen this op already
                    return;
                }

                let entry = self.entries.entry(key).or_default();

                entry.clock.apply(dot.clone());
                entry.val.apply(op);

                self.clock.apply(dot);
                self.apply_deferred();
            }
        }
    }
}

impl<
        K: Ord + Clone + Debug,
        V: Val<A, C> + CvRDT + Debug,
        A: Ord + Hash + Clone + Debug,
        C: Ord + Clone + Hash + Eq + Debug + Display + Num,
    > CvRDT for Map<K, V, A, C>
{
    type Validation = CvRDTValidation<K, V, A, C>;

    fn validate_merge(&self, other: &Self) -> Result<(), Self::Validation> {
        for (key, entry) in self.entries.iter() {
            for (other_key, other_entry) in other.entries.iter() {
                for Dot { actor, counter } in entry.clock.iter() {
                    if other_key != key && other_entry.clock.get(&actor) == counter {
                        return Err(CvRDTValidation::DoubleSpentDot {
                            dot: Dot::new(actor.clone(), counter),
                            our_key: key.clone(),
                            their_key: other_key.clone(),
                        });
                    }
                }

                if key == other_key && entry.clock.concurrent(&other_entry.clock) {
                    entry
                        .val
                        .validate_merge(&other_entry.val)
                        .map_err(CvRDTValidation::Value)?;
                }
            }
        }

        Ok(())
    }

    fn merge(&mut self, other: Self) {
        self.entries = mem::take(&mut self.entries)
            .into_iter()
            .filter_map(|(key, mut entry)| {
                if !other.entries.contains_key(&key) {
                    // other doesn't contain this entry because it:
                    //  1. has seen it and dropped it
                    //  2. hasn't seen it
                    if other.clock >= entry.clock {
                        // other has seen this entry and dropped it
                        None
                    } else {
                        // the other map has not seen this version of this
                        // entry, so add it. But first, we have to remove any
                        // information that may have been known at some point
                        // by the other map about this key and was removed.
                        entry.clock.reset_remove(&other.clock);
                        let mut removed_information = other.clock.clone();
                        removed_information.reset_remove(&entry.clock);
                        entry.val.reset_remove(&removed_information);
                        Some((key, entry))
                    }
                } else {
                    Some((key, entry))
                }
            })
            .collect();

        for (key, mut entry) in other.entries {
            if let Some(our_entry) = self.entries.get_mut(&key) {
                // SUBTLE: this entry is present in both maps, BUT that doesn't mean we
                // shouldn't drop it!
                // Perfectly possible that an item in both sets should be dropped
                let mut common = VClock::intersection(&entry.clock, &our_entry.clock);
                common.merge(entry.clock.clone_without(&self.clock));
                common.merge(our_entry.clock.clone_without(&other.clock));
                if common.is_empty() {
                    // both maps had seen each others entry and removed them
                    self.entries.remove(&key).unwrap();
                } else {
                    // we should not drop, as there is information still tracked in
                    // the common clock.
                    our_entry.val.merge(entry.val);

                    let mut information_that_was_deleted = entry.clock.clone();
                    information_that_was_deleted.merge(our_entry.clock.clone());
                    information_that_was_deleted.reset_remove(&common);
                    our_entry.val.reset_remove(&information_that_was_deleted);
                    our_entry.clock = common;
                }
            } else {
                // we don't have this entry, is it because we:
                //  1. have seen it and dropped it
                //  2. have not seen it
                if self.clock >= entry.clock {
                    // We've seen this entry and dropped it, we won't add it back
                } else {
                    // We have not seen this version of this entry, so we add it.
                    // but first, we have to remove the information on this entry
                    // that we have seen and deleted
                    entry.clock.reset_remove(&self.clock);

                    let mut information_we_deleted = self.clock.clone();
                    information_we_deleted.reset_remove(&entry.clock);
                    entry.val.reset_remove(&information_we_deleted);
                    self.entries.insert(key, entry);
                }
            }
        }

        // merge deferred removals
        for (rm_clock, keys) in other.deferred {
            self.apply_keyset_rm(keys, rm_clock);
        }

        self.clock.merge(other.clock);

        self.apply_deferred();
    }
}

impl<K: Ord, V: Val<A, C>, A: Ord + Hash + Clone, C: Ord + Clone + Hash + Eq + Num>
    Map<K, V, A, C>
{
    /// Constructs an empty Map
    pub fn new() -> Self {
        Default::default()
    }

    /// Returns true if the map has no entries, false otherwise
    pub fn is_empty(&self) -> ReadCtx<bool, A, C> {
        ReadCtx {
            add_clock: self.clock.clone(),
            rm_clock: self.clock.clone(),
            val: self.entries.is_empty(),
        }
    }

    /// Returns the number of entries in the Map
    pub fn len(&self) -> ReadCtx<usize, A, C> {
        ReadCtx {
            add_clock: self.clock.clone(),
            rm_clock: self.clock.clone(),
            val: self.entries.len(),
        }
    }

    /// Retrieve value stored under a key
    pub fn get(&self, key: &K) -> ReadCtx<Option<V>, A, C> {
        let add_clock = self.clock.clone();
        let entry_opt = self.entries.get(&key);
        ReadCtx {
            add_clock,
            rm_clock: entry_opt
                .map(|map_entry| map_entry.clock.clone())
                .unwrap_or_default(),
            val: entry_opt.map(|map_entry| map_entry.val.clone()),
        }
    }

    /// Update a value under some key.
    ///
    /// If the key is not present in the map, the updater will be given the
    /// result of `V::default()`. The `default` value is used to ensure
    /// eventual consistency since our `Map`'s values are CRDTs themselves.
    ///
    /// The `impl Into<K>` bound provides a nice way of providing an input key that
    /// can easily convert to the `Map`'s key. For example, we can call this function
    /// with `"hello": &str` and it can be converted to `String`.
    pub fn update<F>(&self, key: impl Into<K>, ctx: AddCtx<A, C>, f: F) -> Op<K, V, A, C>
    where
        F: FnOnce(&V, AddCtx<A, C>) -> V::Op,
    {
        let key = key.into();
        let dot = ctx.dot.clone();
        let op = match self.entries.get(&key).map(|e| &e.val) {
            Some(data) => f(&data, ctx),
            None => f(&V::default(), ctx),
        };

        Op::Up { dot, key, op }
    }

    /// Remove an entry from the Map
    ///
    /// The `impl Into<K>` bound provides a nice way of providing an input key that
    /// can easily convert to the `Map`'s key. For example, we can call this function
    /// with `"hello": &str` and it can be converted to `String`.
    pub fn rm(&self, key: impl Into<K>, ctx: RmCtx<A, C>) -> Op<K, V, A, C> {
        let mut keyset = BTreeSet::new();
        keyset.insert(key.into());
        Op::Rm {
            clock: ctx.clock,
            keyset,
        }
    }

    /// Retrieve the current read context
    pub fn read_ctx(&self) -> ReadCtx<(), A, C> {
        ReadCtx {
            add_clock: self.clock.clone(),
            rm_clock: self.clock.clone(),
            val: (),
        }
    }

    /// apply the pending deferred removes
    fn apply_deferred(&mut self) {
        let deferred = mem::take(&mut self.deferred);
        for (clock, keys) in deferred {
            self.apply_keyset_rm(keys, clock);
        }
    }

    /// Apply a set of key removals given a clock.
    fn apply_keyset_rm(&mut self, mut keyset: BTreeSet<K>, clock: VClock<A, C>) {
        for key in keyset.iter() {
            if let Some(entry) = self.entries.get_mut(&key) {
                entry.clock.reset_remove(&clock);
                if entry.clock.is_empty() {
                    // The entry clock says we have no info on this entry.
                    // So remove the entry
                    self.entries.remove(&key);
                } else {
                    // The entry clock is not empty so this means we still
                    // have some information on this entry, keep it.
                    entry.val.reset_remove(&clock);
                }
            }
        }

        // now we need to decide wether we should be keeping this
        // remove Op around to remove entries we haven't seen yet.
        match self.clock.partial_cmp(&clock) {
            None | Some(Ordering::Less) => {
                // this remove clock has information we don't have,
                // we need to log this in our deferred remove map, so
                // that we can delete keys that we haven't seen yet but
                // have been seen by this clock
                let deferred_set = self.deferred.entry(clock).or_default();
                deferred_set.append(&mut keyset);
            }
            _ => { /* we've seen all keys this clock has seen */ }
        }
    }

    /// Gets an iterator over the keys of the `Map`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use crdts::Map;
    /// use crdts::MVReg;
    /// use crdts::CmRDT;
    ///
    /// type Actor = &'static str;
    /// type Key = &'static str;
    ///
    /// let actor = "actor";
    ///
    /// let mut map: Map<i32, MVReg<Key, Actor>, Actor> = Map::new();
    ///
    /// let add_ctx = map.read_ctx().derive_add_ctx(actor);
    /// map.apply(map.update(100, add_ctx, |v, a| v.write("foo", a)));
    ///
    /// let add_ctx = map.read_ctx().derive_add_ctx(actor);
    /// map.apply(map.update(50, add_ctx, |v, a| v.write("bar", a)));
    ///
    /// let add_ctx = map.read_ctx().derive_add_ctx(actor);
    /// map.apply(map.update(200, add_ctx, |v, a| v.write("baz", a)));
    ///
    ///
    /// let mut keys: Vec<_> = map.keys().map(|key_ctx| *key_ctx.val).collect();
    ///
    /// keys.sort();
    ///
    /// assert_eq!(keys, &[50, 100, 200]);
    /// ```
    pub fn keys(&self) -> impl Iterator<Item = ReadCtx<&K, A, C>> {
        self.entries.iter().map(move |(k, v)| ReadCtx {
            add_clock: self.clock.clone(),
            rm_clock: v.clock.clone(),
            val: k,
        })
    }

    /// Gets an iterator over the values of the `Map`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use crdts::Map;
    /// use crdts::MVReg;
    /// use crdts::CmRDT;
    ///
    /// type Actor = &'static str;
    /// type Key = &'static str;
    ///
    /// let actor = "actor";
    ///
    /// let mut map: Map<i32, MVReg<Key, Actor>, Actor> = Map::new();
    ///
    /// let add_ctx = map.read_ctx().derive_add_ctx(actor);
    /// map.apply(map.update(100, add_ctx, |v, a| v.write("foo", a)));
    ///
    /// let add_ctx = map.read_ctx().derive_add_ctx(actor);
    /// map.apply(map.update(50, add_ctx, |v, a| v.write("bar", a)));
    ///
    /// let add_ctx = map.read_ctx().derive_add_ctx(actor);
    /// map.apply(map.update(200, add_ctx, |v, a| v.write("baz", a)));
    ///
    ///
    /// let mut values: Vec<_> = map
    ///     .values()
    ///     .map(|val_ctx| val_ctx.val.read().val[0])
    ///     .collect();
    ///
    /// values.sort();
    ///
    /// assert_eq!(values, &["bar", "baz", "foo"]);
    /// ```
    pub fn values(&self) -> impl Iterator<Item = ReadCtx<&V, A, C>> {
        self.entries.values().map(move |v| ReadCtx {
            add_clock: self.clock.clone(),
            rm_clock: v.clock.clone(),
            val: &v.val,
        })
    }

    /// Gets an iterator over the entries of the `Map`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use crdts::Map;
    /// use crdts::MVReg;
    /// use crdts::CmRDT;
    ///
    /// type Actor = &'static str;
    /// type Key = &'static str;
    ///
    /// let actor = "actor";
    ///
    /// let mut map: Map<i32, MVReg<Key, Actor>, Actor> = Map::new();
    ///
    /// let add_ctx = map.read_ctx().derive_add_ctx(actor);
    /// map.apply(map.update(100, add_ctx, |v, a| v.write("foo", a)));
    ///
    /// let add_ctx = map.read_ctx().derive_add_ctx(actor);
    /// map.apply(map.update(50, add_ctx, |v, a| v.write("bar", a)));
    ///
    /// let add_ctx = map.read_ctx().derive_add_ctx(actor);
    /// map.apply(map.update(200, add_ctx, |v, a| v.write("baz", a)));
    ///
    ///
    /// let mut items: Vec<_> = map
    ///     .iter()
    ///     .map(|item_ctx| (*item_ctx.val.0, item_ctx.val.1.read().val[0]))
    ///     .collect();
    ///
    /// items.sort();
    ///
    /// assert_eq!(items, &[(50, "bar"), (100, "foo"), (200, "baz")]);
    /// ```
    pub fn iter(&self) -> impl Iterator<Item = ReadCtx<(&K, &V), A, C>> {
        self.entries.iter().map(move |(k, v)| ReadCtx {
            add_clock: self.clock.clone(),
            rm_clock: v.clock.clone(),
            val: (k, &v.val),
        })
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::mvreg::{self, MVReg};
    use crate::orswot::Orswot;

    type TestActor = u8;
    type TestKey = u8;
    type TestVal = MVReg<u8, TestActor>;
    type TestMap = Map<TestKey, Map<TestKey, TestVal, TestActor>, TestActor>;

    #[test]
    fn test_get() {
        let mut m: TestMap = Map::new();

        assert_eq!(m.get(&0).val, None);

        m.clock.apply(m.clock.inc(1));

        m.entries.insert(
            0,
            Entry {
                clock: m.clock.clone(),
                val: Map::default(),
            },
        );

        assert_eq!(m.get(&0).val, Some(Map::new()));
    }

    #[test]
    fn test_op_exchange_converges_quickcheck1() {
        let op_actor1 = Op::Up {
            dot: Dot::new(0, 3),
            key: 9,
            op: Op::Up {
                dot: Dot::new(0, 3),
                key: 0,
                op: mvreg::Op::Put {
                    clock: Dot::new(0, 3).into(),
                    val: 0,
                },
            },
        };
        let op_1_actor2 = Op::Up {
            dot: Dot::new(1, 1),
            key: 9,
            op: Op::Rm {
                clock: Dot::new(1, 1).into(),
                keyset: vec![0].into_iter().collect(),
            },
        };
        let op_2_actor2 = Op::Rm {
            clock: Dot::new(1, 2).into(),
            keyset: vec![9].into_iter().collect(),
        };

        let mut m1: TestMap = Map::new();
        let mut m2: TestMap = Map::new();

        m1.apply(op_actor1.clone());
        assert_eq!(m1.clock, Dot::new(0, 3).into());
        assert_eq!(m1.entries[&9].clock, Dot::new(0, 3).into());
        assert_eq!(m1.entries[&9].val.deferred.len(), 0);

        m2.apply(op_1_actor2.clone());
        m2.apply(op_2_actor2.clone());
        assert_eq!(m2.clock, Dot::new(1, 1).into());
        assert_eq!(m2.entries.get(&9), None);
        assert_eq!(
            m2.deferred.get(&Dot::new(1, 2).into()),
            Some(&vec![9].into_iter().collect())
        );

        // m1 <- m2
        m1.apply(op_1_actor2);
        m1.apply(op_2_actor2);

        // m2 <- m1
        m2.apply(op_actor1);

        // m1 <- m2 == m2 <- m1
        assert_eq!(m1, m2);
    }

    #[test]
    fn merge_error() {
        let mut m1: Map<u8, Orswot<u8, u8>, u8> = Map {
            clock: VClock::from(Dot::new(75, 1)),
            entries: BTreeMap::new(),
            deferred: HashMap::new(),
        };

        let mut m2: Map<u8, Orswot<u8, u8>, u8> = Map {
            clock: vec![Dot::new(75, 1), Dot::new(93, 1)].into_iter().collect(),
            entries: vec![(
                101,
                Entry {
                    clock: vec![Dot::new(75, 1), Dot::new(93, 1)].into_iter().collect(),
                    val: Orswot {
                        clock: vec![Dot::new(75, 1), Dot::new(93, 1)].into_iter().collect(),
                        entries: vec![
                            (1, VClock::from(Dot::new(75, 1))),
                            (2, VClock::from(Dot::new(93, 1))),
                        ]
                        .into_iter()
                        .collect(),
                        deferred: HashMap::new(),
                    },
                },
            )]
            .into_iter()
            .collect(),
            deferred: HashMap::new(),
        };

        m1.merge(m2.clone());

        assert_eq!(
            m1,
            Map {
                clock: vec![Dot::new(75, 1), Dot::new(93, 1)].into_iter().collect(),
                entries: vec![(
                    101,
                    Entry {
                        clock: Dot::new(93, 1).into(),
                        val: Orswot {
                            clock: vec![Dot::new(93, 1)].into_iter().collect(),
                            entries: vec![(2, VClock::from(Dot::new(93, 1)))]
                                .into_iter()
                                .collect(),
                            deferred: HashMap::new()
                        }
                    }
                )]
                .into_iter()
                .collect(),
                deferred: HashMap::new()
            }
        );

        m2.merge(m1.clone());

        assert_eq!(m1, m2);
    }
}
