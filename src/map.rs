use serde::Serialize;
use serde::de::DeserializeOwned;

use error::Result;
use traits::ComposableCrdt;
use vclock::VClock;
use std::collections::BTreeMap;

/// The Map CRDT - Supports Composition of CRDT's.
///
/// Orswot based Map with reset-remove semantics.
///
/// Reset-remove here means that if one replica removes an entry while
/// concurrently another actor mutates that entry, on merge, we will see that
/// the key is still in the map but all changes seen by the removing replica
/// will disapear from the entry. To understand this more clearly see the
/// following example:
///
/// ``` rust
/// use crdts::{Map, Orswot, ComposableCrdt};
///
/// type Actor = u64;
/// type Friend = String;
/// let mut friend_map: Map<Friend, Orswot<Friend, Actor>, Actor> = Map::new();
///
/// let first_actor_id = 10837103590;
///
/// friend_map.update(
///     "alice".to_string(),
///     |mut friend_set| {
///         friend_set.add("bob".to_string(), first_actor_id);
///         Some(friend_set)
///     },
///     first_actor_id
/// );
///
/// let mut second_friend_map = friend_map.clone();
/// let second_actor_id = 8947212;
///
/// // now the two maps will start to diverge. first map will remove "alice"
/// // from the map while the second map will update the "alice" friend set to
/// // include "clyde".
///
/// friend_map.remove("alice".to_string(), first_actor_id);
/// second_friend_map.update(
///     "alice".to_string(),
///     |mut friend_set| {
///         friend_set.add("clyde".to_string(), second_actor_id);
///         Some(friend_set)
///     },
///     second_actor_id
/// );
///
/// // On merge, we should see that the "alice" key is in the map but the
/// // "alice" friend set only contains clyde. This, in essence, is the
/// // reset-remove semantics, all changes that the removing replica saw are
/// // gone, but changes not seen by the removing replica are kept.
///
/// friend_map.merge(&second_friend_map).unwrap();
///
/// let alice_friends = friend_map.get(&"alice".to_string());
///
/// match alice_friends {
///     Some(set) => assert_eq!(set.value(), vec!["clyde".to_string()]),
///     None => panic!()
/// }
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct Map<K, V, A> where
    K: Ord + Clone + Serialize + DeserializeOwned,
    V: Clone + Serialize + DeserializeOwned + ComposableCrdt<A>,
    A: Ord + Clone + Serialize + DeserializeOwned
{
    // This clock stores the current version of the Map, it should
    // be greator or equal to all MapEntry.clock's in the Map.
    clock: VClock<A>,
    entries: BTreeMap<K, MapEntry<V, A>>
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct MapEntry<V, A> where
    V: Clone + Serialize + DeserializeOwned + ComposableCrdt<A>,
    A: Ord + Clone + Serialize + DeserializeOwned
{
    // The entry clock tells us which actors have last changed this entry.
    // This clock will tell us what to do with this entry in the case of a merge
    // where only one map has this entry.
    //
    // e.g. say replica A has key `"user_32"` but replica B does not. We need to
    // decide whether replica B has processed a `remove("user_32")` operation
    // and replica A has not or replica A has processed an insert("key")
    // operation which has not been seen by replica B yet.
    //
    // This conflict can be resolved by comparing replica B's Map.clock to the
    // the "user_32" MapEntry clock in replica A.
    // If B's clock is >=  "user_32"'s clock, then we know that B has
    // seen this entry and removed it, otherwise B has not received the insert
    // operation so we keep the key.
    clock: VClock<A>,

    // This clock marks the most recent time that this entry did not exist.
    // It acts a lower clock bound for all mutations to the nested CRDT. Changes
    // which happened prior to this clock should be discarded.
    //
    // The birth clock is reset everytime an insert or a remove with a
    // concurrent update happens.
    birth_clock: VClock<A>,

    // The nested CRDT
    val: V
}

impl<K, V, A> ComposableCrdt<A> for Map<K, V, A> where
    K: Ord + Clone + Serialize + DeserializeOwned,
    V: Clone + Serialize + DeserializeOwned + ComposableCrdt<A>,
    A: Ord + Clone + Serialize + DeserializeOwned
{

    fn default_with_clock(clock: VClock<A>) -> Self {
        let mut default = Self::default();
        default.clock = clock;
        default
    }

    fn merge(&mut self, other: &Self) -> Result<()> {
        for (key, entry) in other.entries.iter() {
            // TODO(david) avoid this remove here with entries.get_mut?
            if let Some(mut existing) = self.entries.remove(&key) {
                existing.clock.merge(&entry.clock);
                existing.birth_clock.merge(&entry.birth_clock);
                existing.val.merge(&entry.val)?;

                // TODO(david) this extra merge is most likely not required
                //             but it keeps the merge code consistent, do some
                //             benchmarks to see how this impacts performance
                existing.val.merge(
                    &V::default_with_clock(existing.birth_clock.clone())
                )?;
                self.entries.insert(key.clone(), existing);
            } else {
                // we don't have this entry:
                //   is this because we removed it?
                if self.clock >= entry.clock {
                    // we removed this entry! don't add it back to our map
                    continue;
                }

                // this is either a new entry, or an entry we removed while the
                // other map has concurrently mutated it. (reset-remove)
                let mut new_entry = entry.clone();

                // We merge our map clock into the birth clock to mark that at
                // this time we knew that this entry did not exist in our set
                new_entry.birth_clock.merge(&self.clock);

                // This next merge will remove all changes that happened at or
                // before the updated birth_clock
                new_entry.val.merge(
                    &V::default_with_clock(new_entry.birth_clock.clone())
                )?;
                self.entries.insert(key.clone(), new_entry);
            }
        }

        // check for entries that we have but are missing in other
        let mut to_remove = Vec::new();
        for (key, mut entry) in self.entries.iter_mut() {
            if other.entries.get(&key).is_some() {
                // The entry exists, we've already dealt with it above
                continue;
            }
            if other.clock >= entry.clock {
                // other has seen this entry and removed it, we remove it
                to_remove.push(key.clone());
            } else if other.clock.concurrent(&entry.clock) {
                // other has removed this entry but we modified it concurrently
                // (reset-remove)
                entry.birth_clock.merge(&other.clock);
                entry.val.merge(
                    &V::default_with_clock(entry.birth_clock.clone())
                )?;
            } else {
                // our entry clock is ahead of the other's clock meaning we have
                // seen everything the other has seen. We have nothing to do.
            }
        }

        for key in to_remove.into_iter() {
            self.entries.remove(&key);
        }

        self.clock.merge(&other.clock);
        Ok(())
    }
}

impl<K, V, A> Default for Map<K, V, A> where
    K: Ord + Clone + Serialize + DeserializeOwned,
    V: Clone + Serialize + DeserializeOwned + ComposableCrdt<A>,
    A: Ord + Clone + Serialize + DeserializeOwned
{
    fn default() -> Self {
        Map::new()
    }
}

impl<K, V, A> Map<K, V, A> where
    K: Ord + Clone + Serialize + DeserializeOwned,
    V: Clone + Serialize + DeserializeOwned + ComposableCrdt<A>,
    A: Ord + Clone + Serialize + DeserializeOwned
{
    /// Constructs an empty Map
    pub fn new() -> Map<K, V, A> {
        Map {
            clock: VClock::new(),
            entries: BTreeMap::new()
         }
    }

    /// Returns the number of entries in the Map
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Get a reference to a value stored under a key
    pub fn get(&self, key: &K) -> Option<&V> {
        self.entries.get(&key)
            .map(|map_entry| &map_entry.val)
    }

    /// Insert a value under some key.
    /// Note:
    ///   insert's destroy causality! think of it as the equivalent of removing
    ///   and adding a new element.
    ///
    ///   If you want to update a crdt while preserving causal history, consider
    ///   using `Map::update()`.
    pub fn insert(&mut self, key: K, val: V, actor: A) {
        let birth_clock = self.clock.clone();

        let actor_version = self.clock.increment(actor.clone());
        let mut dot = VClock::new();
        // this witness should never fail because dot is brand new
        dot.witness(actor, actor_version).unwrap();

        self.entries.insert(key, MapEntry { clock: dot, birth_clock, val });
    }

    /// Update a value under some key, if the key is not present in the map,
    /// a V::default() entry is created and passed to the update function.
    ///
    /// The updater must return Some(val) to have the updated val stored back in
    /// the Map. If None is returned, this entry is removed from the Map.
    pub fn update<F>(&mut self, key: K, mut updater: F, actor: A) where
        F: FnMut(V) -> Option<V>
    {
        self.clock.increment(actor.clone());
        match self.entries.remove(&key) {
            Some(mut entry) =>  {
                if let Some(new_val) = updater(entry.val) {
                    entry.clock.increment(actor);
                    entry.val = new_val;
                    self.entries.insert(key, entry);
                } else {
                    // we've already removed the entry
                }
            },
            None => {
                if let Some(new_val) = updater(V::default()) {
                    // TAI: Map.clock.increment(actor) is happening twice here:
                    //      once at the beginning of this update and again in
                    //      insert. This shouldn't be a problem but it's worth
                    //      calling out
                    self.insert(key, new_val, actor);
                } else {
                    // entry is already not in the Map, nothing to do.
                }
            }
        }
    }


    /// Remove an entry from the Map
    pub fn remove(&mut self, key: K, actor: A) {
        self.clock.increment(actor.clone());

        if let Some(map_entry) = self.entries.remove(&key) {
            if !(self.clock >= map_entry.clock) {
                panic!("map's clock is lower than the entries clock")
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use lwwreg::LWWReg;
    use orswot::Orswot;

    use quickcheck::{Arbitrary, Gen};

    type TestLWWMap =  Map<u8, LWWReg<u8, (u64, u16)>, u16>;

    #[derive(Debug, Clone, PartialEq)]
    enum Op {
        Rm(u8),
        Put(u8, (u8, u64, u16)),
        Up(u8, Option<(u8, u64, u16)>),
    }

    impl Op {
        fn apply(&self, map: &mut TestLWWMap, actor: u16) {
            match self.clone() {
                Op::Rm(key) => {
                    map.remove(key, actor);
                },
                Op::Put(key, (val, time, lww_actor)) => {
                    map.insert(
                        key,
                        LWWReg { val: val, dot: (time, lww_actor) },
                        actor
                    );
                },
                Op::Up(key, None) => {
                    map.update(key, |_| None, actor);
                }
                Op::Up(key, Some((val, dot, lww_actor))) => {
                    map.update(key, |mut reg| {
                        reg.update(val, (dot, lww_actor)).unwrap();
                        Some(reg)
                    }, actor);
                }
            };
        }
    }

    impl Arbitrary for Op {
        fn arbitrary<G: Gen>(g: &mut G) -> Op {
            let val: u8 = g.gen();
            let time: u64 = g.gen();
            let actor: u16 = g.gen();
            let key: u8 = g.gen();

            let up_choices = [None, Some((val, time, actor))];
            let choices = [
                Op::Rm(key),
                Op::Put(key, (val, time, actor)),
                Op::Up(key, *(g.choose(&up_choices).unwrap()))
            ];
            let op = g.choose(&choices).unwrap();
            op.clone()
        }

        fn shrink(&self) -> Box<Iterator<Item = Op>> {
            let vec: Vec<Op> = match self.clone() {
                Op::Rm(key) =>
                    vec![Op::Rm(key/2)],
                Op::Put(key, (val, time, actor)) =>
                    vec![Op::Put(key/2, (val, time, actor)),
                         Op::Put(key, (val/2, time, actor)),
                         Op::Put(key, (val, time/2, actor)),
                         Op::Put(key, (val, time, actor/2))],
                Op::Up(key, None) =>
                    vec![Op::Up(key/2, None),
                         Op::Rm(key)],
                Op::Up(key, Some((val, time, actor))) =>
                    vec![Op::Up(key/2, Some((val, time, actor))),
                         Op::Up(key, Some((val/2, time, actor))),
                         Op::Up(key, Some((val, time/2, actor))),
                         Op::Up(key, Some((val, time, actor/2))),
                         Op::Up(key, None)]
            };
            let self_snapshot = self.clone();
            Box::new(
                vec.into_iter()
                    .filter(move |op| op != &self_snapshot)
            )
        }
    }

    #[test]
    fn test_new() {
        let m: TestLWWMap = Map::new();
        assert_eq!(m.len(), 0);
    }

    #[test]
    fn test_default() {
        let m: TestLWWMap = Map::default();
        assert_eq!(m, Map::new());
    }

    #[test]
    fn test_get() {
        let mut m: TestLWWMap = Map::new();

        assert_eq!(m.get(&0), None);

        m.clock.increment(1);
        m.entries.insert(0, MapEntry {
            clock: m.clock.clone(),
            birth_clock: VClock::new(),
            val: LWWReg::default()
        });

        assert_eq!(m.get(&0), Some(&LWWReg { val: 0, dot: (0, 0) }));
    }

    #[test]
    fn test_insert() {
        let mut m: TestLWWMap = Map::new();
        m.insert(32, LWWReg::default(), 1);
        assert_eq!(m.get(&32), Some(&LWWReg { val: 0, dot: (0, 0) }));
        assert_eq!(m.len(), 1);
    }

    #[test]
    fn test_update() {
        let mut m: TestLWWMap = Map::new();

        // constructs a default value if reg does not exist
        m.update(
            101,
            |mut reg| {
                assert_eq!(reg, LWWReg::default());
                let new_val = (reg.val + 1) * 2;
                let new_dot = (reg.dot.0 + 1, 1);
                assert!(reg.update(new_val, new_dot).is_ok());
                Some(reg)
            },
            1
        );
        assert_eq!(m.get(&101), Some(&LWWReg { val: 2, dot: (1, 1) }));

        // Updating once more, the map should give the closure last updated val
        m.update(
            101,
            |mut reg| {
                assert_eq!(reg, LWWReg { val: 2, dot: (1, 1) });
                let new_val = (reg.val + 1) * 2;
                let new_dot = (reg.dot.0 + 1, 1);
                assert!(reg.update(new_val, new_dot).is_ok());
                Some(reg)
            },
            1
        );

        assert_eq!(m.get(&101), Some(&LWWReg { val: 6, dot: (2, 1) }));

        // Returning None from the closure should remove the element
        m.update(
            101,
            |reg| {
                assert_eq!(reg, LWWReg { val: 6, dot: (2, 1) });
                None
            },
            1
        );

        assert_eq!(m.get(&101), None);
    }

    #[test]
    fn test_remove() {
        let mut m: TestLWWMap = Map::new();

        m.insert(101, LWWReg { val: 6, dot: (2, 1) }, 1);
        assert_eq!(m.get(&101), Some(&LWWReg { val: 6, dot: (2, 1) }));

        m.remove(101, 2);

        assert_eq!(m.get(&101), None);
    }

    #[test]
    fn test_reset_remove_semantics() {
        let mut m1: Map<String, Orswot<u8, String>, String> = Map::new();
        m1.update(
            "x".into(),
            |mut x_set| {
                x_set.add(1, "a1".into());
                Some(x_set)
            },
            "a1".into()
        );

        let mut m2 = m1.clone();

        m1.remove("x".into(), "a1".into());

        m2.update(
            "x".into(),
            |mut x_set| {
                x_set.add(2, "a2".into());
                Some(x_set)
            },
            "a2".into()
        );

        println!("m1 {:?}", m1);
        println!("m2 {:?}", m2);
        let m1_snapshot = m1.clone();
        assert!(m1.merge(&m2).is_ok());
        assert!(m2.merge(&m1_snapshot).is_ok());

        println!("m1 {:?}", m1);
        println!("m2 {:?}", m2);

        assert_eq!(m1, m2);

        let x_set = m1.get(&"x".into()).unwrap();
        assert_eq!(x_set.value(), vec![2]);
    }

    fn apply_ops(map: &mut TestLWWMap, ops: &[Op], actor: u16) {
        for op in ops.iter() {
            op.apply(map, actor);
        }
    }

    quickcheck! {
        fn prop_associativity(
            ops1: Vec<Op>,
            ops2: Vec<Op>,
            ops3: Vec<Op>
        ) -> bool {
            let mut m1 = Map::new();
            let mut m2 = Map::new();
            let mut m3 = Map::new();

            apply_ops(&mut m1, &ops1, 1);
            apply_ops(&mut m2, &ops2, 2);
            apply_ops(&mut m3, &ops3, 3);

            let mut m1_snapshot = m1.clone();

            // (m1 ^ m2) ^ m3
            assert!(m1.merge(&m2).is_ok());
            assert!(m1.merge(&m3).is_ok());

            // m1 ^ (m2 ^ m3)
            assert!(m2.merge(&m3).is_ok());
            assert!(m1_snapshot.merge(&m2).is_ok());

            // (m1 ^ m2) ^ m3 = m1 ^ (m2 ^ m3)
            m1 == m1_snapshot
        }

        fn prop_commutativity(ops1: Vec<Op>, ops2: Vec<Op>) -> bool {
            let mut m1 = Map::new();
            let mut m2 = Map::new();

            apply_ops(&mut m1, &ops1, 1);
            apply_ops(&mut m2, &ops2, 2);

            // m1 ^ m2
            assert!(m1.merge(&m2).is_ok());

            // m2 ^ m1
            assert!(m2.merge(&m1).is_ok());

            // m1 ^ m2 = m2 ^ m1
            m1 == m2
        }

        fn prop_idempotency(ops: Vec<Op>) -> bool {
            let mut m = Map::new();
            apply_ops(&mut m, &ops, 1);
            let m_snapshot = m.clone();

            // m ^ m
            assert!(m.merge(&m_snapshot).is_ok());

            // m ^ m = m
            m == m_snapshot
        }

        fn prop_repeated_merge(
            op_pairs: Vec<(Op, Op)>,
            skip_merge: u8
        ) -> bool {
            let mut m1 = Map::new();
            let mut m2 = Map::new();

            let mut merge_count = skip_merge;
            for (op1, op2) in op_pairs.iter() {
                op1.apply(&mut m1, 1);
                op2.apply(&mut m2, 2);
                if merge_count == 0 {
                    merge_count = skip_merge;
                    assert!(m1.merge(&m2).is_ok());
                    assert!(m2.merge(&m1).is_ok());
                    if m1 != m2 { return false }
                } else {
                    merge_count -= 1;
                }
            }

            assert!(m1.merge(&m2).is_ok());
            assert!(m2.merge(&m1).is_ok());

            m1 == m2
        }
    }
}
