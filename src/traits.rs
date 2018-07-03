use serde::Serialize;
use serde::de::DeserializeOwned;

use error::Result;
use vclock::VClock;

/// ComposableCrdt's can be nested into other CRDT's like Map
pub trait ComposableCrdt<A>: Default where
    A : Ord + Clone + Serialize + DeserializeOwned
{
    /// Construct the default CRDT with the CRDT clock set to the given clock
    fn default_with_clock(clock: VClock<A>) -> Self;

    /// merge the other CRDT into this CRDT.
    fn merge(&mut self, other: &Self) -> Result<()>;
}
