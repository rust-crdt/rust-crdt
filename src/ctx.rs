use serde::{Deserialize, Serialize};

use crate::traits::CmRDT;
use crate::vclock::{Actor, Dot, VClock};

/// ReadCtx's are used to extract data from CRDT's while maintaining some causal history.
/// You should store ReadCtx's close to where mutation is exposed to the user.
///
/// e.g. Ship ReadCtx to the clients, then derive an Add/RmCtx and ship that back to
/// where the CRDT is stored to perform the mutation operation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReadCtx<V, A: Actor> {
    /// clock used to derive an AddCtx
    pub add_clock: VClock<A>,

    /// clock used to derive an RmCtx
    pub rm_clock: VClock<A>,

    /// the data read from the CRDT
    pub val: V,
}

/// AddCtx is used for mutations add new information to a CRDT
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AddCtx<A: Actor> {
    /// The adding vclock context
    pub clock: VClock<A>,

    /// The Actor and the Actor's version at the time of the add
    pub dot: Dot<A>,
}

/// RmCtx is used for mutations that remove information from a CRDT
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RmCtx<A: Actor> {
    /// The removing vclock context
    pub clock: VClock<A>,
}

impl<V, A: Actor> ReadCtx<V, A> {
    /// Derives an AddCtx for a given actor from a ReadCtx
    pub fn derive_add_ctx(&self, actor: A) -> AddCtx<A> {
        let mut clock = self.add_clock.clone();
        let dot = clock.inc(actor);
        clock.apply(dot.clone());
        AddCtx { clock, dot }
    }

    /// Derives a RmCtx from a ReadCtx
    pub fn derive_rm_ctx(&self) -> RmCtx<A> {
        RmCtx {
            clock: self.rm_clock.clone(),
        }
    }
}
