extern crate crdts;
use crdts::{CmRDT, CvRDT, VClock};
use std::cmp::Ordering::*;

fn main() {
    #[derive(Debug, Default, Clone, PartialEq)]
    struct VersionedString {
        clock: VClock<String>,
        data: String,
    }
    let shared_password = VersionedString::default();

    // alice and bob take a copy ...
    let mut bobs_copy = shared_password.clone();
    let mut alices_copy = shared_password.clone();

    // bob edits the shared password..
    bobs_copy
        .clock
        .apply(bobs_copy.clock.inc("BOB".to_string()));
    bobs_copy.data = "pa$$w0rd".to_string();

    // ... and shares it with alice.

    // Alice first compares the vclock of her copy with bob's:
    match alices_copy.clock.partial_cmp(&bobs_copy.clock) {
        Some(Less) => { /* bob's clock is ahead */ }
        _ => panic!("Bob's clock should be ahead!!"),
    }
    // Alice sees that bob's clock is ahead of hers.
    // This tells her that Bob has seen every edit she has
    // seen and his string is a more recent version.
    alices_copy = bobs_copy.clone();

    // Now, alice decides to changes the password.
    alices_copy
        .clock
        .apply(alices_copy.clock.inc("ALICE".to_string()));
    alices_copy.data = "letMein32".to_string();

    // But! concurrently, bob edits the password again!
    bobs_copy
        .clock
        .apply(bobs_copy.clock.inc("BOB".to_string()));
    bobs_copy.data = "0sdjf0as9j13k0zc".to_string();

    // Alice shares her edit with bob and bob compares clocks
    match bobs_copy.clock.partial_cmp(&alices_copy.clock) {
        None => { /* these clocks are not ordered! */ }
        _ => panic!("These clocks are not ordered!"),
    }

    // If we take a look at the clocks we see the problem.
    assert_eq!(format!("{}", bobs_copy.clock), "<BOB:2>");
    assert_eq!(format!("{}", alices_copy.clock), "<ALICE:1, BOB:1>");

    // bob's version counter is bigger on his copy but alices
    // version counter is bigger on her copy
    // (version counters default to 0 if not present in a clock)

    // This is how VClocks can be used to detect conflicts.
    // Bob needs to manually look at the two strings and decide
    // how to manage this conflict.

    // Bob decides to keep Alices string, he merges alices clock
    // into his to signify that he has seen her edits.
    bobs_copy.clock.merge(alices_copy.clock.clone());
    bobs_copy.data = "letMein32".to_string();

    // looking once more at bob's clock we see it includes all
    // edits done by both bob and alice
    assert_eq!(format!("{}", bobs_copy.clock), "<ALICE:1, BOB:2>");

    // Once Alice receives bob's updated password she'll see that
    // his clock is ahead of hers and choose to keep his versioned string.
    match alices_copy.clock.partial_cmp(&bobs_copy.clock) {
        Some(Less) => {
            // bob's clock is ahead
            alices_copy = bobs_copy.clone()
        }
        _ => panic!("Alice's clock should be behind!!"),
    }

    assert_eq!(alices_copy, bobs_copy);
}
