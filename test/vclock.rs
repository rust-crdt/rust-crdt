use crdts::{CmRDT, CvRDT, Dot, ResetRemove, VClock};

#[test]
fn test_reset_remove() {
    let mut a: VClock<u8> = vec![Dot::new(1, 4), Dot::new(2, 3), Dot::new(5, 9)]
        .into_iter()
        .collect();
    let b: VClock<u8> = vec![Dot::new(1, 5), Dot::new(2, 3), Dot::new(5, 8)]
        .into_iter()
        .collect();
    let expected: VClock<u8> = vec![Dot::new(5, 9)].into_iter().collect();

    a.reset_remove(&b);
    assert_eq!(a, expected);
}

#[test]
fn test_merge() {
    let mut a: VClock<u8> = vec![Dot::new(1, 1), Dot::new(4, 4)].into_iter().collect();
    let b: VClock<u8> = vec![Dot::new(3, 3), Dot::new(4, 3)].into_iter().collect();

    a.merge(b);

    let expected: VClock<u8> = vec![Dot::new(1, 1), Dot::new(3, 3), Dot::new(4, 4)]
        .into_iter()
        .collect();

    assert_eq!(a, expected);
}

#[test]
fn test_merge_less_left() {
    let (mut a, mut b) = (VClock::new(), VClock::new());
    a.apply(Dot::new(5, 5));

    b.apply(Dot::new(6, 6));
    b.apply(Dot::new(7, 7));

    a.merge(b);
    assert_eq!(a.get(&5), 5);
    assert_eq!(a.get(&6), 6);
    assert_eq!(a.get(&7), 7);
}

#[test]
fn test_merge_less_right() {
    let (mut a, mut b) = (VClock::new(), VClock::new());
    a.apply(Dot::new(6, 6));
    a.apply(Dot::new(7, 7));

    b.apply(Dot::new(5, 5));

    a.merge(b);
    assert_eq!(a.get(&5), 5);
    assert_eq!(a.get(&6), 6);
    assert_eq!(a.get(&7), 7);
}

#[test]
fn test_merge_same_id() {
    let (mut a, mut b) = (VClock::new(), VClock::new());
    a.apply(Dot::new(1, 1));
    a.apply(Dot::new(2, 1));

    b.apply(Dot::new(1, 1));
    b.apply(Dot::new(3, 1));

    a.merge(b);
    assert_eq!(a.get(&1), 1);
    assert_eq!(a.get(&2), 1);
    assert_eq!(a.get(&3), 1);
}

#[test]
#[allow(clippy::neg_cmp_op_on_partial_ord)]
fn test_vclock_ordering() {
    assert_eq!(VClock::<i8>::new(), VClock::new());

    let (mut a, mut b) = (VClock::new(), VClock::new());
    a.apply(Dot::new("A".to_string(), 1));
    a.apply(Dot::new("A".to_string(), 2));
    a.apply(Dot::new("A".to_string(), 0));
    b.apply(Dot::new("A".to_string(), 1));

    // a {A:2}
    // b {A:1}
    // expect: a dominates
    assert!(a > b);
    assert!(b < a);
    assert!(a != b);

    b.apply(Dot::new("A".to_string(), 3));
    // a {A:2}
    // b {A:3}
    // expect: b dominates
    assert!(b > a);
    assert!(a < b);
    assert!(a != b);

    a.apply(Dot::new("B".to_string(), 1));
    // a {A:2, B:1}
    // b {A:3}
    // expect: concurrent
    assert!(a != b);
    assert!(!(a > b));
    assert!(!(b > a));

    a.apply(Dot::new("A".to_string(), 3));
    // a {A:3, B:1}
    // b {A:3}
    // expect: a dominates
    assert!(a > b);
    assert!(b < a);
    assert!(a != b);

    b.apply(Dot::new("B".to_string(), 2));
    // a {A:3, B:1}
    // b {A:3, B:2}
    // expect: b dominates
    assert!(b > a);
    assert!(a < b);
    assert!(a != b);

    a.apply(Dot::new("B".to_string(), 2));
    // a {A:3, B:2}
    // b {A:3, B:2}
    // expect: equal
    assert!(!(b > a));
    assert!(!(a > b));
    assert_eq!(a, b);
}

#[cfg(feature = "quickcheck")]
mod prop_tests {
    use super::*;

    use std::cmp::Ordering;

    use quickcheck_macros::quickcheck;

    #[quickcheck]
    fn prop_into_iter_produces_same_vclock(clock: VClock<u8>) -> bool {
        clock == clock.clone().into_iter().collect()
    }

    #[quickcheck]
    fn prop_dots_are_commutative_in_from_iter(dots: Vec<Dot<u8>>) -> bool {
        // TODO: is there a better way to check comutativity of dots?
        let reverse: VClock<u8> = dots.clone().into_iter().rev().collect();
        let forward: VClock<u8> = dots.into_iter().collect();

        reverse == forward
    }

    #[quickcheck]
    fn prop_idempotent_dots_in_from_iter(dots: Vec<Dot<u8>>) -> bool {
        let single: VClock<u8> = dots.clone().into_iter().collect();

        let double: VClock<u8> = dots.clone().into_iter().chain(dots.into_iter()).collect();

        single == double
    }

    #[quickcheck]
    fn prop_glb_self_is_nop(clock: VClock<u8>) -> bool {
        let mut clock_glb = clock.clone();
        clock_glb.glb(&clock);

        clock_glb == clock
    }

    #[quickcheck]
    fn prop_glb_commutes(a: VClock<u8>, b: VClock<u8>) -> bool {
        let mut a_glb = a.clone();
        a_glb.glb(&b);

        let mut b_glb = b;
        b_glb.glb(&a);

        a_glb == b_glb
    }

    #[quickcheck]
    fn prop_reset_remove_with_empty_is_nop(clock: VClock<u8>) -> bool {
        let mut subbed = clock.clone();
        subbed.reset_remove(&VClock::new());
        subbed == clock
    }

    #[quickcheck]
    fn prop_reset_remove_self_is_empty(clock: VClock<u8>) -> bool {
        let mut subbed = clock.clone();
        subbed.reset_remove(&clock);
        subbed == VClock::new()
    }

    #[quickcheck]
    fn prop_reset_remove_is_empty_implies_equal_or_greator(a: VClock<u8>, b: VClock<u8>) -> bool {
        let mut a = a;
        a.reset_remove(&b);

        if a.is_empty() {
            matches!(
                a.partial_cmp(&b),
                Some(Ordering::Less) | Some(Ordering::Equal)
            )
        } else {
            matches!(a.partial_cmp(&b), None | Some(Ordering::Greater))
        }
    }
}
