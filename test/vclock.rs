use crdts::*;

use std::cmp::Ordering;

pub fn build_vclock(prims: Vec<u8>) -> VClock<u8> {
    let mut v = VClock::new();
    for actor in prims {
        v.apply(v.inc(actor));
    }
    v
}

quickcheck! {
    fn prop_into_iter_produces_same_vclock(prims: Vec<u8>) -> bool {
        let clock = build_vclock(prims);
        clock == clock.clone().into_iter().collect()
    }

    fn prop_dots_are_commutative_in_from_iter(dots: Vec<(u8, u64)>) -> bool {
        // TODO: is there a better way to check comutativity of dots?
        let reverse: VClock<u8> = dots.clone()
            .into_iter()
            .map(|(a, c)| Dot::new(a, c))
            .rev()
            .collect();
        let forward: VClock<u8> = dots
            .into_iter()
            .map(|(a, c)| Dot::new(a, c))
            .collect();

        reverse == forward
    }

    fn prop_idempotent_dots_in_from_iter(dots: Vec<(u8, u64)>) -> bool {
        let single: VClock<u8> = dots.clone()
            .into_iter()
            .map(|(a, c)| Dot::new(a, c))
            .collect();

        let double: VClock<u8> = dots.clone()
            .into_iter()
            .chain(dots.into_iter())
            .map(|(a, c)| Dot::new(a, c))
            .collect();

        single == double
    }

    fn prop_glb_self_is_nop(prims: Vec<u8>) -> bool {
        let clock = build_vclock(prims);
        let mut clock_glb = clock.clone();
        clock_glb.glb(&clock);

        clock_glb == clock
    }

    fn prop_glb_commutes(prims_a: Vec<u8>, prims_b: Vec<u8>) -> bool {
        let a = build_vclock(prims_a);
        let b = build_vclock(prims_b);

        let mut a_glb = a.clone();
        a_glb.glb(&b);

        let mut b_glb = b.clone();
        b_glb.glb(&a);

        a_glb == b_glb
    }

    fn prop_forget_with_empty_is_nop(prims: Vec<u8>) -> bool {
        let clock = build_vclock(prims);
        let mut subbed  = clock.clone();
        subbed.forget(&VClock::new());
        subbed == clock
    }

    fn prop_forget_self_is_empty(prims: Vec<u8>) -> bool {
        let clock = build_vclock(prims);
        let mut subbed  = clock.clone();
        subbed.forget(&clock);
        subbed == VClock::new()
    }

    fn prop_forget_is_empty_implies_equal_or_greator(prims_a: Vec<u8>, prims_b: Vec<u8>) -> bool {
        let mut a = build_vclock(prims_a);
        let b = build_vclock(prims_b);

        a.forget(&b);

        if a.is_empty() {
            match a.partial_cmp(&b) {
                Some(Ordering::Less) | Some(Ordering::Equal) => true,
                _ => false
            }
        } else {
            match a.partial_cmp(&b) {
                None | Some(Ordering::Greater) => true,
                _ => false
            }
        }
    }
}

#[test]
fn test_forget() {
    let mut a: VClock<u8> = vec![Dot::new(1, 4), Dot::new(2, 3), Dot::new(5, 9)]
        .into_iter()
        .collect();
    let b: VClock<u8> = vec![Dot::new(1, 5), Dot::new(2, 3), Dot::new(5, 8)]
        .into_iter()
        .collect();
    let expected: VClock<u8> = vec![Dot::new(5, 9)].into_iter().collect();

    a.forget(&b);
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
