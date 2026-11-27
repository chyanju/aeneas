//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
//! A join after a branching, after a call which took a shared reference to a
//! value whose type hides a `'static` borrow: the call leaves a region
//! abstraction for `'static` with a projected shared borrow, which the
//! preparation of the join doesn't destructure. The join then falls back to
//! duplicating the code which follows the branching in each branch.

pub enum Cause {
    Failure(&'static str),
    Other,
}

/// Takes the cause by shared reference, without reading it.
pub fn weigh(_c: &Cause, w: u32) -> u32 {
    w
}

pub fn check(x: u32) -> Result<u32, Cause> {
    if x > 3 {
        Err(Cause::Failure("big"))
    } else {
        Ok(x)
    }
}

pub fn with_if(c: Cause, w: u32, b: bool) -> u32 {
    let o = weigh(&c, w) > 2;
    let x = if b { 1 } else { 2 };
    if o {
        x
    } else {
        0
    }
}

pub fn with_match(c: Cause, w: u32, n: u32) -> u32 {
    let o = weigh(&c, w) > 2;
    let x = match n {
        0 => 1,
        1 => 5,
        _ => 2,
    };
    if o {
        x
    } else {
        0
    }
}

pub fn with_and(c: Cause, w: u32, b: bool) -> u32 {
    let o = weigh(&c, w) > 2;
    let x = b && o;
    if x {
        1
    } else {
        0
    }
}

pub fn ref_param(c: &Cause, w: u32, b: bool) -> u32 {
    let o = weigh(c, w) > 2;
    let x = if b { 1 } else { 2 };
    if o {
        x
    } else {
        0
    }
}

/// The call is a method of the standard library.
pub fn match_assigns(mut c: Option<Cause>, x: u32) -> Option<Cause> {
    let o = c.is_none();
    match check(x) {
        Err(e) => c = Some(e),
        Ok(_) => {}
    }
    if o {
        c
    } else {
        None
    }
}

#[verify::test]
pub fn test_joins() {
    assert!(with_if(Cause::Other, 3, true) == 1);
    assert!(with_if(Cause::Other, 3, false) == 2);
    assert!(with_if(Cause::Failure("x"), 1, true) == 0);
    assert!(with_match(Cause::Other, 3, 0) == 1);
    assert!(with_match(Cause::Other, 3, 1) == 5);
    assert!(with_match(Cause::Other, 3, 7) == 2);
    assert!(with_match(Cause::Other, 1, 1) == 0);
    assert!(with_and(Cause::Other, 3, true) == 1);
    assert!(with_and(Cause::Other, 3, false) == 0);
    assert!(with_and(Cause::Other, 1, true) == 0);
    assert!(ref_param(&Cause::Other, 3, false) == 2);
    assert!(match_assigns(None, 5).is_some());
    assert!(match_assigns(None, 2).is_none());
    assert!(match_assigns(Some(Cause::Other), 5).is_none());
}
