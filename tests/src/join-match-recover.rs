//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
//! Regression tests.
//!
//! The join after a branching fails when we match the contexts of the
//! branches with the joined context. This failure must be *recoverable*, so
//! that we fall back to not joining: the code after the branching is
//! evaluated (and thus duplicated) in every branch.

// The region abstraction introduced by the indexing is still alive at the
// branching, and the join modifies it (by ending the abstraction of the call
// to `get_u32`): the contexts of the branches don't match the joined context.
pub struct Elem {
    pub v: u32,
}

pub fn get_u32(x: &u32) -> u32 {
    *x
}

pub fn call_on_elem_field_if(t: &[Elem], c: bool) -> u32 {
    let a = get_u32(&t[0].v);
    let x = if c { 1 } else { 2 };
    x + a
}

pub fn call_on_elem_field_match(t: &[Elem], o: Option<u32>) -> u32 {
    let a = get_u32(&t[0].v);
    let x = match o {
        Some(y) => y,
        None => 0,
    };
    x + a
}

pub fn call_on_elem_field_and(t: &[Elem], c: bool) -> u32 {
    let a = get_u32(&t[0].v);
    let ok = c && a > 3;
    ok as u32 + a
}

pub fn call_on_elem_field_in_loop(t: &[Elem], k: usize) -> u32 {
    let mut s = 0;
    let mut i = 0;
    while i < k {
        let a = get_u32(&t[i].v);
        let x = if a > 3 { 1 } else { 2 };
        s += x;
        i += 1;
    }
    s
}

// The input contains a shared borrow below a shared borrow, hidden inside a
// symbolic value which we can't expand (an option, a field whose type is an
// option): the matcher rejects the shared loan which contains this value.
pub fn nested_shared_input_option<'a, 'b>(_m: &'a Option<&'b u8>, a: bool) {
    if a {}
    if a {}
}

pub struct HiddenRef<'a> {
    pub n: u32,
    pub r: Option<&'a u32>,
}

pub fn nested_shared_input_field(x: &HiddenRef<'_>, c: bool) -> u32 {
    let z = if c { 1 } else { 2 };
    z + x.n
}

#[verify::test]
pub fn test_call_on_elem_field() {
    let t = [Elem { v: 5 }, Elem { v: 2 }];
    assert!(call_on_elem_field_if(&t, true) == 6);
    assert!(call_on_elem_field_if(&t, false) == 7);
    assert!(call_on_elem_field_match(&t, Some(10)) == 15);
    assert!(call_on_elem_field_match(&t, None) == 5);
    assert!(call_on_elem_field_and(&t, true) == 6);
    assert!(call_on_elem_field_and(&t, false) == 5);
    assert!(call_on_elem_field_in_loop(&t, 2) == 3);
}

#[verify::test]
pub fn test_nested_shared_input() {
    let r = 3;
    let x = HiddenRef { n: 4, r: Some(&r) };
    assert!(nested_shared_input_field(&x, true) == 5);
    assert!(nested_shared_input_field(&x, false) == 6);
}
