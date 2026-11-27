//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
//! The crate uses methods of `Iterator` which its model in the backend does
//! not define (`count`, `copied`, `cloned`; the signatures of the last two
//! can't be translated as fields of the trait declaration). The trait
//! declaration is the model, the implementations of the trait only define the
//! methods of the model, and the calls to the other methods on a known type
//! are calls to their default implementations.

pub struct Counter {
    pub n: u32,
}

impl Iterator for Counter {
    type Item = u32;
    fn next(&mut self) -> Option<u32> {
        if self.n < 5 {
            self.n += 1;
            Some(self.n)
        } else {
            None
        }
    }
}

pub struct Refs<'a> {
    pub s: &'a [u32],
    pub i: usize,
}

impl<'a> Iterator for Refs<'a> {
    type Item = &'a u32;
    fn next(&mut self) -> Option<&'a u32> {
        if self.i < self.s.len() {
            let x = &self.s[self.i];
            self.i += 1;
            Some(x)
        } else {
            None
        }
    }
}

pub fn use_next() -> u32 {
    let mut c = Counter { n: 0 };
    let mut s = 0;
    while let Some(x) = c.next() {
        s += x;
    }
    s
}

pub fn use_count(c: Counter) -> usize {
    c.count()
}

pub fn use_copied(r: Refs<'_>) -> u32 {
    let mut s = 0;
    for x in r.copied() {
        s += x;
    }
    s
}

pub fn use_cloned(r: Refs<'_>) -> u32 {
    let mut s = 0;
    for x in r.cloned() {
        s += x;
    }
    s
}

pub fn generic_next<I: Iterator<Item = u32>>(it: &mut I) -> u32 {
    match it.next() {
        Some(x) => x,
        None => 0,
    }
}

#[verify::test]
pub fn test_next() {
    assert!(use_next() == 15);
    let mut c = Counter { n: 3 };
    assert!(generic_next(&mut c) == 4);
    assert!(generic_next(&mut c) == 5);
    assert!(generic_next(&mut c) == 0);
}
