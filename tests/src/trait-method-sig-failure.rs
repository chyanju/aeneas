//@ [!lean] skip
//@ [lean] known-failure
//@ [lean] no-abort-on-error
//@ [lean] aeneas-args=-log-error MainLogger
// A trait method whose signature can't be translated (here because of a generic associated type):
// the trait, its implementation and the uses of the trait fail, and the other definitions are
// translated.

pub trait Tr {
    type Out<'a>
    where
        Self: 'a;
    fn get<'a>(&'a self) -> Self::Out<'a>;
    fn ok(&self) -> u32;
}

pub struct S;

impl Tr for S {
    type Out<'a> = &'a S;
    fn get<'a>(&'a self) -> &'a S {
        self
    }
    fn ok(&self) -> u32 {
        0
    }
}

pub fn call_ok<X: Tr>(x: &X) -> u32 {
    x.ok()
}

pub fn incr(x: u32) -> u32 {
    x + 1
}
