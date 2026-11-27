//@ [!lean] skip
//@ [lean] known-failure
//@ [lean] no-abort-on-error
//@ [lean] aeneas-args=-log-error MainLogger
// A trait method whose signature can't be translated (here because of the constraint on the
// associated type of the trait itself) is dropped from the trait declaration: the declaration,
// the implementations and the uses of the other methods are translated, and a use of the dropped
// method through a trait clause fails. The same holds for a method which the model of a builtin
// trait does not define (`Iterator::count`).

pub trait Tr {
    type Item;
    fn value(&self) -> u32;
    fn bad<T: Copy>(self) -> u32
    where
        Self: Sized + Tr<Item = T>,
    {
        0
    }
}

pub struct S {
    pub n: u32,
}

impl Tr for S {
    type Item = u32;
    fn value(&self) -> u32 {
        self.n
    }
}

pub fn call_value<X: Tr>(x: &X) -> u32 {
    x.value()
}

pub fn call_value_s(x: &S) -> u32 {
    x.value()
}

pub fn call_bad<X: Tr<Item = u32>>(x: X) -> u32 {
    x.bad()
}

pub fn call_bad_s(x: S) -> u32 {
    x.bad()
}

pub fn generic_count<I: Iterator<Item = u32>>(it: I) -> usize {
    it.count()
}

pub fn incr(x: u32) -> u32 {
    x + 1
}
