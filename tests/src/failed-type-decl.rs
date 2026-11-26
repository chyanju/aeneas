//@ [!lean] skip
//@ [lean] known-failure
//@ [lean] no-abort-on-error
//@ [lean] aeneas-args=-log-error MainLogger
// Types whose declaration can't be translated (here because of `dyn` fields): the functions that
// look into them fail one by one, and the other definitions are translated.

pub trait M {}

pub struct W<'a> {
    pub m: &'a mut dyn M,
    pub n: u32,
}

pub struct S<'a> {
    pub m: &'a dyn M,
    pub n: u32,
}

pub struct T(pub Box<dyn M>, pub u32);

pub enum E {
    A(Box<dyn M>),
    B(u32),
}

// The value given back for `w`
pub fn given_back(w: &mut W<'_>) {
    w.n += 1;
}

// A structure update
pub fn struct_update(s: &mut S<'_>) {
    s.n += 1;
}

// A constructor
pub fn constructor(x: u32) -> E {
    E::B(x)
}

// A tuple-struct pattern
pub fn tuple_field(t: &T) -> u32 {
    t.1
}

// A field projection
pub fn field_read(s: &S<'_>) -> u32 {
    s.n
}

pub fn incr(x: u32) -> u32 {
    x + 1
}
