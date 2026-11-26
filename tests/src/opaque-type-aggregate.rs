//@ [!lean] skip
//@ [lean] known-failure
//@ [lean] no-abort-on-error
//@ [lean] aeneas-args=-log-error MainLogger
//@ charon-args=--opaque crate::R --opaque crate::P --opaque crate::E --opaque crate::D
// Values of opaque types can't be built: the functions that build one fail one by one, and the
// other definitions are translated.

pub struct R(pub u32);

pub struct P {
    pub a: u32,
    pub b: u32,
}

pub enum E {
    A(u32),
    B,
}

#[derive(Default)]
pub struct D(pub u32);

pub fn mk_r(x: u32) -> R {
    R(x)
}

pub fn mk_p(a: u32) -> P {
    P { a, b: 0 }
}

pub fn mk_e(x: u32) -> E {
    E::A(x)
}

pub fn mk_e_unit() -> E {
    E::B
}

pub fn default_d() -> D {
    D::default()
}

pub fn pass(r: R) -> R {
    r
}

pub fn incr(x: u32) -> u32 {
    x + 1
}
