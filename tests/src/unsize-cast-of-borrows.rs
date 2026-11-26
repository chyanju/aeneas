//@ [!lean] skip
//@ [lean] known-failure
//@ [lean] no-abort-on-error
//@ [lean] aeneas-args=-log-error MainLogger
// Unsizing casts of boxes whose content holds borrows are not supported: the functions that use
// them fail one by one, and the other definitions are translated.

// The cast of a parameter
pub fn unsize_param<'a>(b: Box<[&'a u32; 1]>) -> Box<[&'a u32]> {
    b
}

// `vec![x]` casts `Box<[&u32; 1]>` to `Box<[&u32]>`. With `-checks`, the error is raised before
// the cast, by the check of the typing invariants.
pub fn vec_of_ref(x: &u32) -> Vec<&u32> {
    vec![x]
}

pub fn unsize_param_u32(b: Box<[u32; 1]>) -> Box<[u32]> {
    b
}

pub fn push_ref(x: &u32) -> Vec<&u32> {
    let mut v = Vec::new();
    v.push(x);
    v
}
