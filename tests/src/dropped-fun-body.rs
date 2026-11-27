//@ [!lean] skip
//@ [lean] known-failure
//@ [lean] no-abort-on-error
//@ [lean] aeneas-args=-log-error MainLogger
// The translation of the body of `as_mut_of_none` to pure code fails: the function is extracted
// without its body, like an opaque function, and a warning says so.

pub struct Memo {
    pub v: Vec<u64>,
}

pub struct Ctx<'a> {
    pub memo: Option<&'a mut Memo>,
    pub n: u64,
}

pub fn as_mut_of_none(ctx: &mut Ctx<'_>) -> u64 {
    match &ctx.memo {
        Some(_) => 1,
        None => match ctx.memo.as_mut() {
            Some(m) => m.v.len() as u64,
            None => 0,
        },
    }
}

pub fn incr(x: u32) -> u32 {
    x + 1
}
