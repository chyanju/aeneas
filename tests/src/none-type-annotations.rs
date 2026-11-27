//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
//! Expressions whose type Lean can't infer, and which we thus annotate: a
//! lambda which ignores its input and returns `None`, and a `None` given to a
//! function whose type parameter nothing else determines.

pub struct Memo {
    pub v: Vec<u64>,
}

impl Memo {
    pub fn get(&self, k: usize) -> Option<&u64> {
        if k < self.v.len() {
            Some(&self.v[k])
        } else {
            None
        }
    }
}

pub struct Ctx<'a> {
    pub memo: Option<&'a mut Memo>,
    pub n: u64,
}

// In the branch where `ctx.memo` is `None`, the backward function of the
// shared match is `fun o => none`.
pub fn cached_or_push(ctx: &mut Ctx<'_>) -> u64 {
    let cached = match &ctx.memo {
        Some(m) => match m.get(0) {
            Some(v) => Some(*v),
            None => None,
        },
        None => None,
    };
    if let Some(v) = cached {
        return v;
    }
    ctx.n += 1;
    if let Some(m) = &mut ctx.memo {
        m.v.push(ctx.n);
    }
    ctx.n
}

// In the branch where `o` is `None`, the call is `Option.take none`, and it is
// the bound expression of a let-binding.
pub fn take_of_none(o: &mut Option<Memo>) -> u64 {
    match o {
        Some(_) => 1,
        None => match o.take() {
            Some(m) => m.v.len() as u64,
            None => 0,
        },
    }
}

// In the branch where `o` is `None`, the call is `Option.is_some none`, whose
// output type doesn't mention the type parameter.
pub fn is_some_of_none(o: &Option<Memo>) -> bool {
    match o {
        Some(_) => true,
        None => o.is_some(),
    }
}

#[verify::test]
pub fn test_cached_or_push() {
    // Without a memo
    let mut ctx = Ctx { memo: None, n: 1 };
    assert!(cached_or_push(&mut ctx) == 2);
    assert!(ctx.n == 2);
    assert!(ctx.memo.is_none());
    // With an empty memo: the new value is pushed
    let mut m = Memo { v: Vec::new() };
    let mut ctx = Ctx {
        memo: Some(&mut m),
        n: 5,
    };
    assert!(cached_or_push(&mut ctx) == 6);
    assert!(ctx.n == 6);
    // The cached value is returned, and nothing changes
    assert!(cached_or_push(&mut ctx) == 6);
    assert!(ctx.n == 6);
    assert!(m.v.len() == 1);
    assert!(m.v[0] == 6);
}

#[verify::test]
pub fn test_none_arguments() {
    let mut o = None;
    assert!(take_of_none(&mut o) == 0);
    assert!(o.is_none());
    assert!(!is_some_of_none(&o));
    let mut o = Some(Memo { v: Vec::new() });
    assert!(take_of_none(&mut o) == 1);
    assert!(is_some_of_none(&o));
}
