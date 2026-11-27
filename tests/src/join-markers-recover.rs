//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
//! A `match` in a loop on a `Result` whose error type holds a `&'static str`,
//! whose `Ok` branch moves a value into a variable of the loop: the collapse of
//! the join of its branches leaves markers in the context. The join then falls
//! back to duplicating the code which follows the `match` in each branch.

pub enum E {
    Unavailable(&'static str),
    Overflow,
}

pub struct Q {
    pub n: u32,
    pub v: Vec<u32>,
}

pub fn step(q: &Q) -> Result<Q, E> {
    if q.n >= 3 {
        Err(E::Overflow)
    } else {
        Ok(Q {
            n: q.n + 1,
            v: Vec::new(),
        })
    }
}

pub fn grow(n: u32) -> (u32, bool) {
    let mut q = Q {
        n: 0,
        v: Vec::new(),
    };
    let mut failed = false;
    let mut k = 0;
    while k < n && !failed {
        match step(&q) {
            Ok(x) => q = x,
            Err(_) => failed = true,
        }
        k += 1;
    }
    (q.n, failed)
}

/// The `Ok` branch also adds to a counter behind a mutable borrow and updates
/// a second variable of the loop under a condition.
pub fn expand(g: &[u32], work: &mut u64) -> Option<u32> {
    let mut q = Q {
        n: 0,
        v: Vec::new(),
    };
    let mut sum = 0;
    let mut overflow = false;
    let mut k = 0;
    while k < g.len() && !overflow {
        match step(&q) {
            Ok(x) => {
                q = x;
                *work = work.saturating_add(q.n as u64);
                if g[k] != 0 {
                    sum += g[k];
                }
            }
            Err(_) => overflow = true,
        }
        k += 1;
    }
    if overflow {
        None
    } else {
        Some(sum)
    }
}

#[verify::test]
pub fn test_grow() {
    let (n, failed) = grow(2);
    assert!(n == 2);
    assert!(!failed);
    let (n, failed) = grow(5);
    assert!(n == 3);
    assert!(failed);
}

#[verify::test]
pub fn test_expand() {
    let mut work = 0;
    let g = [1, 0, 2];
    assert!(matches!(expand(&g, &mut work), Some(3)));
    assert!(work == 6);
    let mut work = 0;
    let g = [1, 1, 1, 1];
    assert!(expand(&g, &mut work).is_none());
    assert!(work == 6);
}
