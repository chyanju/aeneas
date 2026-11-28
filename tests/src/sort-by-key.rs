//@ [!lean] skip
//@ [lean] subdir=SortByKey
//! Tests for the Lean model of `<[T]>::sort_by_key`.
//!
//! `sort_abs` is the example of the documentation
//! (<https://doc.rust-lang.org/std/primitive.slice.html#method.sort_by_key>), with `k.abs()`
//! written as a comparison and a negation. The model is an opaque function of the elements, so
//! the translation is not evaluated: `SortByKey/Properties.lean` proves what the sorts give when
//! they return, and the Rust tests run the examples.

/// The example of the documentation.
pub fn sort_abs(v: &mut [i32]) {
    v.sort_by_key(|k| if *k < 0 { -*k } else { *k });
}

/// A stable sort: the pairs of equal first components keep their order.
pub fn sort_by_first(v: &mut [(u32, u32)]) {
    v.sort_by_key(|p| p.0);
}

/// A key computed with a captured value.
pub fn sort_by_residue(v: &mut [u32], m: u32) {
    v.sort_by_key(|x| *x % m);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sort_by_key_doc() {
        let mut v = [4i32, -5, 1, -3, 2];
        sort_abs(&mut v);
        assert_eq!(v, [1, 2, -3, 4, -5]);
    }

    #[test]
    fn sort_by_key_stable() {
        let mut v = [(2, 0), (1, 1), (2, 2), (1, 3)];
        sort_by_first(&mut v);
        assert_eq!(v, [(1, 1), (1, 3), (2, 0), (2, 2)]);
    }

    #[test]
    fn sort_by_key_residue() {
        let mut v = [7, 3, 10, 4];
        sort_by_residue(&mut v, 3);
        assert_eq!(v, [3, 7, 10, 4]);
    }

    #[test]
    #[should_panic]
    fn sort_by_key_residue_zero() {
        let mut v = [7, 3];
        sort_by_residue(&mut v, 0);
    }
}
