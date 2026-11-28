//@ [!lean] skip
//@ [lean] subdir=VecMethods
#![feature(register_tool)]
#![register_tool(verify)]
//! Tests for the Lean models of `Vec` methods (`Vec::is_empty`, `Vec::insert`).
//!
//! `new_is_empty` and `pushed_is_empty` are the examples of the documentation of
//! `Vec::is_empty` (<https://doc.rust-lang.org/std/vec/struct.Vec.html#method.is_empty>),
//! `insert_doc` is the example of the documentation of `Vec::insert`
//! (<https://doc.rust-lang.org/std/vec/struct.Vec.html#method.insert>).

pub fn new_is_empty() -> bool {
    let v: Vec<i32> = Vec::new();
    v.is_empty()
}

#[verify::test]
pub fn test_new_is_empty() {
    assert!(new_is_empty());
}

pub fn pushed_is_empty() -> bool {
    let mut v = Vec::new();
    v.push(1);
    v.is_empty()
}

#[verify::test]
pub fn test_pushed_is_empty() {
    assert!(!pushed_is_empty());
}

/// `is_empty` guarding an index: the first element, or `default` for an empty vector.
pub fn first_or(v: &Vec<u32>, default: u32) -> u32 {
    if v.is_empty() {
        default
    } else {
        v[0]
    }
}

#[verify::test]
pub fn test_first_or() {
    let mut v = Vec::new();
    assert_eq!(first_or(&v, 7), 7);
    v.push(3);
    assert_eq!(first_or(&v, 7), 3);
}

/// The example of the documentation of `Vec::insert`, on `['a', 'b', 'c']`: an insertion
/// inside the vector, then one at its length, which appends.
pub fn insert_doc(vec: &mut Vec<char>) {
    vec.insert(1, 'd');
    vec.insert(4, 'e');
}

#[verify::test]
pub fn test_insert_doc() {
    let mut vec = vec!['a', 'b', 'c'];
    insert_doc(&mut vec);
    assert_eq!(vec.len(), 5);
    assert_eq!(vec[0], 'a');
    assert_eq!(vec[1], 'd');
    assert_eq!(vec[2], 'b');
    assert_eq!(vec[3], 'c');
    assert_eq!(vec[4], 'e');
}

/// `x` inserted at `index`: Rust panics if `index > len`.
pub fn insert_at(v: &mut Vec<u32>, index: usize, x: u32) {
    v.insert(index, x);
}

#[verify::test]
pub fn test_insert_at() {
    // Into an empty vector: `index = len = 0`.
    let mut v = Vec::new();
    insert_at(&mut v, 0, 5);
    assert_eq!(v.len(), 1);
    assert_eq!(v[0], 5);
    // At the front.
    insert_at(&mut v, 0, 3);
    assert_eq!(v.len(), 2);
    assert_eq!(v[0], 3);
    assert_eq!(v[1], 5);
    // In the middle.
    insert_at(&mut v, 1, 4);
    assert_eq!(v.len(), 3);
    assert_eq!(v[0], 3);
    assert_eq!(v[1], 4);
    assert_eq!(v[2], 5);
    // At the length.
    insert_at(&mut v, 3, 6);
    assert_eq!(v.len(), 4);
    assert_eq!(v[3], 6);
}

/// An insertion at the length of the vector.
pub fn insert_at_len(v: &mut Vec<u32>, x: u32) {
    let n = v.len();
    v.insert(n, x);
}

#[verify::test]
pub fn test_insert_at_len() {
    let mut v = Vec::new();
    insert_at_len(&mut v, 1);
    insert_at_len(&mut v, 2);
    assert_eq!(v.len(), 2);
    assert_eq!(v[0], 1);
    assert_eq!(v[1], 2);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn vec_methods() {
        test_new_is_empty();
        test_pushed_is_empty();
        test_first_or();
        test_insert_doc();
        test_insert_at();
        test_insert_at_len();
    }

    #[test]
    #[should_panic(expected = "insertion index (is 1) should be <= len (is 0)")]
    fn insert_past_len_panics() {
        let mut v = Vec::new();
        insert_at(&mut v, 1, 7);
    }
}
