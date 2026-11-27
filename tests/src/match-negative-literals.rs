//@ [!lean] skip
//@ [lean] subdir=MatchNegativeLiterals
#![feature(register_tool)]
#![register_tool(verify)]
//! Matches over signed integers with negative literal patterns: in a Lean
//! pattern a negative value is written as the bit-vector literal of its two's
//! complement. The theorems of `Properties.lean` state that every match takes
//! the branch of a pattern for the value of this pattern exactly.

pub const TRUE: i8 = 1;
pub const FALSE: i8 = -1;

pub fn code_i8(v: i8) -> u8 {
    match v {
        TRUE => 1,
        FALSE => 0,
        _ => 2,
    }
}

pub fn bounds_i8(v: i8) -> u8 {
    match v {
        -128 => 1,
        -127 => 2,
        -2 => 3,
        127 => 4,
        0 => 5,
        _ => 0,
    }
}

pub fn negative_only_i8(v: i8) -> u8 {
    match v {
        -1 => 1,
        -2 => 2,
        _ => 0,
    }
}

pub fn code_i16(v: i16) -> u8 {
    match v {
        -1 => 1,
        -32768 => 2,
        1 => 3,
        _ => 0,
    }
}

pub fn code_i32(v: i32) -> u8 {
    match v {
        -1 => 1,
        -2147483648 => 2,
        1 => 3,
        _ => 0,
    }
}

pub fn code_i64(v: i64) -> u8 {
    match v {
        -1 => 1,
        -9223372036854775808 => 2,
        1 => 3,
        _ => 0,
    }
}

pub fn code_i128(v: i128) -> u8 {
    match v {
        -1 => 1,
        -170141183460469231731687303715884105728 => 2,
        1 => 3,
        _ => 0,
    }
}

#[verify::test]
pub fn test_code_i8() {
    assert!(code_i8(1) == 1);
    assert!(code_i8(-1) == 0);
    assert!(code_i8(0) == 2);
    assert!(code_i8(-2) == 2);
    assert!(code_i8(127) == 2);
    assert!(code_i8(-128) == 2);
    assert!(bounds_i8(-128) == 1);
    assert!(bounds_i8(-127) == 2);
    assert!(bounds_i8(-2) == 3);
    assert!(bounds_i8(127) == 4);
    assert!(bounds_i8(0) == 5);
    assert!(bounds_i8(-1) == 0);
    assert!(bounds_i8(126) == 0);
    assert!(negative_only_i8(-1) == 1);
    assert!(negative_only_i8(-2) == 2);
    assert!(negative_only_i8(1) == 0);
}

#[verify::test]
pub fn test_code_wide() {
    assert!(code_i16(-1) == 1);
    assert!(code_i16(-32768) == 2);
    assert!(code_i16(1) == 3);
    assert!(code_i16(32767) == 0);
    assert!(code_i32(-1) == 1);
    assert!(code_i32(-2147483648) == 2);
    assert!(code_i32(1) == 3);
    assert!(code_i32(2147483647) == 0);
    assert!(code_i64(-1) == 1);
    assert!(code_i64(-9223372036854775808) == 2);
    assert!(code_i64(1) == 3);
    assert!(code_i64(9223372036854775807) == 0);
    assert!(code_i128(-1) == 1);
    assert!(code_i128(-170141183460469231731687303715884105728) == 2);
    assert!(code_i128(1) == 3);
    assert!(code_i128(170141183460469231731687303715884105727) == 0);
}
