//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
//! A long chain of `if ... else if ...`: the code is nested so deeply that it
//! reaches the maximum indentation of the page. We then lay out the definition
//! on a wider page: otherwise the arguments of the calls, which do not fit on
//! the line of their function, are aligned with it, and Lean does not read
//! them as arguments.

pub fn combine_three_arguments(first: u32, second: u32, third: u32) -> u32 {
    first + second * 2 + third * 3
}

pub fn deep_chain(selector: u32, first_argument: u32, second_argument: u32) -> u32 {
    if selector == 0 {
        combine_three_arguments(first_argument, second_argument, 1)
    } else if selector == 1 {
        combine_three_arguments(first_argument, second_argument, 2)
    } else if selector == 2 {
        combine_three_arguments(first_argument, second_argument, 3)
    } else if selector == 3 {
        combine_three_arguments(first_argument, second_argument, 4)
    } else if selector == 4 {
        combine_three_arguments(first_argument, second_argument, 5)
    } else if selector == 5 {
        combine_three_arguments(first_argument, second_argument, 6)
    } else if selector == 6 {
        combine_three_arguments(first_argument, second_argument, 7)
    } else if selector == 7 {
        combine_three_arguments(first_argument, second_argument, 8)
    } else if selector == 8 {
        combine_three_arguments(first_argument, second_argument, 9)
    } else if selector == 9 {
        combine_three_arguments(first_argument, second_argument, 10)
    } else if selector == 10 {
        combine_three_arguments(first_argument, second_argument, 11)
    } else if selector == 11 {
        combine_three_arguments(first_argument, second_argument, 12)
    } else if selector == 12 {
        combine_three_arguments(first_argument, second_argument, 13)
    } else if selector == 13 {
        combine_three_arguments(first_argument, second_argument, 14)
    } else if selector == 14 {
        combine_three_arguments(first_argument, second_argument, 15)
    } else if selector == 15 {
        combine_three_arguments(first_argument, second_argument, 16)
    } else if selector == 16 {
        combine_three_arguments(first_argument, second_argument, 17)
    } else if selector == 17 {
        combine_three_arguments(first_argument, second_argument, 18)
    } else if selector == 18 {
        combine_three_arguments(first_argument, second_argument, 19)
    } else if selector == 19 {
        combine_three_arguments(first_argument, second_argument, 20)
    } else if selector == 20 {
        combine_three_arguments(first_argument, second_argument, 21)
    } else if selector == 21 {
        combine_three_arguments(first_argument, second_argument, 22)
    } else if selector == 22 {
        combine_three_arguments(first_argument, second_argument, 23)
    } else if selector == 23 {
        combine_three_arguments(first_argument, second_argument, 24)
    } else if selector == 24 {
        combine_three_arguments(first_argument, second_argument, 25)
    } else if selector == 25 {
        combine_three_arguments(first_argument, second_argument, 26)
    } else if selector == 26 {
        combine_three_arguments(first_argument, second_argument, 27)
    } else if selector == 27 {
        combine_three_arguments(first_argument, second_argument, 28)
    } else if selector == 28 {
        combine_three_arguments(first_argument, second_argument, 29)
    } else if selector == 29 {
        combine_three_arguments(first_argument, second_argument, 30)
    } else if selector == 30 {
        combine_three_arguments(first_argument, second_argument, 31)
    } else if selector == 31 {
        combine_three_arguments(first_argument, second_argument, 32)
    } else if selector == 32 {
        combine_three_arguments(first_argument, second_argument, 33)
    } else if selector == 33 {
        combine_three_arguments(first_argument, second_argument, 34)
    } else if selector == 34 {
        combine_three_arguments(first_argument, second_argument, 35)
    } else if selector == 35 {
        combine_three_arguments(first_argument, second_argument, 36)
    } else if selector == 36 {
        combine_three_arguments(first_argument, second_argument, 37)
    } else if selector == 37 {
        combine_three_arguments(first_argument, second_argument, 38)
    } else if selector == 38 {
        combine_three_arguments(first_argument, second_argument, 39)
    } else if selector == 39 {
        combine_three_arguments(first_argument, second_argument, 40)
    } else if selector == 40 {
        combine_three_arguments(first_argument, second_argument, 41)
    } else if selector == 41 {
        combine_three_arguments(first_argument, second_argument, 42)
    } else if selector == 42 {
        combine_three_arguments(first_argument, second_argument, 43)
    } else if selector == 43 {
        combine_three_arguments(first_argument, second_argument, 44)
    } else if selector == 44 {
        combine_three_arguments(first_argument, second_argument, 45)
    } else if selector == 45 {
        combine_three_arguments(first_argument, second_argument, 46)
    } else {
        0
    }
}

#[verify::test]
pub fn test_deep_chain() {
    assert!(deep_chain(0, 10, 20) == 53);
    assert!(deep_chain(1, 10, 20) == 56);
    assert!(deep_chain(30, 10, 20) == 143);
    assert!(deep_chain(40, 10, 20) == 173);
    assert!(deep_chain(45, 10, 20) == 188);
    assert!(deep_chain(46, 10, 20) == 0);
}
