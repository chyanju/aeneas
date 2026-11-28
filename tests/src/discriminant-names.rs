//@ [!lean] skip
//@ [lean] subdir=DiscriminantNames
#![feature(register_tool)]
#![register_tool(verify)]
//! An enumeration with the name of an enumeration of `discriminant.rs`. The Lean library
//! generates an instance of `Discriminant` for each; the instances are named after the full
//! names of the types, so the two translations can be imported together
//! (`DiscriminantNames/Properties.lean`).

#[derive(PartialEq)]
pub enum AlertLevel {
    Notice,
    Warning,
    Fatal,
}

pub fn is_fatal(l: &AlertLevel) -> bool {
    *l == AlertLevel::Fatal
}

#[verify::test]
pub fn test_is_fatal() {
    assert!(is_fatal(&AlertLevel::Fatal));
    assert!(!is_fatal(&AlertLevel::Warning));
    assert!(!is_fatal(&AlertLevel::Notice));
}

#[cfg(test)]
mod tests {
    #[test]
    fn discriminant_names() {
        super::test_is_fatal();
    }
}
