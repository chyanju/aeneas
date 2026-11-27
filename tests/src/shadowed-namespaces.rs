//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]
//! Local variables which have the name of a module. In Lean, `term.make` is
//! the field `make` of the variable `term` if there is such a variable in
//! scope: a variable gets a fresh name when we print, in its scope, a
//! qualified name whose first component is the name of the variable.

pub mod term {
    pub struct Term {
        pub id: u32,
    }

    pub fn make(id: u32) -> Term {
        Term { id }
    }
}

pub mod cs {
    pub struct ConstraintSystem {
        pub n: u32,
    }

    pub fn make(n: u32) -> ConstraintSystem {
        ConstraintSystem { n }
    }

    pub fn size(c: &ConstraintSystem) -> u32 {
        c.n
    }
}

/// The parameter `term` is in scope in the type of the parameter `t`.
pub fn param(term: u32, t: term::Term) -> u32 {
    term + t.id
}

/// The parameter `term` is in scope in the return type.
pub fn return_type(term: u32) -> term::Term {
    term::Term { id: term }
}

/// The variable `term` is in scope in the call which follows its definition.
pub fn local(x: u32) -> u32 {
    let term = x + 1;
    term::make(term).id
}

/// The variable of a branch of a match.
pub fn in_match(o: Option<u32>) -> u32 {
    match o {
        Some(term) => term::make(term).id,
        None => 0,
    }
}

/// A value without a name in Rust gets the name of its type: `cs` for a
/// `ConstraintSystem`.
pub fn temporary(n: u32) -> u32 {
    cs::size(&cs::make(n))
}

/// The same in a loop, whose function receives the constraint system.
pub fn in_loop(c: &cs::ConstraintSystem, k: u32) -> u32 {
    let mut i = 0;
    let mut s = 0;
    while i < k {
        s += cs::size(c);
        i += 1;
    }
    s
}

/// The parameter `term` is not in scope in its own type, and we print no
/// qualified name in its scope: it keeps its name.
pub fn keeps_name_param(term: term::Term) -> u32 {
    term.id
}

/// The variable `term` is not in scope in the expression that it is bound to:
/// it keeps its name.
pub fn keeps_name_let(x: u32) -> u32 {
    let term = term::make(x);
    term.id
}

#[verify::test]
pub fn test_shadowed_namespaces() {
    assert!(param(1, term::make(2)) == 3);
    assert!(return_type(4).id == 4);
    assert!(local(5) == 6);
    assert!(in_match(Some(7)) == 7);
    assert!(in_match(None) == 0);
    assert!(temporary(8) == 8);
    assert!(in_loop(&cs::make(3), 4) == 12);
    assert!(keeps_name_param(term::make(9)) == 9);
    assert!(keeps_name_let(10) == 10);
}
