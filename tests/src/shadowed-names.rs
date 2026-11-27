//@ [!lean] skip
//@ [lean] subdir=ShadowedNames
#![feature(register_tool)]
#![register_tool(verify)]
//! Names which, in Lean, resolve to another declaration than the one we print
//! them for: a field of a structure is in scope in the types of the fields
//! which follow it; a declaration being defined is in scope in its body under
//! its short name; and in the declaration [def A.f], the name [x] is [A.x] if
//! there is such a declaration. We then print these names from the root
//! namespace. The theorems of `Properties.lean` state that the declarations have
//! the intended meaning.

pub mod term {
    pub struct Term {
        pub id: u32,
    }

    pub fn make(id: u32) -> Term {
        Term { id }
    }
}

/// The field `term` is in scope in the type of the field `t`.
pub struct Pending {
    pub term: u32,
    pub t: term::Term,
}

pub fn pending_sum(p: &Pending) -> u32 {
    p.term + p.t.id
}

/// The method `term` is in scope in the type of the method `make`.
pub trait Source {
    fn term(&self) -> u32;
    fn make(&self) -> term::Term;
}

pub struct Num {
    pub x: u32,
}

impl Source for Num {
    fn term(&self) -> u32 {
        self.x
    }

    fn make(&self) -> term::Term {
        term::make(self.x)
    }
}

/// In the methods of `Check`, `ok` is the field `Check.ok`.
pub struct Check {
    pub ok: bool,
}

impl Check {
    pub fn passed(&self) -> bool {
        self.ok
    }
}

/// The same body outside the namespace of `Check`.
pub fn passed(c: &Check) -> bool {
    c.ok
}

/// In the methods of `Value` and of its implementation of `PartialEq`, `Bool`
/// is the variant `Value.Bool`.
#[derive(PartialEq)]
pub enum Value {
    Bool(bool),
    Int(u32),
}

impl Value {
    pub fn is_int(&self) -> bool {
        matches!(self, Value::Int(_))
    }
}

/// The same with variants without fields.
#[derive(PartialEq, Clone, Copy)]
pub enum Kind {
    Bool,
    Int,
}

pub fn same_kind(a: Kind, b: Kind) -> bool {
    a == b
}

/// Types named like types of the library: in their declarations, `Bool` and
/// `Char` are the types being defined; in the declarations of the module, they
/// are the types of the module.
pub mod m {
    pub struct Bool {
        pub b: bool,
    }

    pub enum Char {
        A(char),
        B,
    }

    pub fn flip(x: &Bool) -> bool {
        !x.b
    }

    pub fn letter(c: &Char) -> char {
        match c {
            Char::A(c) => *c,
            Char::B => 'b',
        }
    }
}

pub struct Flag {
    pub flag: bool,
}

/// A free function `make`, called from the method `Flag::make`.
pub fn make(x: bool) -> Flag {
    Flag { flag: x }
}

impl Flag {
    /// Before the method `ok`: `ok` is not yet the method `Flag.ok`.
    pub fn before(&self) -> u32 {
        1
    }

    /// In its body, `ok` is the method being defined.
    pub fn ok(&self) -> bool {
        self.flag
    }

    /// After the method `ok`: `ok` is the method `Flag.ok`.
    pub fn after(&self) -> u32 {
        2
    }

    /// In its body, `make` is the method being defined.
    pub fn make(x: bool) -> Flag {
        make(x)
    }
}

pub struct Opt {
    pub v: u32,
}

impl Opt {
    pub fn some(&self) -> bool {
        self.v > 0
    }

    /// In the pattern, `some` is the method `Opt.some`.
    pub fn get_or_zero(o: Option<u32>) -> u32 {
        match o {
            Some(x) => x,
            None => 0,
        }
    }

    /// `some` is the method `Opt.some`.
    pub fn first(&self) -> Option<u32> {
        if self.v > 0 {
            Some(self.v)
        } else {
            None
        }
    }
}

#[verify::test]
pub fn test_shadowed_names() {
    let p = Pending {
        term: 1,
        t: term::make(2),
    };
    assert!(pending_sum(&p) == 3);
    let n = Num { x: 4 };
    assert!(n.term() == 4);
    assert!(n.make().id == 4);
    let c = Check { ok: true };
    assert!(c.passed());
    assert!(passed(&c));
    assert!(Value::Int(1).is_int());
    assert!(!Value::Bool(true).is_int());
    assert!(Value::Bool(true) == Value::Bool(true));
    assert!(!(Value::Bool(true) == Value::Int(1)));
    assert!(same_kind(Kind::Bool, Kind::Bool));
    assert!(!same_kind(Kind::Bool, Kind::Int));
    assert!(m::flip(&m::Bool { b: false }));
    assert!(m::letter(&m::Char::A('a')) == 'a');
    assert!(m::letter(&m::Char::B) == 'b');
    let f = Flag::make(true);
    assert!(f.ok());
    assert!(f.before() == 1);
    assert!(f.after() == 2);
    let o = Opt { v: 3 };
    assert!(o.some());
    assert!(matches!(o.first(), Some(3)));
    assert!(Opt { v: 0 }.first().is_none());
    assert!(Opt::get_or_zero(Some(5)) == 5);
    assert!(Opt::get_or_zero(None) == 0);
}
