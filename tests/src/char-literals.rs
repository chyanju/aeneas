//@ [!lean] skip
//@ [lean] subdir=CharLiterals
//! Character literals. In the generated code the quote, the backslash and the
//! characters above 127 are escaped, and the other characters are printed as
//! they are (the control characters too). The theorems of `Properties.lean`
//! state that every literal is the character with the expected code.

pub fn tab() -> char {
    '\t'
}

pub fn line_feed() -> char {
    '\n'
}

pub fn carriage_return() -> char {
    '\r'
}

pub fn backslash() -> char {
    '\\'
}

pub fn quote() -> char {
    '\''
}

pub fn double_quote() -> char {
    '"'
}

pub fn e_acute() -> char {
    '\u{e9}'
}

pub fn y_diaeresis() -> char {
    '\u{ff}'
}

pub fn space() -> char {
    ' '
}

pub fn tilde() -> char {
    '~'
}

pub fn letter() -> char {
    'a'
}

pub fn is_blank(c: char) -> bool {
    c == ' ' || c == '\t' || c == '\n' || c == '\r'
}

pub fn is_quote_or_backslash(c: char) -> bool {
    c == '\'' || c == '\\'
}
