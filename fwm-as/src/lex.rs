use core::fmt;

/// Represents a token.
/// See [`Lex`] for more info.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Token<'a> {
    /// Comment. Example: `# foo`
    Comment(&'a str),
    /// Opcode define statement. Example: `.op`
    DefOpcode,
    /// Register define statement. Example: `.reg`
    DefRegister,
    /// Any ident. Example: `foo_bar`, `mov`
    Ident(&'a str),
    /// Any register. Example: `%foo_bar`
    Register(&'a str),
    /// Any number. Example: `$10h`, `-1`, `-FFh`
    Number(u64),
    /// String. Example: `"foo"`
    String(&'a str),
    /// `[`
    LeftBracket,
    /// `]`
    RightBracket,
    /// `;`
    Semilicon,
    /// `,`
    Comma,
    /// `@`
    At,
}

/// fwm-as lexer.
/// Represents an iterator over [`Token`]s.
///
/// # Example
/// ```
/// # use fwm_as::lex::{Lex, Token, Error};
/// #
/// let fragment = "mov %foo, $10h";
/// let tokens: Result<Vec<Token>, Error> = Lex::new(fragment).collect();
///
/// assert_eq!(tokens, Ok(vec![Token::Ident("mov"), Token::Register("foo"), Token::Comma, Token::Number(16)]));
/// ```
pub struct Lex<'a> {
    v: &'a str,
    pos: usize,
}

impl<'a> Lex<'a> {
    /// Create new lexer by string.
    pub fn new(v: &'a str) -> Self {
        Self { v, pos: 0 }
    }
}
impl<'a> Iterator for Lex<'a> {
    type Item = Result<Token<'a>, Error>;

    fn next(&mut self) -> Option<Self::Item> {
        let step: usize = self.v[self.pos..]
            .chars()
            .take_while(|c| *c == ' ' || *c == '\t' || *c == '\n' || *c == '\r')
            .map(char::len_utf8)
            .sum();
        self.pos += step;

        let c = self.v[self.pos..].chars().next().map(|v| {
            self.pos += v.len_utf8();
            v
        });

        match c? {
            '[' => Some(Ok(Token::LeftBracket)),
            ']' => Some(Ok(Token::RightBracket)),
            ';' => Some(Ok(Token::Semilicon)),
            ',' => Some(Ok(Token::Comma)),
            '@' => Some(Ok(Token::At)),

            '%' => {
                let len: usize = self.v[self.pos..]
                    .chars()
                    .take_while(|c| matches!(c, 'a'..='z' | 'A'..='Z' | '0'..='9' | '_' | ':'))
                    .map(char::len_utf8)
                    .sum();
                self.pos += len;

                Some(Ok(Token::Register(&self.v[self.pos - len..self.pos])))
            }

            '"' => {
                let Some(len) = self.v[self.pos..].find('"') else {
                    return Some(Err(Error {
                        start: self.pos - 1,
                        end: self.v.len(),
                        kind: ErrorKind::UnterminatedString,
                    }));
                };
                self.pos += len + 1;

                Some(Ok(Token::String(&self.v[self.pos - len - 1..self.pos - 1])))
            }

            c @ ('-' | '$' | '0'..='9') => {
                let (s, len) = {
                    let len: usize = self.v[self.pos..]
                        .chars()
                        .take_while(|c| matches!(c, '_' | 'a'..='f' | 'A'..='F' | '0'..='9'))
                        .map(char::len_utf8)
                        .sum();

                    let s = &self.v[self.pos..self.pos + len];
                    self.pos += len;

                    (s, len)
                };
                let base = if let Some('h' | 'H') = self.v[self.pos..].chars().next() {
                    self.pos += 1;
                    16
                } else if s.find(|c| matches!(c, 'a'..='f' | 'A'..='F')).is_some() {
                    return Some(Err(Error {
                        start: self.pos - 1 - len,
                        end: self.pos,
                        kind: ErrorKind::InvalidDecimalNumber,
                    }));
                } else {
                    10
                };
                let def = match c {
                    '0'..='9' => u64::from(c) - u64::from('0'),
                    _ => 0,
                };
                let num = s
                    .chars()
                    .filter(|c| *c != '_')
                    .map(|v| match v {
                        c @ '0'..='9' => u64::from(c) - u64::from('0'),
                        c @ 'a'..='f' => u64::from(c) - u64::from('a') + 10,
                        c @ 'A'..='F' => u64::from(c) - u64::from('A') + 10,
                        _ => unreachable!(),
                    })
                    .fold(def, |acc, r| acc * base + r);
                if c == '-' {
                    Some(Ok(Token::Number(!0u64 - num + 1)))
                } else {
                    Some(Ok(Token::Number(num)))
                }
            }

            '.' => {
                let s = &self.v[self.pos..];
                if s.starts_with("op ") {
                    self.pos += "op ".len();
                    Some(Ok(Token::DefOpcode))
                } else if s.starts_with("reg ") {
                    self.pos += "reg ".len();
                    Some(Ok(Token::DefRegister))
                } else {
                    let len: usize = s
                        .chars()
                        .take_while(|c| matches!(c, 'a'..='z' | 'A'..='Z' | '0'..='9' | '_' | ':'))
                        .map(char::len_utf8)
                        .sum();

                    Some(Err(Error {
                        start: self.pos - 1,
                        end: self.pos + len,
                        kind: ErrorKind::InvalidDefineStatement,
                    }))
                }
            }

            'a'..='z' | 'A'..='Z' | '_' | ':' => {
                let s = {
                    let len: usize = self.v[self.pos..]
                        .chars()
                        .take_while(|c| matches!(c, 'a'..='z' | 'A'..='Z' | '0'..='9' | '_' | ':'))
                        .map(char::len_utf8)
                        .sum();
                    self.pos += len;

                    &self.v[self.pos - len - 1..self.pos]
                };

                Some(Ok(Token::Ident(s)))
            }

            '#' => {
                let s = {
                    let len: usize = self.v[self.pos..]
                        .chars()
                        .take_while(|c| *c != '\n')
                        .map(char::len_utf8)
                        .sum();
                    self.pos += len;

                    &self.v[self.pos - len - 1..self.pos]
                };

                Some(Ok(Token::Comment(s)))
            }

            _ => Some(Err(Error {
                start: self.pos - 1,
                end: self.pos,
                kind: ErrorKind::UnexpectedToken,
            })),
        }
    }
}

/// Represents a lexer error.
///
/// # Example
/// ```
/// # use fwm_as::lex::{Lex, Error, ErrorKind};
/// #
/// let fragment = "mov %foo= $10";
/// //                      ^ invalid token
/// let result: Result<Vec<_>, _> = Lex::new(fragment).collect();
///
/// assert_eq!(result, Err(Error { start: 8, end: 9, kind: ErrorKind::UnexpectedToken }));
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Error {
    pub start: usize,
    pub end: usize,
    pub kind: ErrorKind,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.kind.fmt(f)?;
        write!(f, " at {}..{}", self.start, self.end)
    }
}
#[cfg(not(feature = "no-std"))]
impl std::error::Error for Error {}

/// Represents a kind of lexer error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ErrorKind {
    /// Unexpected token
    UnexpectedToken,
    /// Invalid define statement (ex. `.foo`)
    InvalidDefineStatement,
    /// Invalid litters in decimal number
    InvalidDecimalNumber,
    /// Unterminated double quote string
    UnterminatedString,
}

impl fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnexpectedToken => write!(f, "unexpected token"),
            Self::InvalidDefineStatement => write!(f, "invalid define statement"),
            Self::InvalidDecimalNumber => write!(f, "invalid litters in decimal number"),
            Self::UnterminatedString => write!(f, "unterminated double quote string"),
        }
    }
}

#[cfg(test)]
mod tests {
    use alloc::vec::Vec;
    use super::*;

    #[test]
    fn normal_fragment() {
        let fragment = "
            # Comment.
            .op mov 400ah
            .op xor 123
            .reg    r0, $13
            .reg    fa1 9
            xor %fa1, %fa1
            mov %r0,  [8; $FFh]

            \nident_foo\nident_bar\t$10 \"string\"
            ";
        let expected = [
            Token::Comment("# Comment."),
            Token::DefOpcode,
            Token::Ident("mov"),
            Token::Number(0x400a),
            Token::DefOpcode,
            Token::Ident("xor"),
            Token::Number(123),
            Token::DefRegister,
            Token::Ident("r0"),
            Token::Comma,
            Token::Number(13),
            Token::DefRegister,
            Token::Ident("fa1"),
            Token::Number(9),
            Token::Ident("xor"),
            Token::Register("fa1"),
            Token::Comma,
            Token::Register("fa1"),
            Token::Ident("mov"),
            Token::Register("r0"),
            Token::Comma,
            Token::LeftBracket,
            Token::Number(8),
            Token::Semilicon,
            Token::Number(0xff),
            Token::RightBracket,
            Token::Ident("ident_foo"),
            Token::Ident("ident_bar"),
            Token::Number(10),
            Token::String("string"),
        ];

        let actual = {
            let actual: Result<Vec<_>, _> = Lex::new(fragment).collect();

            match actual {
                Ok(v) => v,
                Err(e) => panic!("got error while parsing: {e}"),
            }
        };

        assert_eq!(&actual, &expected);
    }

    #[test]
    fn erroneous_fragments() {
        #[rustfmt::skip]
        let fragments = [
            ("! mov $1, $1",        0,  1,  ErrorKind::UnexpectedToken),
            ("foo bar! $10",        7,  8,  ErrorKind::UnexpectedToken),
            ("foobar ! $10",        7,  8,  ErrorKind::UnexpectedToken),
            ("foo\nbar\nbaz=\n$10", 11, 12, ErrorKind::UnexpectedToken),

            (" .opcode", 1, 8, ErrorKind::InvalidDefineStatement),
            (" .regs",   1, 6, ErrorKind::InvalidDefineStatement),
            (".opcode",  0, 7, ErrorKind::InvalidDefineStatement),
            (". foo",    0, 1, ErrorKind::InvalidDefineStatement),

            ("1a",    0, 2, ErrorKind::InvalidDecimalNumber),
            ("$FF",   0, 3, ErrorKind::InvalidDecimalNumber),
            ("$a123", 0, 5, ErrorKind::InvalidDecimalNumber),
            ("$123a", 0, 5, ErrorKind::InvalidDecimalNumber),

            ("\"hello", 0, 6, ErrorKind::UnterminatedString),
        ];

        for (fragment, start, end, kind) in fragments {
            let actual: Result<Vec<_>, _> = Lex::new(fragment).collect();

            assert_eq!(
                actual,
                Err(Error { start, end, kind }),
                "fragment: `{fragment}`"
            );
        }
    }
}
