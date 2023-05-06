//! A basic parser module.
//!
//! # Examples
//!
//! ```
//! # use fwm_base::parser::{Parser, ParserError, Expression, ExpressionArgument};
//! let file: &[u8] = &[
//!     0x10, 0x00,
//!     0x20, 0x00, 0xc2, 0x10, 0x10, 0x10, 0x10,
//! ];
//! let exprs: Result<Vec<Expression>, ParserError> = Parser::new(&file)
//!     .into_iter() // -> ParserIter
//!     .collect();
//!
//! assert_eq!(exprs.unwrap(), &[
//!     Expression { opcode: 0x1000, args: vec![], },
//!     Expression { opcode: 0x2000, args: vec![ExpressionArgument::DWord(0xc2, 0x10101010)], }
//! ]);
//! ```

use core::fmt;
use alloc::vec::Vec;

/// Expression argument.
///
/// See module-level documentation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExpressionArgument {
    Single(u8),
    Double(u8, u8),
    Word(u8, u16),
    DWord(u8, u32),
}
/// Full expression.
///
/// See module-level documentation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Expression {
    pub opcode: u16,
    pub args: Vec<ExpressionArgument>,
}

/// Basic Parser. Can be tuned into iterator using [`Parser::into_iter`].
pub struct Parser<'a> {
    buffer: &'a [u8],
    offset: usize,
}

impl<'a> Parser<'a> {
    pub fn new(buffer: &'a [u8]) -> Self {
        Self { buffer, offset: 0 }
    }
    fn next_arg(&mut self) -> Result<ExpressionArgument, ParserError> {
        let Some(kind) = self.buffer.get(self.offset).copied() else {
            return Err(ParserError {
                kind: ParserErrorKind::InvalidOpcodeKind,
                start: self.offset,
                offset: self.offset,
            });
        };
        self.offset += 1;
        match kind {
            0x00..=0x5f => Ok(ExpressionArgument::Single(kind)),
            0x60..=0xbf | 0xc0 => {
                let Some(ext) = self.buffer.get(self.offset).copied() else {
                    return Err(ParserError {
                        kind: ParserErrorKind::InvalidArgumentLength { expected: 2 },
                        start: self.offset - 1,
                        offset: self.offset,
                    });
                };
                self.offset += 1;

                Ok(ExpressionArgument::Double(kind, ext))
            }
            0xc1 => {
                let Some(ext) = self.buffer.get(self.offset..self.offset + 2).map(|v| (v[0] as u16) << 8 | (v[1] as u16)) else {
                    return Err(ParserError {
                        kind: ParserErrorKind::InvalidArgumentLength { expected: 3 },
                        start: self.offset - 1,
                        offset: self.offset,
                    });
                };
                self.offset += 2;

                Ok(ExpressionArgument::Word(kind, ext))
            }
            0xc2 => {
                let Some(ext) = self.buffer.get(self.offset..self.offset + 4).map(|v| (v[0] as u32) << 24 | (v[1] as u32) << 16 | (v[2] as u32) << 8 | (v[3] as u32)) else {
                    return Err(ParserError {
                        kind: ParserErrorKind::InvalidArgumentLength { expected: 5 },
                        start: self.offset - 1,
                        offset: self.offset,
                    });
                };
                self.offset += 4;

                Ok(ExpressionArgument::DWord(kind, ext))
            }

            _ => Err(ParserError {
                kind: ParserErrorKind::InvalidArgumentKind,
                start: self.offset,
                offset: self.offset,
            }),
        }
    }
    /// Parses and return next [`Expression`]. If there no more expressions will return
    /// [`ParserErrorKind::EOF`].
    pub fn next_expr(&mut self) -> Result<Expression, ParserError> {
        let start = self.offset;

        if start == self.buffer.len() {
            return Err(ParserError {
                kind: ParserErrorKind::EOF,
                start,
                offset: self.offset,
            });
        }

        let opcode = self.buffer.get(start..start + 2).map(|v| (v[0], v[1]));
        let Some((kind, no)) = opcode else {
            return Err(ParserError {
                kind: ParserErrorKind::InvalidOpcode,
                start,
                offset: self.offset,
            });
        };

        self.offset += 2;
        let opcode = (kind as u16) << 8 | no as u16;

        if matches!(kind, 0x00..=0x1f | 0x80..=0x9f) {
            return Ok(Expression {
                opcode,
                args: Vec::new(),
            });
        }
        let argc = kind % 0x80 / 0x20;
        let args: Result<Vec<ExpressionArgument>, ParserError> =
            (0..argc).map(|_| self.next_arg()).collect();

        Ok(Expression {
            opcode,
            args: args?,
        })
    }
}

impl<'a> IntoIterator for Parser<'a> {
    type IntoIter = ParserIter<'a>;
    type Item = <Self::IntoIter as Iterator>::Item;

    fn into_iter(self) -> Self::IntoIter {
        ParserIter(self)
    }
}

/// Iterator wrapper over [`Parser`].
pub struct ParserIter<'a>(Parser<'a>);

impl<'a> ParserIter<'a> {
    pub fn new(parser: Parser<'a>) -> Self {
        Self(parser)
    }
    pub fn parser(self) -> Parser<'a> {
        self.0
    }
}

impl<'a> Iterator for ParserIter<'a> {
    type Item = Result<Expression, ParserError>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.0.next_expr() {
            Err(ParserError {
                kind: ParserErrorKind::EOF,
                ..
            }) => None,
            v => Some(v),
        }
    }
}

/// Represents error that may occurs while parsing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParserError {
    kind: ParserErrorKind,
    start: usize,
    offset: usize,
}

#[cfg(not(feature = "no-std"))]
impl std::error::Error for ParserError {}

impl fmt::Display for ParserError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} @ {}..{}", self.kind, self.start, self.offset)
    }
}

/// Represents a error kind that may occur while parsing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ParserErrorKind {
    /// Unexpected end of file
    EOF,
    /// Invalid opcode bytes
    InvalidOpcode,
    /// Invalid arguments count
    InvalidOpcodeKind,
    /// Invalid argument length
    InvalidArgumentLength { expected: u8 },
    /// Invalid argument kind bytes
    InvalidArgumentKind,
}

impl fmt::Display for ParserErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParserErrorKind::EOF => write!(f, "end of file"),
            ParserErrorKind::InvalidOpcode => write!(f, "invalid opcode bytes"),
            ParserErrorKind::InvalidOpcodeKind => write!(f, "not enought arguments"),
            ParserErrorKind::InvalidArgumentLength { expected } => {
                write!(f, "invalid argument length, expected {expected} bytes")
            }
            ParserErrorKind::InvalidArgumentKind => write!(f, "invalid argument kind byte"),
        }
    }
}

#[cfg(test)]
#[rustfmt::skip]
mod tests {
    use alloc::vec;
    use super::*;

    #[test]
    fn normal_parsing() {
        let buffer: &[u8] = &[
            0x00, 0x10, // no arguments
            0x20, 0x99, 0x19, // 1 argument
            0x5f, 0x00, 0x00, 0x8a, 0x10, // 2 arguments, (reg, reg_with_offset)
            0xe1, 0x00, 0x00, 0x00, 0x00, // 3 user arguments, (reg, reg, reg)
            0x35, 0x00, 0xc1, 0x10, 0x00, // 1 argument, (u16)
            0x3a, 0x00, 0xc2, 0x10, 0x10,
                              0x10, 0x10, // 1 argument, (u32)
        ];
        let expected: &[_] = &[
            Expression { opcode: 0x0010, args: vec![] },
            Expression { opcode: 0x2099, args: vec![ExpressionArgument::Single(0x19)] },
            Expression { opcode: 0x5f00, args: vec![ExpressionArgument::Single(0x00), ExpressionArgument::Double(0x8a, 0x10)] },
            Expression { opcode: 0xe100, args: vec![ExpressionArgument::Single(0x00),ExpressionArgument::Single(0x00),ExpressionArgument::Single(0x00),] },
            Expression { opcode: 0x3500, args: vec![ExpressionArgument::Word(0xc1, 0x1000)] },
            Expression { opcode: 0x3a00, args: vec![ExpressionArgument::DWord(0xc2, 0x10101010)] },
        ];
        let actual: Result<Vec<_>, _> = Parser::new(buffer).into_iter().collect();

        let actual = actual.unwrap();
        assert_eq!(expected, actual);
    }

    #[test]
    fn invalid_opcode() {
        let buffer: &[u8] = &[
            0x20, // passed only kind without number
        ];
        let res = Parser::new(buffer).next_expr();

        assert_eq!(res, Err(ParserError { kind: ParserErrorKind::InvalidOpcode, start: 0, offset: 0 }));
    }

    #[test]
    fn invalid_opcode_kind() {
        let buffer: &[u8] = &[
            0x20, 0x00, // opcode required 1 arguments, but 0 given
        ];
        let res = Parser::new(buffer).next_expr();

        assert_eq!(res, Err(ParserError { kind: ParserErrorKind::InvalidOpcodeKind, start: 2, offset: 2 }));
    }

    #[test]
    fn invalid_argument() {
        // (expected, start, offset, buffer)
        let buffers: Vec<(u8, usize, usize, &[u8])> = vec![
            // addr:
            (2, 2, 3, &[0x20, 0x00, 0x65]),
            // u16:
            (3, 2, 3, &[0x20, 0x00, 0xc1]),
            (3, 2, 3, &[0x20, 0x00, 0xc1, 0x10]),
            // u32:
            (5, 2, 3, &[0x20, 0x00, 0xc2, 0x10, 0x10]),
            (5, 2, 3, &[0x20, 0x00, 0xc2, 0x10, 0x10, 0x10]),
            // second:
            (2, 3, 4, &[0x40, 0x00, 0x00, 0x65]),
            (3, 3, 4, &[0x40, 0x00, 0x00, 0xc1, 0x10]),
        ];

        for (idx, (expected, start, offset, buffer)) in buffers.into_iter().enumerate() {
            let res = Parser::new(buffer).next_expr();

            assert_eq!(
                res,
                Err(ParserError { kind: ParserErrorKind::InvalidArgumentLength { expected }, start, offset }),
                "Testing line #{idx}: {buffer:?}"
            );
        }
    }

    #[test]
    fn invalid_argument_kind() {
        let buffer: &[u8] = &[
            0x20, 0x00, 0xff, // reserved
        ];
        let res = Parser::new(buffer).next_expr();

        assert_eq!(res, Err(ParserError { kind: ParserErrorKind::InvalidArgumentKind, start: 3, offset: 3 }));
    }
}
