use core::{fmt, slice};
use alloc::vec::Vec;

use crate::lex::Token;

/// Argument of opcode.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OPCodeArgument<'a> {
    Register(&'a str),
    Address(&'a str, i64),
    Number(u64),
    LabelPtr(&'a str),
    Raw(u64, u64),
}

/// Syntax tree (line) item. Unit of [`SyntaxTree`].
///
/// *Note*: due to some rust's jokes use [`SyntaxItem::is_opcode`], [`SyntaxItem::opcode_name`] and
/// [`SyntaxItem::opcode_args`] for opcode items.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SyntaxItem<'a> {
    /// Syntax label. Defines using [`Token::At`]:
    ///
    /// ```text
    /// @label foo %bar
    ///        mov %bar, 42
    /// ```
    Label(&'a str),
    /// OPCode defineation, from [`Token::DefOpcode`]:
    ///
    /// ```text
    /// .op opname 4001h
    /// ```
    OPCodeDef(&'a str, u16),
    /// Register defineation, from [`Token::DefRegister`]:
    ///
    /// ```text
    /// .reg foo 12
    /// # Possible values are 0..=255
    /// # Also .reg uses mod by 0x30, so 31h (0x31) is just 1.
    /// ```
    RegisterDef(&'a str, u8),
    /// OPCode without arguments. See [`SyntaxItem`] docs for more
    ///
    /// ```text
    /// ret
    /// ```
    OPCode0(&'a str),
    /// OPCode with 1 argument. See [`SyntaxItem`] docs for more
    ///
    /// ```text
    /// push %foo
    /// ```
    OPCode1(&'a str, OPCodeArgument<'a>),
    /// OPCode with 2 arguments. See [`SyntaxItem`] docs for more
    ///
    /// ```text
    /// mov %r4, $14h
    /// ```
    OPCode2(&'a str, [OPCodeArgument<'a>; 2]),
    /// OPCode with 3 arguments. See [`SyntaxItem`] docs for more
    ///
    /// ```text
    /// # %a = %b + %c
    /// __summov64 %a, %b, %c
    /// ```
    OPCode3(&'a str, [OPCodeArgument<'a>; 3]),
    /// Raw data just pushed to output.
    ///
    /// ```text
    /// @[1; 4001h]    @[1; 10h] @[2; $C0FFh] # register(4001h) opcode(10h) $FFh
    /// # it like 0-argument opcode, so if it defines
    /// # as opcode it requires arguments added also as raw items
    /// ```
    Raw(u64, u64),
}

impl<'a> SyntaxItem<'a> {
    /// Checks if this item is opcode.
    ///
    /// ```
    /// # use fwm_as::tree::SyntaxItem;
    /// #
    /// assert!(SyntaxItem::OPCode0("ret").is_opcode());
    /// assert!(!SyntaxItem::Raw(0, 0).is_opcode());
    /// ```
    pub fn is_opcode(&self) -> bool {
        matches!(
            self,
            Self::OPCode0(_) | Self::OPCode1(_, _) | Self::OPCode2(_, _) | Self::OPCode3(_, _)
        )
    }
    /// Gets opcode name. Panics if item is not opcode
    ///
    /// ```
    /// # use fwm_as::tree::SyntaxItem;
    /// #
    /// assert_eq!(SyntaxItem::OPCode0("ret").opcode_name(), "ret");
    /// ```
    ///
    /// ```should_panic
    /// # use fwm_as::tree::SyntaxItem;
    /// #
    /// // panics:
    /// assert_eq!(SyntaxItem::Label("foo").opcode_name(), "ret");
    /// ```
    pub fn opcode_name(&self) -> &'a str {
        match self {
            Self::OPCode0(s) | Self::OPCode1(s, _) | Self::OPCode2(s, _) | Self::OPCode3(s, _) => s,
            _ => panic!("trying to get opcode_name on non-opcode value"),
        }
    }
    /// Gets opcode args. Panics if item is not opcode
    ///
    /// ```
    /// # use fwm_as::tree::{SyntaxItem, OPCodeArgument};
    /// #
    /// assert_eq!(SyntaxItem::OPCode0("ret").opcode_args(), &[]);
    /// assert_eq!(SyntaxItem::OPCode1("push", OPCodeArgument::LabelPtr("foo")).opcode_args().len(), 1);
    /// ```
    ///
    /// ```should_panic
    /// # use fwm_as::tree::SyntaxItem;
    /// #
    /// // panics:
    /// let _ = SyntaxItem::Label("foo").opcode_args();
    /// ```
    pub fn opcode_args(&self) -> &[OPCodeArgument<'a>] {
        match self {
            Self::OPCode0(_) => &[],
            Self::OPCode1(_, v) => slice::from_ref(v),
            Self::OPCode2(_, a) => a,
            Self::OPCode3(_, a) => a,
            _ => panic!("trying to get opcode_args on non-opcode value"),
        }
    }
}

/// Syntax tree. Represents just a vector of [`SyntaxItem`]. Can be obtained from:
///
/// 1. [`SyntaxTree::new`]
pub struct SyntaxTree<'a>(pub Vec<SyntaxItem<'a>>);

impl<'a> SyntaxTree<'a> {
    /// Parses tokens from iterator.
    ///
    /// # Examples
    /// ```
    /// use fwm_as::{tree::{SyntaxTree, SyntaxItem, OPCodeArgument}, lex::Token};
    /// 
    /// let tokens = [
    ///     Token::DefRegister, Token::Ident("r0"), Token::Number(16),
    ///     Token::At, Token::Ident("label"),
    ///     Token::Ident("call"), Token::LeftBracket, Token::Register("r0"), Token::Semilicon,
    ///         Token::Number(0), Token::RightBracket,
    ///     Token::Ident("xor"), Token::Register("r0"), Token::Comma, Token::Register("r0"),
    ///     Token::Ident("jmp"), Token::LeftBracket, Token::Ident("label"), Token::RightBracket,
    /// ];
    ///
    /// let v = SyntaxTree::new(&tokens).map(|f| f.0);
    /// assert_eq!(v, Ok(vec![
    ///     SyntaxItem::RegisterDef("r0", 16),
    ///     SyntaxItem::Label("label"),
    ///     SyntaxItem::OPCode1("call", OPCodeArgument::Address("r0", 0)),
    ///     SyntaxItem::OPCode2("xor", [OPCodeArgument::Register("r0"),
    ///         OPCodeArgument::Register("r0")]),
    ///     SyntaxItem::OPCode1("jmp", OPCodeArgument::LabelPtr("label")),
    /// ]));
    /// ```
    ///
    /// ```
    /// # use fwm_as::{tree::{SyntaxTree, SyntaxError, SyntaxErrorKind}, lex::Token};
    /// # 
    /// let tokens = [ Token::DefRegister, Token::Ident("r0"), ];
    /// let v = SyntaxTree::new(&tokens).map(|f| f.0);
    ///
    /// assert_eq!(v, Err(SyntaxError { idx: 0, kind: SyntaxErrorKind::RegDefSyntax }))
    /// ```
    ///
    /// See also: [`SyntaxError`]
    pub fn new<'b, I>(iter: I) -> Result<Self, SyntaxError>
    where
        I: IntoIterator<Item = &'b Token<'a>>,
        'a: 'b,
    {
        let mut v = Vec::new();
        let mut iter = iter.into_iter().enumerate().peekable(); // or use DoubleEndedIterator?.. idk...

        loop {
            let Some((idx, token)) = iter.next() else { break; };

            match token {
                Token::Comment(_) => continue,
                Token::DefOpcode => {
                    let (Some((_, Token::Ident(opcode))), Some((_, Token::Number(id)))) = (iter.next(), iter.next()) else {
                        return Err(SyntaxError { idx, kind: SyntaxErrorKind::OPDefSyntax });
                    };
                    v.push(SyntaxItem::OPCodeDef(opcode, *id as u16));
                }
                Token::DefRegister => {
                    let (Some((_, Token::Ident(reg))), Some((_, Token::Number(id)))) = (iter.next(), iter.next()) else {
                        return Err(SyntaxError { idx, kind: SyntaxErrorKind::RegDefSyntax });
                    };
                    v.push(SyntaxItem::RegisterDef(reg, *id as u8));
                }

                Token::At => match iter.next() {
                    Some((_, Token::Ident(label))) => v.push(SyntaxItem::Label(label)),
                    Some((_, Token::LeftBracket)) => {
                        let (
                                Some((_, Token::Number(len))),
                                Some((_, Token::Semilicon)),
                                Some((_, Token::Number(val))),
                                Some((_, Token::RightBracket)),
                            ) = (iter.next(), iter.next(), iter.next(), iter.next()) else {
                                return Err(SyntaxError { idx, kind: SyntaxErrorKind::RawOPCode });
                            };
                        v.push(SyntaxItem::Raw(*len, *val))
                    }
                    _ => {
                        return Err(SyntaxError {
                            idx,
                            kind: SyntaxErrorKind::UnexpectedAt,
                        })
                    }
                },

                Token::Ident(ident) => 'brk: {
                    if !matches!(
                        iter.peek(),
                        Some(
                            (_, Token::Register(_))
                                | (_, Token::Number(_))
                                | (_, Token::LeftBracket)
                        )
                    ) {
                        v.push(SyntaxItem::OPCode0(ident));
                        break 'brk;
                    }

                    let mut args: [OPCodeArgument<'a>; 3] = [OPCodeArgument::Raw(0, 0); 3];
                    let mut arg_n = 0;
                    let mut push_arg = |arg| {
                        args[arg_n] = arg;
                        arg_n += 1;
                    };
                    // todo: fix `push_arg` kurwa

                    for _ in 0..3 {
                        match iter.next() {
                            Some((_, Token::Register(reg))) => {
                                push_arg(OPCodeArgument::Register(reg))
                            }
                            Some((_, Token::Number(num))) => push_arg(OPCodeArgument::Number(*num)),
                            Some((idx, Token::LeftBracket)) => {
                                let (Some(lhs), Some(mhs)) = (iter.next(), iter.next()) else {
                                    return Err(SyntaxError { idx, kind: SyntaxErrorKind::UnexpectedMeta });
                                };
                                match (lhs.1, mhs.1) {
                                    (Token::Number(len), Token::Semilicon) => {
                                        let (Some((_, Token::Number(val))), Some((_, Token::RightBracket))) = (iter.next(), iter.next()) else {
                                            return Err(SyntaxError { idx, kind: SyntaxErrorKind::RawArgument });
                                        };
                                        push_arg(OPCodeArgument::Raw(*len, *val))
                                    }
                                    (Token::Register(reg), Token::Semilicon) => {
                                        let (Some((_, Token::Number(off))), Some((_, Token::RightBracket))) = (iter.next(), iter.next()) else {
                                            return Err(SyntaxError { idx, kind: SyntaxErrorKind::AddressOffset });
                                        };
                                        push_arg(OPCodeArgument::Address(reg, *off as i64))
                                    }
                                    (Token::Ident(label), Token::RightBracket) => {
                                        push_arg(OPCodeArgument::LabelPtr(label))
                                    }
                                    _ => {
                                        return Err(SyntaxError {
                                            idx,
                                            kind: SyntaxErrorKind::UnknownArgument,
                                        })
                                    }
                                }
                            }
                            _ => {
                                return Err(SyntaxError {
                                    idx,
                                    kind: SyntaxErrorKind::UnknownToken,
                                });
                            }
                        }
                        if let Some((_, Token::Comma)) = iter.peek() {
                            iter.next();
                        } else {
                            break;
                        }
                    }

                    match arg_n {
                        1 => v.push(SyntaxItem::OPCode1(ident, args[0])),
                        2 => v.push(SyntaxItem::OPCode2(ident, [args[0], args[1]])),
                        3 => v.push(SyntaxItem::OPCode3(ident, args)),
                        _ => unreachable!(),
                    }
                }

                _ => {
                    return Err(SyntaxError {
                        idx,
                        kind: SyntaxErrorKind::UnknownToken,
                    })
                }
            }
        }

        Ok(Self(v))
    }
}

/// Syntax error
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SyntaxError {
    pub idx: usize,
    pub kind: SyntaxErrorKind,
}

#[cfg(not(feature = "no-std"))]
impl std::error::Error for SyntaxError {}
impl fmt::Display for SyntaxError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.kind.fmt(f)?;
        write!(f, " at position {}", self.idx)
    }
}

/// Kind of syntax error
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SyntaxErrorKind {
    /// Invalid `.op` syntax
    OPDefSyntax,
    /// Invalid `.reg` syntax
    RegDefSyntax,
    /// Invalid raw opcode escape
    RawOPCode,
    /// Unexpected [`Token::At`] (tokens after `@` does not match any variant)
    UnexpectedAt,
    /// Unexpected [`Token::LeftBracket`] in opcode arguments (tokens after `[`
    /// does not match any variant)
    UnexpectedMeta,
    /// Invalid raw argument (`[4; 12345678h]`) syntax
    RawArgument,
    /// Invalid address offset (`[%r0; 4]`) syntax
    AddressOffset,
    /// Unknown argument in opcode (tokens does not match any variant)
    UnknownArgument,
    /// Unknown token when expected opcode, label, etc...
    UnknownToken,
}

impl fmt::Display for SyntaxErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::OPDefSyntax => write!(f, "invalid `.op` syntax"),
            Self::RegDefSyntax => write!(f, "invalid `.reg` syntax"),
            Self::RawOPCode => write!(f, "invalid raw opcode escape"),
            Self::UnexpectedAt => write!(f, "unexpected `@`"),
            Self::UnexpectedMeta => write!(f, "unexpected `[`"),
            Self::RawArgument => write!(f, "invalid raw argument syntax"),
            Self::AddressOffset => write!(f, "invalid address offset syntax"),
            Self::UnknownArgument => write!(f, "invalid argument syntax"),
            Self::UnknownToken => write!(f, "unexpected token"),
        }
    }
}

#[cfg(test)]
mod tests {
    use alloc::vec;
    use super::*;

    #[test]
    fn normal_fragment() {
        #[rustfmt::skip]
        let fragment = [
            Token::Comment("Hello world!"),
            Token::DefRegister, Token::Ident("r0"), Token::Number(0x10),
            Token::DefOpcode, Token::Ident("mov"), Token::Number(0x4000),
            Token::At, Token::Ident("begin"),
            Token::Ident("mov"), Token::LeftBracket, Token::Register("r0"), Token::Semilicon, Token::Number(42), Token::RightBracket,
                Token::Comma, Token::Number(5), Token::Comma, Token::LeftBracket, Token::Ident("begin"), Token::RightBracket,
            Token::Ident("foo"),
            Token::Ident("bar"), Token::Number(1), Token::Comma, Token::Number(2),
            Token::At, Token::LeftBracket, Token::Number(1), Token::Semilicon, Token::Number(0x0F), Token::RightBracket,
        ];
        #[rustfmt::skip]
        let expected = vec![
            SyntaxItem::RegisterDef("r0", 0x10),
            SyntaxItem::OPCodeDef("mov", 0x4000),
            SyntaxItem::Label("begin"),
            SyntaxItem::OPCode3("mov", [OPCodeArgument::Address("r0", 42), OPCodeArgument::Number(5), OPCodeArgument::LabelPtr("begin")],),
            SyntaxItem::OPCode0("foo"),
            SyntaxItem::OPCode2("bar", [OPCodeArgument::Number(1), OPCodeArgument::Number(2)]),
            SyntaxItem::Raw(1, 0x0F),
        ];

        let actual = SyntaxTree::new(fragment.iter()).map(|f| f.0);

        assert_eq!(Ok(expected), actual);
    }

    #[test]
    fn erroneous_fragments() {
        #[rustfmt::skip]
        let tests = [
            (0, vec![Token::DefOpcode, Token::Number(1)],                           SyntaxErrorKind::OPDefSyntax),
            (0, vec![Token::DefOpcode],                                             SyntaxErrorKind::OPDefSyntax),
            (0, vec![Token::DefRegister, Token::Ident("foo"), Token::Ident("bar")], SyntaxErrorKind::RegDefSyntax),

            (0, vec![Token::At, Token::LeftBracket, Token::Ident("_123")], SyntaxErrorKind::RawOPCode),
            (0, vec![Token::At, Token::LeftBracket],                       SyntaxErrorKind::RawOPCode),

            (0, vec![Token::At, Token::Number(123)],   SyntaxErrorKind::UnexpectedAt),
            (0, vec![Token::At],                       SyntaxErrorKind::UnexpectedAt),

            (1, vec![Token::Ident("mov"), Token::LeftBracket],                       SyntaxErrorKind::UnexpectedMeta),

            (1, vec![Token::Ident("mov"), Token::LeftBracket, Token::Number(123), Token::Semilicon, Token::Ident("foo")], SyntaxErrorKind::RawArgument),

            (1, vec![Token::Ident("mov"), Token::LeftBracket, Token::Register("foo"), Token::Semilicon], SyntaxErrorKind::AddressOffset),

            (1, vec![Token::Ident("mov"), Token::LeftBracket, Token::At, Token::At], SyntaxErrorKind::UnknownArgument),
        ];

        for (idx, tokens, kind) in tests {
            let actual = SyntaxTree::new(tokens.iter()).map(|f| f.0);

            assert_eq!(actual, Err(SyntaxError { idx, kind }), "tokens: {tokens:?}");
        }
    }
}
