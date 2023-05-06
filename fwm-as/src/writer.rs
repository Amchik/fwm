use core::fmt;
use alloc::{string::{String, ToString}, format, vec::Vec};
use hashbrown::HashMap;

use crate::tree::{OPCodeArgument, SyntaxItem};

/// Represents script context of known labels, opcodes and registers.
///
/// # Example
/// ```
/// # use fwm_as::{writer::Context, tree::{SyntaxItem, OPCodeArgument}};
/// #
/// let defs = &[
///     SyntaxItem::OPCodeDef("xor", 0x4001),
///     SyntaxItem::RegisterDef("r0", 0x10),
/// ];
/// let items = &[
///     SyntaxItem::OPCode2("xor", [OPCodeArgument::Address("r0", -4), OPCodeArgument::Number(0xFF)]),
/// ];
///
/// let ctx = Context::new()
///     .populate(defs.iter())
///     .populate(items.iter()); // note: it does nothing unless there no labels
///
/// assert_eq!(ctx.generate(items.iter()), Ok(vec![0x40, 0x01, 0xa0, 0x04, 0xC0, 0xFF]));
/// ```
#[derive(Default, Clone)]
pub struct Context<'a> {
    pub labels: HashMap<String, u64>,
    pub opcodes: HashMap<&'a str, u16>,
    pub regs: HashMap<&'a str, u8>,

    pub last_label: Option<&'a str>,

    pub count: u64,
}

impl<'a> Context<'a> {
    /// Creates empty context
    pub fn new() -> Self {
        Default::default()
    }

    /// Populates context. It using builder pattern, if you need just
    /// mutating (ex. in loops) use [`Context::populate`].
    ///
    /// # Example
    /// ```
    /// # use fwm_as::{writer::Context, tree::SyntaxItem};
    /// #
    /// let defs = &[
    ///     SyntaxItem::OPCodeDef("xor", 0x4001),
    ///     SyntaxItem::RegisterDef("r0", 0x10),
    /// ];
    ///
    /// let ctx = Context::new().populate(defs.iter());
    ///
    /// assert_eq!(ctx.count, 0);
    /// assert_eq!(ctx.opcodes.get("xor"), Some(&0x4001));
    /// ```
    pub fn populate<'b, I>(mut self, v: I) -> Self
    where
        I: IntoIterator<Item = &'a SyntaxItem<'a>>,
        'a: 'b,
    {
        for item in v {
            match item {
                SyntaxItem::Label(label) if label.starts_with(':') => {
                    let label = format!("{}.L{label}", self.last_label.unwrap_or_default());
                    self.labels.insert(label, self.count);
                }
                SyntaxItem::Label(label) => {
                    self.labels.insert(label.to_string(), self.count);
                    self.last_label = Some(label);
                }
                SyntaxItem::OPCodeDef(op, v) => {
                    self.opcodes.insert(op, *v);
                }
                SyntaxItem::RegisterDef(reg, v) => {
                    self.regs.insert(reg, *v);
                }

                SyntaxItem::Raw(len, _) if *len != 0 => {}

                SyntaxItem::OPCode0(_)
                | SyntaxItem::OPCode1(_, _)
                | SyntaxItem::OPCode2(_, _)
                | SyntaxItem::OPCode3(_, _)
                | SyntaxItem::Raw(_, _) => self.count += 1,
            }
        }

        self
    }

    /// Generates fwm bytecode by known context without mutating it.
    /// See more in [`Context`].
    pub fn generate<'b, I>(&self, v: I) -> Result<Vec<u8>, BytecodeError<'a>>
    where
        I: IntoIterator<Item = &'a SyntaxItem<'a>>,
        'a: 'b,
    {
        let mut buffer = Vec::new();
        let mut last_label = None;

        for (expr_id, item) in v.into_iter().enumerate() {
            match item {
                SyntaxItem::Label(label) if !label.starts_with(':') => {
                    last_label = Some(*label);
                }

                SyntaxItem::OPCode0(op)
                | SyntaxItem::OPCode1(op, _)
                | SyntaxItem::OPCode2(op, _)
                | SyntaxItem::OPCode3(op, _) => {
                    let opcode_id = match self.opcodes.get(op) {
                        Some(v) => v.to_be_bytes(),
                        _ => {
                            return Err(BytecodeError {
                                expr_id,
                                kind: BytecodeErrorKind::OPCode(op),
                            });
                        }
                    };

                    buffer.push(opcode_id[0]);
                    buffer.push(opcode_id[1]);

                    for arg in item.opcode_args() {
                        match arg {
                            OPCodeArgument::Number(v) if *v > u16::MAX.into() => {
                                buffer.push(0xC2); // magic const, u32

                                v.to_be_bytes()
                                    .into_iter()
                                    .skip(4)
                                    .for_each(|b| buffer.push(b));
                            }
                            OPCodeArgument::Number(v) if *v > u8::MAX.into() => {
                                buffer.push(0xC1); // magic const, u16

                                v.to_be_bytes()
                                    .into_iter()
                                    .skip(6)
                                    .for_each(|b| buffer.push(b));
                            }
                            OPCodeArgument::Number(v) => {
                                buffer.push(0xC0); // magic const, u8
                                buffer.push(v.to_be_bytes()[7]);
                            }

                            OPCodeArgument::Register(reg) => {
                                let reg = match self.regs.get(reg) {
                                    Some(v) => *v % 0x30,
                                    _ => {
                                        return Err(BytecodeError {
                                            expr_id,
                                            kind: BytecodeErrorKind::Register(reg),
                                        })
                                    }
                                };
                                buffer.push(reg);
                            }
                            OPCodeArgument::Address(reg, off) => {
                                let reg = match self.regs.get(reg) {
                                    Some(v) if *off >= 0 => *v % 0x30 + 0x60,
                                    Some(v) => *v % 0x30 + 0x90,
                                    _ => {
                                        return Err(BytecodeError {
                                            expr_id,
                                            kind: BytecodeErrorKind::Register(reg),
                                        })
                                    }
                                };
                                buffer.push(reg);
                                buffer.push(off.unsigned_abs() as u8);
                            }

                            OPCodeArgument::LabelPtr(label) => {
                                // size optimization?
                                let label = {
                                    let lbl = if label.starts_with(':') {
                                        self.labels.get(&format!(
                                            "{}.L{label}",
                                            last_label.unwrap_or_default()
                                        ))
                                    } else {
                                        self.labels.get(*label)
                                    };

                                    match lbl {
                                        Some(l) => *l,
                                        _ => {
                                            return Err(BytecodeError {
                                                expr_id,
                                                kind: BytecodeErrorKind::Label(label),
                                            })
                                        }
                                    }
                                };
                                buffer.push(0xC2); // u32 prefix
                                label
                                    .to_be_bytes()
                                    .into_iter()
                                    .skip(4)
                                    .for_each(|b| buffer.push(b));
                            }

                            OPCodeArgument::Raw(len @ 0..=8, val) => val
                                .to_be_bytes()
                                .into_iter()
                                .skip(8 - *len as usize)
                                .for_each(|b| buffer.push(b)),

                            OPCodeArgument::Raw(len, _) => {
                                return Err(BytecodeError {
                                    expr_id,
                                    kind: BytecodeErrorKind::BigRaw(*len),
                                })
                            }
                        }
                    }
                }

                SyntaxItem::Raw(len @ 0..=8, val) => val
                    .to_be_bytes()
                    .into_iter()
                    .skip(8 - *len as usize)
                    .for_each(|b| buffer.push(b)),

                SyntaxItem::Raw(len, _) => {
                    return Err(BytecodeError {
                        expr_id,
                        kind: BytecodeErrorKind::BigRaw(*len),
                    })
                }

                _ => {}
            }
        }

        Ok(buffer)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BytecodeError<'a> {
    pub expr_id: usize,
    pub kind: BytecodeErrorKind<'a>,
}

impl<'a> fmt::Display for BytecodeError<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.kind.fmt(f)?;
        write!(f, " at expression #{}", self.expr_id)
    }
}
#[cfg(not(feature = "no-std"))]
impl<'a> std::error::Error for BytecodeError<'a> {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BytecodeErrorKind<'a> {
    OPCode(&'a str),
    Register(&'a str),
    Label(&'a str),
    BigRaw(u64),
}

impl<'a> fmt::Display for BytecodeErrorKind<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::OPCode(op) => write!(f, "unknown opcode `{op}`"),
            Self::Register(reg) => write!(f, "unknown register `{reg}`"),
            Self::Label(label) => write!(f, "unknown label `{label}`"),
            Self::BigRaw(len) => write!(f, "invalid raw len: {len}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use alloc::vec;
    use super::*;

    #[test]
    fn normal_fragment() {
        let defs = &[
            SyntaxItem::OPCodeDef("halt", 0x0000),
            SyntaxItem::OPCodeDef("jmp", 0x2000),
            SyntaxItem::OPCodeDef("xor", 0x4000),
            SyntaxItem::OPCodeDef("mov", 0x4001),
            SyntaxItem::OPCodeDef("addassign", 0x6000),
            SyntaxItem::RegisterDef("r0", 0x10),
        ];
        let items = &[
            SyntaxItem::OPCode2(
                "xor",
                [
                    OPCodeArgument::Register("r0"),
                    OPCodeArgument::Register("r0"),
                ],
            ),
            SyntaxItem::OPCode2(
                "mov",
                [
                    OPCodeArgument::Register("r0"),
                    OPCodeArgument::Number(u8::MAX.into()),
                ],
            ),
            SyntaxItem::OPCode2(
                "mov",
                [
                    OPCodeArgument::Register("r0"),
                    OPCodeArgument::Number(u16::MAX.into()),
                ],
            ),
            SyntaxItem::OPCode2(
                "mov",
                [OPCodeArgument::Register("r0"), OPCodeArgument::Number(0)],
            ),
            SyntaxItem::OPCode2(
                "mov",
                [
                    OPCodeArgument::Register("r0"),
                    OPCodeArgument::Number(u16::MAX as u64 + 1),
                ],
            ),
            SyntaxItem::Raw(0, 0),
            SyntaxItem::Raw(8, 0x4001_10_C2FFFFFFFF), // mov %r0, int32(0xFFFF_FFFF)
            SyntaxItem::Raw(0, 0),
            SyntaxItem::Raw(1, 0x20),
            SyntaxItem::Raw(2, 0x10_10), // op(0x2010) %r0
            SyntaxItem::OPCode1("jmp", OPCodeArgument::LabelPtr("exampleLabel")),
            SyntaxItem::Label("exampleLabel"),
            SyntaxItem::OPCode1("jmp", OPCodeArgument::LabelPtr("exampleLabel")),
            SyntaxItem::OPCode1("jmp", OPCodeArgument::Address("r0", 1)),
            SyntaxItem::OPCode1("jmp", OPCodeArgument::Address("r0", -1)),
            SyntaxItem::OPCode1("jmp", OPCodeArgument::Address("r0", -0xFF)),
            SyntaxItem::OPCode1("jmp", OPCodeArgument::Address("r0", 0xFF)),
            SyntaxItem::OPCode3(
                "addassign",
                [
                    OPCodeArgument::Register("r0"),
                    OPCodeArgument::Number(40),
                    OPCodeArgument::Number(2),
                ],
            ),
            SyntaxItem::OPCode0("halt"),
        ];
        #[rustfmt::skip] // imagine if this test fail
        let expected = vec![
            0x40, 0x00, 0x10, 0x10, // xor %r0, %r0
            0x40, 0x01, 0x10, 0xC0, 0xFF, // mov %r0, $FFh
            0x40, 0x01, 0x10, 0xC1, 0xFF, 0xFF, // mov %r0, $FFFFh
            0x40, 0x01, 0x10, 0xC0, 0x00, // mov %r0, 0
            0x40, 0x01, 0x10, 0xC2, 0x00, 0x01, 0x00, 0x00, // mov %r0, $1_0000h
            // raw, len=0
            0x40, 0x01, 0x10, 0xC2, 0xFF, 0xFF, 0xFF, 0xFF, // raw, len=8
            // raw, len=0
            0x20 /* raw, len = 1 */, 0x10, 0x10, // raw, len=2
            0x20, 0x00, 0xC2, 0x00, 0x00, 0x00, 0x08, // jmp [exampleLabel]
            // label `exampleLabel` @ expression ID 8
            0x20, 0x00, 0xC2, 0x00, 0x00, 0x00, 0x08, // jmp [exampleLabel]
            0x20, 0x00, 0x70, 0x01, // jmp [%r0; 1]
            0x20, 0x00, 0xa0, 0x01, // jmp [%r0; -1]
            0x20, 0x00, 0xa0, 0xFF, // jmp [%r0; -255]
            0x20, 0x00, 0x70, 0xFF, // jmp [%r0; 255]
            0x60, 0x00, 0x10, 0xC0, 0x28, 0xC0, 0x02, // addassign %r0, 40, 2
            0x00, 0x00, // halt
        ];

        let ctx = Context::new().populate(defs.iter()).populate(items.iter());

        assert_eq!(ctx.generate(items.iter()), Ok(expected));
    }

    #[test]
    fn erroneous_fragments() {
        let defs = &[
            SyntaxItem::OPCodeDef("jmp", 0x2000),
            SyntaxItem::OPCodeDef("mov", 0x4001),
            SyntaxItem::RegisterDef("r0", 0x10),
        ];

        #[rustfmt::skip]
        let cases = [
            (0, vec![SyntaxItem::OPCode2("movq", [OPCodeArgument::Register("r1"), OPCodeArgument::Register("r0")])], BytecodeErrorKind::OPCode("movq")),
            (0, vec![SyntaxItem::OPCode2("mov", [OPCodeArgument::Register("r1"), OPCodeArgument::Register("r0")])], BytecodeErrorKind::Register("r1")),
            (1, vec![SyntaxItem::Label("foo"), SyntaxItem::OPCode1("jmp", OPCodeArgument::LabelPtr("fo"))], BytecodeErrorKind::Label("fo")),
            (0, vec![SyntaxItem::OPCode1("mov", OPCodeArgument::Raw(16, 0))], BytecodeErrorKind::BigRaw(16)),
            (0, vec![SyntaxItem::Raw(9, 0)], BytecodeErrorKind::BigRaw(9)),
        ];

        let ctx = Context::new().populate(defs.iter());

        for (expr_id, items, kind) in cases {
            let expected = Err(BytecodeError { expr_id, kind });
            let actual = ctx.clone().populate(items.iter()).generate(items.iter());

            assert_eq!(actual, expected, "items: {items:?}");
        }
    }

    #[test]
    fn known_labels() {
        let code = &[
            SyntaxItem::OPCodeDef("jmp", 0x2001),
            SyntaxItem::Label(":0"),
            SyntaxItem::OPCode1("jmp", OPCodeArgument::LabelPtr(":0")),
            SyntaxItem::Label("foo"),
            SyntaxItem::Label(":0"),
            SyntaxItem::OPCode1("jmp", OPCodeArgument::LabelPtr(":0")),
            SyntaxItem::Label("bar"),
            SyntaxItem::Label(":0"),
            SyntaxItem::OPCode1("jmp", OPCodeArgument::LabelPtr(":0")),
        ];
        let expected = vec![
            0x20, 0x01, 0xC2, 0x00, 0x00, 0x00, 0x00, // jmp u32(0)
            0x20, 0x01, 0xC2, 0x00, 0x00, 0x00, 0x01, // jmp u32(1)
            0x20, 0x01, 0xC2, 0x00, 0x00, 0x00, 0x02, // jmp u32(2)
        ];
        let ctx = Context::new().populate(code.iter());

        let actual = ctx.generate(code.iter());
        assert_eq!(actual, Ok(expected));
    }
}
