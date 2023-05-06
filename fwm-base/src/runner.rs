//! Simple portable fwm runner
//!
//! It parses [`OPCode`]s and runs it. See [`FWMRunner`] docs for
//! more.

use alloc::vec::Vec;

use crate::{
    opcode::{OPCode, OPCodeKind},
    vm::{RegisterKind, VMContext},
};

/// FWM simple runner
///
/// # Example
/// See [parser module](../parser/index.html) doc for parsing. Here `parse_code` is just example.
/// ```
/// # use fwm_base::{runner::{FWMRunner, FWMSignal}, parser::*, opcode::*, vm::*};
/// # 
/// # fn parse_code(s: &[u8]) -> Vec<OPCode> {
/// #    Parser::new(s)
/// #        .into_iter()
/// #        .map(|f| f
/// #            .map(|r| OPCodeKind::from_raw(r.opcode)
/// #            .and_then(|o| o.to_opcode(&r.args)))
/// #            .ok())
/// #        .flatten()
/// #        .map(Option::unwrap)
/// #        .collect()
/// # }
/// let code = vec![ 0x40, 0x00, 0x00, 0xC0, 0x14 ]; // mov %fa0, 14
/// let opcodes: Vec<OPCode> = parse_code(&code);
///
/// let mut fwm = FWMRunner::new(opcodes);
/// let sig = loop {
///     match fwm.run() {
///         FWMSignal::Continue => {},
///         s => break s,
///     }
/// };
/// assert_eq!(sig, FWMSignal::EOF);
/// assert_eq!(fwm.context.get_register(RegisterKind::FA(0)), 0x14);
/// ```
#[derive(Debug)]
pub struct FWMRunner {
    pub lines: Vec<OPCode>,
    pub context: VMContext,
}
/// Type of returned signal
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FWMSignal<'a> {
    /// All ok, no errors
    Continue,
    /// Like [`FWMSignal::Continue`], but with data
    Data(&'a [u8]),
    /// End of execution list
    EOF,
    /// Signaled, something went wrong
    Signaled,
}

impl FWMRunner {
    /// Creates new runner from code lines
    pub fn new(lines: Vec<OPCode>) -> Self {
        Self {
            lines,
            context: VMContext::new(),
        }
    }

    /// Execute one line and go to next
    ///
    /// # Example usage
    /// ```
    /// # use fwm_base::{runner::*, opcode::*, parser::*};
    /// #
    /// let code = vec![
    ///     OPCode::Mov([
    ///         ExpressionArgument::Single(0x00), // %fa0
    ///         ExpressionArgument::Double(0xC0, 0x2A), // 42
    ///     ]),
    ///     OPCode::Halt([]),
    /// ];
    /// // Single run
    /// let mut fwm = FWMRunner::new(code.clone());
    /// assert_eq!(fwm.run(), FWMSignal::Continue);
    /// assert_eq!(fwm.run(), FWMSignal::EOF);
    ///
    /// // or using `loop`:
    /// let mut fwm = FWMRunner::new(code.clone());
    /// let sig = loop {
    ///     match fwm.run() {
    ///         FWMSignal::Continue => {},
    ///         sig => break sig,
    ///     }
    /// };
    /// assert_eq!(sig, FWMSignal::EOF);
    /// ```
    pub fn run(&mut self) -> FWMSignal {
        let local = self.context.get_local();
        let Some(opcode) = self.lines.get(local.pos) else {
            return FWMSignal::EOF;
        };
        let mut data = None;

        self.context.get_local_mut().pos += 1;

        match opcode {
            OPCode::Die(_) => {
                return FWMSignal::Signaled;
            }
            OPCode::Halt(_) => {
                return FWMSignal::EOF;
            }
            OPCode::Ret(_) => {
                if self.context.local.len() == 1 {
                    return FWMSignal::Signaled;
                }
                self.context.pop_function();
            }

            OPCode::Call([pos]) => {
                let Some(pos) = self.context.get_value(*pos) else {
                    return FWMSignal::Signaled;
                };
                self.context.push_function(pos as usize);
                return FWMSignal::Continue;
            }
            OPCode::Jmp([pos])
            | OPCode::Jme([pos])
            | OPCode::Jmne([pos])
            | OPCode::Jmgt([pos])
            | OPCode::Jmge([pos])
            | OPCode::Jmlt([pos])
            | OPCode::Jmle([pos]) => 'brk: {
                let (kind, cmp) = (
                    opcode.opcode(),
                    self.context.get_register(RegisterKind::CMP),
                );
                let cont = match kind {
                    OPCodeKind::Jmp => true,
                    OPCodeKind::Jme => cmp == 0,
                    OPCodeKind::Jmne => cmp != 0,
                    OPCodeKind::Jmgt => (cmp as i64) > 0,
                    OPCodeKind::Jmge => (cmp as i64) >= 0,
                    OPCodeKind::Jmlt => (cmp as i64) < 0,
                    OPCodeKind::Jmle => (cmp as i64) <= 0,

                    _ => unreachable!(),
                };
                if !cont {
                    break 'brk;
                }

                let Some(pos) = self.context.get_value(*pos) else {
                    return FWMSignal::Signaled;
                };
                self.context.get_local_mut().pos = pos as usize;
                return FWMSignal::Continue;
            }

            OPCode::Not([dest]) | OPCode::Neg([dest]) => {
                let kind = opcode.opcode();
                if VMContext::is_readonly(*dest) {
                    return FWMSignal::Signaled;
                }
                let Some(val) = self.context.get_value(*dest) else {
                    return FWMSignal::Signaled;
                };
                let val = match kind {
                    OPCodeKind::Not => !val,
                    OPCodeKind::Neg => -(val as i64) as u64,

                    _ => unreachable!(),
                };
                if self.context.set_value(*dest, val).is_none() {
                    return FWMSignal::Signaled;
                }
            }

            OPCode::Mov([dest, src])
            | OPCode::Movd([dest, src])
            | OPCode::Movw([dest, src])
            | OPCode::Movb([dest, src]) => {
                let Some(val) = self.context.get_value(*src) else {
                    return FWMSignal::Signaled;
                };
                if VMContext::is_readonly(*dest) {
                    return FWMSignal::Signaled;
                }
                let blen = match opcode.opcode() {
                    OPCodeKind::Mov => 8,
                    OPCodeKind::Movd => 4,
                    OPCodeKind::Movw => 2,
                    OPCodeKind::Movb => 1,

                    _ => unreachable!(),
                };
                if self.context.set_bytes_value(*dest, val, blen).is_none() {
                    return FWMSignal::Signaled;
                }
            }
            OPCode::Add([dest, src])
            | OPCode::Sub([dest, src])
            | OPCode::Mul([dest, src])
            | OPCode::Div([dest, src])
            | OPCode::IMul([dest, src])
            | OPCode::IDiv([dest, src])
            | OPCode::Shr([dest, src])
            | OPCode::Shl([dest, src])
            | OPCode::And([dest, src])
            | OPCode::Or([dest, src])
            | OPCode::Xor([dest, src]) => {
                let kind = opcode.opcode();
                if VMContext::is_readonly(*dest) {
                    return FWMSignal::Signaled;
                }
                let (Some(lhs), Some(rhs)) = (self.context.get_value(*dest), self.context.get_value(*src)) else {
                    return FWMSignal::Signaled;
                };
                let val = match kind {
                    OPCodeKind::Div | OPCodeKind::IDiv if rhs == 0 => return FWMSignal::Signaled,

                    OPCodeKind::Add => lhs.overflowing_add(rhs).0,
                    OPCodeKind::Sub => lhs.overflowing_sub(rhs).0,
                    OPCodeKind::Mul => lhs.overflowing_mul(rhs).0,
                    OPCodeKind::Div => lhs.overflowing_div(rhs).0,
                    OPCodeKind::IMul => ((lhs as i64).overflowing_div(rhs as i64)).0 as u64,
                    OPCodeKind::IDiv => ((lhs as i64).overflowing_div(rhs as i64)).0 as u64,
                    OPCodeKind::Shr => lhs >> rhs,
                    OPCodeKind::Shl => lhs << rhs,
                    OPCodeKind::And => lhs & rhs,
                    OPCodeKind::Or => lhs | rhs,
                    OPCodeKind::Xor => lhs ^ rhs,

                    _ => unreachable!(),
                };
                if self.context.set_value(*dest, val).is_none() {
                    return FWMSignal::Signaled;
                }
            }

            OPCode::Cmp([a, b]) | OPCode::Test([a, b]) => {
                let (Some(a), Some(b)) = (self.context.get_value(*a), self.context.get_value(*b)) else {
                    return FWMSignal::Signaled;
                };
                let v = match opcode.opcode() {
                    OPCodeKind::Cmp => b.overflowing_sub(a).0,
                    OPCodeKind::Test => a & b,

                    _ => unreachable!(),
                };
                self.context.set_register(RegisterKind::CMP, v);
            }

            OPCode::Write([addr, len]) => {
                let (Some(addr), Some(len)) = (self.context.get_value(*addr), self.context.get_value(*len)) else {
                    return FWMSignal::Signaled;
                };
                let (addr, len) = (addr as usize, len as usize);
                if addr + len > self.context.global.stack.len() {
                    return FWMSignal::Signaled;
                }
                data = Some(&self.context.global.stack[addr..addr + len]);
            }
        };

        if let Some(data) = data {
            FWMSignal::Data(data)
        } else {
            FWMSignal::Continue
        }
    }
}
