//! Virtual Machine contexts implementation.

use core::cmp::min;
use alloc::{vec, vec::Vec};

use crate::parser::ExpressionArgument;

/// Represents a global context (first 8 registers)
#[derive(Debug)]
pub struct GlobalContext {
    pub stack: Vec<u8>,
    pub regs_fa: [u64; 7],
    pub reg_sc: u64,
}

impl GlobalContext {
    pub fn new() -> Self {
        Self {
            stack: vec![0; 1024],
            regs_fa: [0; 7],
            reg_sc: 0,
        }
    }
    pub fn get_register(&self, kind: RegisterKind) -> u64 {
        match kind {
            RegisterKind::FA(n) => self.regs_fa[n as usize],
            RegisterKind::SC => self.reg_sc,

            _ => panic!("attempted to get local register {kind:?} from global context"),
        }
    }
    pub fn set_register(&mut self, kind: RegisterKind, v: u64) {
        match kind {
            RegisterKind::FA(n) => self.regs_fa[n as usize] = v,
            RegisterKind::SC => self.reg_sc = v,

            _ => panic!("attempted to set local register {kind:?} from global context"),
        }
    }
    pub fn read_stack(&self, ptr: usize) -> Option<u64> {
        let Some(rng) = self.stack.get(ptr..min(ptr + 8, self.stack.len())) else {
            return None;
        };

        Some(
            rng.iter()
                .rev()
                .fold(0u64, |num, byte| (num << 8) | (*byte as u64)),
        )
    }
    pub fn write_stack(&mut self, ptr: usize, v: u64, blen: u8) -> Option<u64> {
        let len = self.stack.len();
        let Some(rng) = self.stack.get_mut(ptr..min(ptr + blen as usize, len)) else {
            return None;
        };

        Some(rng.iter_mut().fold(v, |v, byte| {
            *byte = (v & 0xFF) as u8;
            v >> 8
        }))
    }
}
impl Default for GlobalContext {
    fn default() -> Self {
        Self::new()
    }
}

/// Represents a local contexts with position.
#[derive(Default, Debug)]
pub struct LocalContext {
    pub reg_sp: u64,
    pub regs: [u64; 9],
    pub reg_sys: u64,
    pub reg_cmp: u64,
    pub reg_sig: u8,
    pub reg_wrr: u8,
    pub reg_e1: u32,
    pub reg_e2: u32,
    pub pos: usize,
}

impl LocalContext {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn get_register(&self, kind: RegisterKind) -> u64 {
        match kind {
            RegisterKind::SP => self.reg_sp,
            RegisterKind::R(n) => self.regs[n as usize],
            RegisterKind::SYS => self.reg_sys,
            RegisterKind::CMP => self.reg_cmp,
            RegisterKind::SIG => self.reg_sig as u64,
            RegisterKind::WRR => self.reg_wrr as u64,
            RegisterKind::E1 => self.reg_e1 as u64,
            RegisterKind::E2 => self.reg_e2 as u64,
            RegisterKind::E3 => (self.reg_e2 as u64) << 8 | self.reg_e1 as u64,

            _ => panic!("attempted to get global register {kind:?} from local context"),
        }
    }
    pub fn set_register(&mut self, kind: RegisterKind, v: u64) {
        match kind {
            RegisterKind::SP => self.reg_sp = v,
            RegisterKind::R(n) => self.regs[n as usize] = v,
            RegisterKind::SYS => self.reg_sys = v,
            RegisterKind::CMP => self.reg_cmp = v,
            RegisterKind::SIG => self.reg_sig = v as u8,
            RegisterKind::WRR => self.reg_wrr = v as u8,
            RegisterKind::E1 => self.reg_e1 = v as u32,
            RegisterKind::E2 => self.reg_e2 = v as u32,
            RegisterKind::E3 => {
                self.reg_e1 = v as u32;
                self.reg_e2 = (v >> 32) as u32;
            }

            _ => panic!("attempted to set global register {kind:?} from local context"),
        }
    }
}

/// Ignores the first input. Example: `ignore!(foo, bar) -> bar`.
macro_rules! ignore {
    ($a:tt, $b:tt) => {
        $b
    };
}
/// Implements RegisterKind.
///
/// Generates `to_register(self) -> u8` method, that converts struct
/// to raw register. If variant defined as range, value of variant will be
/// added to start of range (see example bellow).
///
/// Generates `from_register(u8) -> Option<Self>` method, that converts
/// raw register to struct. If variant defined as range and input matches it,
/// value of range will be (input - range_start) (see example bellow).
///
/// ```ignore
/// impl_regkind! {
///     #[repr(u8)]
///     #[derive(Debug, PartialEq)]
///     pub(crate) enum Foo {
///         Bar = 0x01,
///         Baz = 0x02..=0x04,
///     }
/// }
///
/// assert_eq!(Foo::Bar.to_register(), 0x01);
/// assert_eq!(Foo::Baz(1).to_register(), 0x03); // 0x02 (start of range) + 1 (value)
/// assert_eq!(Foo::from_register(0x03), Some(Foo::Baz(1))); // 0x03 matches 0x02..=0x04, so its
///                                                          // Foo::Baz(0x03 (input) - 0x02 (start
///                                                          // of range) ).
/// ```
macro_rules! impl_regkind {
    ($(#[$m:meta])* $v:vis enum $name:ident { $($(#[$mv:meta])* $var:ident = $code:literal $(..=$end:literal)?),* $(,)? }) => {
        $( #[$m] )*
        $v enum $name {$(
            $( #[$mv] )*
            $var $( (ignore!($end, u8)) )? = $code,
        )*}

        impl $name {
            #[doc = "Gets "]
            #[doc = stringify!($name)]
            #[doc = " from raw register id"]
            pub const fn from_register(reg: u8) -> Option<Self> {
                match reg {
                    $(
                        $code $(..=$end)? => Some(Self::$var $((reg - ignore!($end, $code)))?),
                    )*
                    _ => None,
                }
            }
            #[doc = "Converts "]
            #[doc = stringify!($name)]
            #[doc = " to raw register id"]
            pub const fn to_register(self) -> u8 {
                match self {
                    $(
                        Self::$var $( (ignore!($end, n)) )? => $code $( + ignore!($end, n) )?,
                    )*
                }
            }
            /// Checks if register value is correct or [`None`]
            pub const fn checked_checked(self) -> Option<Self> {
                match self {
                    $($(
                        Self::$var (n) if n + $code > $end => None,
                    )?)*
                    _ => Some(self),
                }
            }
        }
    };
}

impl_regkind! {
    /// Kind of register. Can be obtained from raw u8
    /// register using [`RegisterKind::from_register`] and converted back
    /// by [`RegisterKind::to_register`].
    #[derive(Clone, Copy, PartialEq, Eq, Debug)]
    #[repr(u8)]
    pub enum RegisterKind {
        /// "Function argument". Can be from `FA(0)` up to `FA(6)`.
        /// Note: it recommended to use [`RegisterKind::checked`] function on static
        /// construct.
        FA  = 0x00..=0x06,
        /// "Current stack pointer".
        SC  = 0x07,
        /// *Readonly*. "Previous stack pointer". Sets automaticly by `call` and `ret`.
        SP  = 0x08,
        /// General purpose registers. Can be from `R(0)` up to `R(8)`.
        /// Note: it recommended to use [`RegisterKind::checked`] function on static
        /// construct.
        R   = 0x10..=0x18,
        /// System call number register.
        SYS = 0x19,
        /// *Readonly*. Compare result.
        CMP = 0x1a,
        /// *Readonly*. Signal number (can be used in callbacks).
        SIG = 0x1b,
        /// *Readonly*. "Register to write".
        WRR = 0x1c,
        /// *Readonly*. 1st-32nd bytes of 64bit-register.
        E1  = 0x1d,
        /// *Readonly*. 33rd-64th bytes of 64bit-register.
        E2  = 0x1e,
        /// *Readonly*. 64bit-register value.
        E3  = 0x1f,
    }
}

impl RegisterKind {
    /// Returns `true` if this register is only for reading.
    pub const fn is_readonly(self) -> bool {
        !matches!(self, Self::FA(_) | Self::SC | Self::R(_) | Self::SYS)
    }

    /// Checks if register value is correct or panic.
    /// TIP: use constaint [`RegisterKind::checked_checked`] that returns [`Option<RegisterKind>`]
    ///
    /// ```should_panic
    /// # use fwm_base::vm::RegisterKind;
    /// let reg = RegisterKind::FA(10).checked(); // panic!
    /// ```
    #[inline(always)]
    pub fn checked(self) -> Self {
        if let Some(s) = self.checked_checked() {
            s
        } else {
            panic!("invalid register value: {self:?}")
        }
    }
}

/// Represents full Virtual Machine context.
#[derive(Debug)]
pub struct VMContext {
    pub global: GlobalContext,
    pub local: Vec<LocalContext>,
}

impl Default for VMContext {
    fn default() -> Self {
        Self::new()
    }
}
impl VMContext {
    /// Allocate new context.
    pub fn new() -> Self {
        Self {
            global: GlobalContext::new(),
            local: vec![LocalContext::new()],
        }
    }

    pub fn get_local(&self) -> &LocalContext {
        self.local
            .last()
            .expect("last local element should always exists")
    }
    pub fn get_local_mut(&mut self) -> &mut LocalContext {
        self.local
            .last_mut()
            .expect("last local element should always exists")
    }

    pub fn push_function(&mut self, pos: usize) {
        let mut ctx = LocalContext::new();
        ctx.pos = pos;
        ctx.set_register(RegisterKind::SP, self.get_register(RegisterKind::SC));
        self.local.push(ctx);
    }
    pub fn pop_function(&mut self) {
        if self.local.len() == 1 {
            panic!("cannot pop last function");
        }
        self.set_register(RegisterKind::SC, self.get_register(RegisterKind::SP));
        self.local.pop();
    }

    /// Gets value of register.
    pub fn get_register(&self, kind: RegisterKind) -> u64 {
        if kind.to_register() <= 0x07 {
            self.global.get_register(kind)
        } else {
            self.local
                .last()
                .expect("last local element should always exists")
                .get_register(kind)
        }
    }
    /// Sets value to register.
    pub fn set_register(&mut self, kind: RegisterKind, v: u64) {
        if kind.to_register() <= 0x07 {
            self.global.set_register(kind, v)
        } else {
            self.local
                .last_mut()
                .expect("last local element should always exists")
                .set_register(kind, v)
        }
    }

    /// Gets value from argument. If argument is address value will be obrained from stack.
    /// If argument is value this function will return it.
    pub fn get_value(&self, arg: ExpressionArgument) -> Option<u64> {
        match arg {
            ExpressionArgument::Single(reg) if reg < 0x30 => {
                RegisterKind::from_register(reg).map(|kind| self.get_register(kind))
            }
            ExpressionArgument::Double(0xC0, v) => Some(v as u64),
            ExpressionArgument::Single(reg) | ExpressionArgument::Double(reg, _) => {
                let Some(kind) = RegisterKind::from_register(reg % 0x30) else {
                    return None;
                };
                let val = self.get_register(kind);
                let location = match arg {
                    ExpressionArgument::Double(r, o) if r < 0x60 => val + (o as u64),
                    ExpressionArgument::Double(_, o) if o as u64 <= val => val - (o as u64),
                    ExpressionArgument::Single(_) => val,
                    _ => return None,
                };
                self.global.read_stack(location as usize)
            }
            ExpressionArgument::Word(_, v) => Some(v as u64),
            ExpressionArgument::DWord(_, v) => Some(v as u64),
        }
    }


    /// Sets value to argument. If argument is address value will be set to stack.
    /// If argument is value this function will return [`None`]. On success this function
    /// return number, that not writted, usually 0.
    pub fn set_value(&mut self, arg: ExpressionArgument, v: u64) -> Option<u64> {
        self.set_bytes_value(arg, v, 8)
    }

    /// Sets value to argument. If argument is address value will be set to stack.
    /// If argument is value this function will return [`None`]. On success this function
    /// return number, that not writted, usually 0.
    pub fn set_bytes_value(&mut self, arg: ExpressionArgument, v: u64, blen: u8) -> Option<u64> {
        match arg {
            ExpressionArgument::Single(reg) if reg < 0x30 => RegisterKind::from_register(reg)
                .map(|kind| self.set_register(kind, v))
                .map(|_| 0),
            ExpressionArgument::Double(0xC0, _) => None,
            ExpressionArgument::Single(reg) | ExpressionArgument::Double(reg, _) => {
                let Some(kind) = RegisterKind::from_register(reg % 0x30) else {
                    return None;
                };
                let val = self.get_register(kind);
                let location = match arg {
                    ExpressionArgument::Double(r, o) if r < 0x90 => val + (o as u64),
                    ExpressionArgument::Double(_, o) if o as u64 <= val => val - (o as u64),
                    ExpressionArgument::Single(_) => val,
                    _ => return None,
                };
                self.global.write_stack(location as usize, v, blen)
            }
            ExpressionArgument::Word(_, _) | ExpressionArgument::DWord(_, _) => None,
        }
    }

    /// Returns `true` if argument points to readonly thing.
    pub fn is_readonly(arg: ExpressionArgument) -> bool {
        match arg {
            ExpressionArgument::Single(reg) if reg < 0x30 => RegisterKind::from_register(reg)
                .map(RegisterKind::is_readonly)
                .unwrap_or(true),
            ExpressionArgument::Double(0xC0, _) => true,
            ExpressionArgument::Single(_) | ExpressionArgument::Double(_, _) => false,
            ExpressionArgument::Word(_, _) | ExpressionArgument::DWord(_, _) => true,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // internal macro test
    #[test]
    fn impl_regkind() {
        impl_regkind! {
            #[repr(u8)]
            #[derive(Debug, PartialEq, Clone, Copy)]
            pub(crate) enum Foo {
                Foo = 0x00..=0x01,
                Bar = 0x02,
                Baz = 0x03..=0x0a,
            }
        }

        let expected = [
            (Some(Foo::Bar),    0x02),
            (Some(Foo::Baz(1)), 0x04),
            (Some(Foo::Foo(0)), 0x00),
            (None,              0x11),
        ];

        for (foo, val) in expected {
            if let Some(foo) = foo {
                assert_eq!(foo.to_register(), val);
                assert_eq!(foo.checked_checked(), Some(foo));
            }

            assert_eq!(Foo::from_register(val), foo);
        }

        assert_eq!(Foo::Foo(2).checked_checked(), None);
        assert_eq!(Foo::Baz(11).checked_checked(), None);
    }
    // internal macro and my iq test
    #[test]
    fn register_kinds() {
        let kinds: Vec<_> = (0..u8::MAX)
            .map(RegisterKind::from_register)
            .flatten()
            .collect();

        //let mut prog = VMContext::new(Vec::new());
        let mut prog = VMContext::new();
        for kind in &kinds {
            prog.set_register(*kind, 42);
        }
        for kind in &kinds {
            prog.get_register(*kind);
        }
    }
}
