//! Simple virtual machine runner implementation.
use fwm_base_proc_tolower::lower;

use core::{array, convert};

/// read macro or code bellow. Also check docs.
/// Good luck
///
/// ```ignore
/// enum Bar {
///     42 => [
///         variant = 10, // has value 52
///                       // also first variant should be always with code
///     ],
/// }
/// ```
macro_rules! impl_opcodes {
    ($(#[$m1:meta])* $v1:vis enum $name1:ident {} $(#[$m2:meta])* $v2:vis enum $name2:ident { $($group:literal => [ $($(#[doc = $vm:expr])* $var:ident $(= $code:literal)?),* $(,)? ] ),* $(,)? }) => {
        $(#[$m1])*
        $v1 enum $name1 {$(
            $(
                $(#[doc = $vm])* $var $(= $group + $code)?,
            )*
        )*}

        impl $name1 {
            /// Array of all variants.
            pub const VARIANTS: &[$name1] = &[$($(Self::$var, )*)*];

            /// Get name of variant.
            pub const fn name(self) -> &'static str {
                match self {$($(
                    Self::$var => lower!($var),
                )*)*}
            }

            /// Get documentation for variant.
            /// 
            /// *Note*: provided documentation is IN-CODE documentation, like that
            /// you type in `///`.
            pub const fn incode_doc(self) -> &'static str {
                match self {$($(
                    Self::$var => concat!( $($vm)* , ),
                )*)*}
            }
        }

        $(#[$m2])*
        $v2 enum $name2 {$(
            $(
                $(#[doc = $vm])* $var ([crate::parser::ExpressionArgument; $group % 0x8000 / 0x2000]) $(= $group + $code)?,
            )*
        )*}

        impl convert::TryFrom<($name1, &[crate::parser::ExpressionArgument])> for $name2 {
            type Error = array::TryFromSliceError;

            fn try_from(v: ($name1, &[crate::parser::ExpressionArgument])) -> Result<Self, Self::Error> {
                // // -: fix that kurwa
                //let slice = v.1.get(0..v.0.args_count() as usize).unwrap_or(&[]);
                match v.0 {$($(
                    $name1::$var => Ok(Self::$var(v.1.try_into()?)),
                )*)*}
            }
        }
        impl From<&$name2> for $name1 {
            fn from(v: &$name2) -> Self {
                match v {$($(
                    $name2::$var(_) => Self::$var,
                )*)*}
            }
        }
    };
}

impl_opcodes! {
    /// Represents opcode kind. Can be obtained from [`OPCode`]
    /// using [`OPCode::opcode`] or converted to it using [`OPCodeKind::to_opcode`].
    #[derive(Clone, Copy, PartialEq, Eq, Debug)]
    #[repr(u16)]
    pub enum OPCodeKind { /* ... */ }

    /// Represents opcode object. Extended version of [`OPCodeKind`].
    #[derive(Clone, Debug)]
    #[repr(u16)]
    pub enum OPCode {
        0x0000 => [
            /// Signal self
            Die = 0,
            /// Stop execution process
            Halt,
            /// Return from a function
            Ret,
        ],
        0x2000 => [
            /// Call a position. Creates new environment that preserves some registers.
            Call = 0,
            /// Jump to position
            Jmp,
            /// Jump to position if `%cmp == 0`
            Jme,
            /// Jump to position if `%cmp != 0`
            Jmne,
            /// Jump to position if `%cmp > 0`
            Jmgt,
            /// Jump to position if `%cmp >= 0`
            Jmge,
            /// Jump to position if `%cmp < 0`
            Jmlt,
            /// Jump to position if `%cmp <= 0`
            Jmle,
        ],
        0x2100 => [
            /// Invert `%dest`.
            Not = 0,
            /// Negative `%dest`. Note: it works only for 64-bit numbers.
            Neg,
        ],
        0x4000 => [
            /// Move `%src` to `%dest` in 64-bit mode
            Mov = 0,
            /// Move `%src` to `%dest` in 32-bit mode
            Movd,
            /// Move `%src` to `%dest` in 16-bit mode
            Movw,
            /// Move `%src` to `%dest` in 8-bit mode
            Movb,
            /// Performs `%dest <- %dest + %src`
            Add,
            /// Performs `%dest <- %dest - %src`
            Sub,
            /// Performs `%dest <- %dest * %src`
            Mul,
            /// Performs `%dest <- %dest / %src`
            Div,
            /// Performs `%dest <- %dest * %src` (signed)
            IMul,
            /// Performs `%dest <- %dest / %src` (signed)
            IDiv,
            /// Performs `%dest <- %dest >> %src`
            Shr,
            /// Performs `%dest <- %dest << %src`
            Shl,
            /// Performs `%dest <- %dest & %src`
            And,
            /// Performs `%dest <- %dest | %src`
            Or,
            /// Performs `%dest <- %dest ^ %src`
            Xor,
        ],
        0x4100 => [
            /// Performs `%cmp <- %src - %dest`
            Cmp = 0,
            /// Performs `%cmp <- %dest & &src`
            Test,
        ],
        0x4f00 => [
            /// Writes from `%dest` position in stack `%src` bytes to output.
            Write = 0,
        ],
    }
}

impl OPCode {
    /// Gets opcode kind.
    #[inline(always)]
    pub fn opcode(&self) -> OPCodeKind {
        self.into()
    }
}

impl OPCodeKind {
    /// Convert opcode kind to full [`OPCode`] object.
    #[inline(always)]
    pub fn to_opcode(self, args: &[crate::parser::ExpressionArgument]) -> Option<OPCode> {
        let Some(args) = args.get(0..self.args_count() as usize) else {
            return None;
        };
        OPCode::try_from((self, args)).ok()
    }

    /// Try get opcode king by raw id.
    #[inline(always)]
    pub fn from_raw(opcode: u16) -> Option<Self> {
        Self::VARIANTS
            .iter()
            .find(|p| p.as_raw() == opcode)
            .copied()
    }
    /// Returns raw opcide id.
    #[inline(always)]
    pub fn as_raw(self) -> u16 {
        self as u16
    }

    /// Return count of arguments
    #[inline(always)]
    pub fn args_count(self) -> u8 {
        (self.as_raw() % 0x8000 / 0x2000) as u8
    }
}
