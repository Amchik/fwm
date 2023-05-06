//! # FWM Virtual Machine
//!
//! This crate contains base things of fwm. fwm bytecode goes through 4 stages
//! to be executed:
//!
//! 1. [`parser`] -- parser stage. Parses bytecode to objects.
//! 2. [`vm`] -- virtual environment. Creates and allocates registers and other things.
//! 3. [`opcode`] -- parse numberic opcodes into real.
//! 4. [`runner`] -- execute code by real opcodes obtained in previous stage.
//!
//! Stage 3 and 4 can be replaced by owm if it needed.
//!
//! # Example
//! Opcode list and specification can be found in [`OPCodeKind`] enum.
//!
//! ```
//! # use fwm_base::{parser::*, opcode::*, vm::*, runner::*};
//! #
//! let bytecode = &[
//!     0x40, 0x00, 0x00, 0xC0, 0x30, // mov   %fa0, 48
//!     0x40, 0x00, 0x01, 0xC0, 0x40, // mov   %fa1, 64
//!     0x20, 0x00, 0xC0, 0x07,       // call  7
//!     0x41, 0x00, 0x00, 0xC0, 0x70, // cmp   %fa0, 112     # 48 + 64 = 112
//!     0x20, 0x02, 0xC0, 0x06,       // jme   6
//!     0x00, 0x00,                   // die
//!     0x00, 0x01,                   // halt
//!
//!     0x40, 0x04, 0x00, 0x01,       // add %fa0, %fa1
//!     0x00, 0x02,                   // ret                 # %fa0 is a return register
//! ];
//!
//! let opcodes = {
//!     let exprs: Result<Option<Vec<_>>, _> = Parser::new(bytecode)
//!         .into_iter()
//!         .map(|f| f.map(|r| OPCodeKind::from_raw(r.opcode).and_then(|o| o.to_opcode(&r.args))))
//!         .collect();
//!
//!     match exprs {
//!         Ok(Some(v)) => v,
//!         Ok(None) => panic!("vm-error: unknown opcode kind or syntax"),
//!         Err(e) => panic!("vm-error: {e}"),
//!     }
//! };
//!
//! let mut fwm = FWMRunner::new(opcodes);
//!
//! loop {
//!     match fwm.run() {
//!         FWMSignal::Continue | FWMSignal::Data(_) => continue,
//!         FWMSignal::EOF => break,
//!         FWMSignal::Signaled => panic!("runtime-error: signaled"),
//!     }
//! }
//!
//! assert_eq!(fwm.context.get_register(RegisterKind::FA(0)), 112);
//! ```
//!
//! # Specification
//!
//! Concept stolen from 0wm, written in C. First 2 bytes is OPCODE: opcode kind and number.
//!
//! [`ExpressionArgument`] represents one argument, [`Expression`] represents full expresion
//! including all arguments (if any).
//!
//! ## OPCODE kind specification
//!
//! | Range |  Description   | Arguments count |
//! |-------|----------------|-----------------|
//! | 00-1f | system opcodes | 0               |
//! | 20-3f | system opcodes | 1               |
//! | 40-5f | system opcodes | 2               |
//! | 60-6f | system opcodes | 3               |
//! | 70-7f | reserved       | 3[^1]           |
//! | 80-9f | user opcodes   | 0               |
//! | a0-bf | user opcodes   | 1               |
//! | c0-df | user opcodes   | 2               |
//! | e0-ff | user opcodes   | 3               |
//!
//! [^1]: may changed in future
// TODO: typo
//!
//! ## Arguments specification
//!
//! |             Name             |               Length              | Range (in hex) |
//! |------------------------------|-----------------------------------|----------------|
//! | Common registers             | [`ExpressionArgument::Single`], 1 | 00-2f          |
//! | Address (of common regs)     | [`ExpressionArgument::Single`], 1 | 30-5f          |
//! | Address with positive offset | [`ExpressionArgument::Double`], 2 | 60-8f          |
//! | Address with negative offset | [`ExpressionArgument::Double`], 2 | 90-bf          |
//! | `u8` (1 byte) value          | [`ExpressionArgument::Double`], 2 | c0             |
//! | `u16` (2 bytes) value        | [`ExpressionArgument::Word`], 3   | c1             |
//! | `u32` (4 bytes) value        | [`ExpressionArgument::DWord`], 5  | c2             |
//!
//! ## Registers specification
//!
//! There only 32 register. All is 64-bit numbers. Some register are readonly.
//!
//! |      Name      |     Code(s)    | Description                                                                 |
//! |----------------|----------------|-----------------------------------------------------------------------------|
//! | `%FA0`..`%FA6` | `0x00`..`0x06` | *Public*. Function arguments.                                               |
//! | `%SC`          | `0x07`         | *Public* "Current stack pointer".                                           |
//! | `%SP`          | `0x08`         | *Readonly*. "Previous stack pointer". Sets automaticly by `call` and `ret`. |
//! | `%R0`..`%R8`   | `0x10`..`0x18` | General purpose registers. Can be from `R(0)` up to `R(8)`.                 |
//! | `%SYS`         | `0x19`         | System call number register.                                                |
//! | `%CMP`         | `0x1a`         | *Readonly*. Compare result (from `cmp` and `test`)                          |
//! | `%SIG`         | `0x1b`         | *Readonly*. Signal number                                                   |
//! | `%WRR`         | `0x1d`         | *Readonly*. "Register to write".                                            |
//! | `%E1`          | `0x1d`         | *Readonly*. 1st-32nd bytes of 64bit-register.                               |
//! | `%E2`          | `0x1e`         | *Readonly*. 33rd-64th bytes of 64bit-register.                              |
//! | `%E3`          | `0x1f`         | *Readonly*. 64bit-register value.                                           |
//!
//! There is [`RegisterKind`] struct, that represents all kinds of register.
//!

#![cfg_attr(feature = "no-std", no_std)]
extern crate alloc;

// doc imports
#[allow(unused_imports)]
use {parser::*, vm::*, opcode::*};

pub mod opcode;
pub mod parser;
pub mod runner;
pub mod vm;
