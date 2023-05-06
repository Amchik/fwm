#![cfg_attr(feature = "no-std", no_std)]
extern crate alloc;

/// Lexer implementation
pub mod lex;
/// Syntax tree implementation
pub mod tree;
/// Writer to fwm bytecode
pub mod writer;
