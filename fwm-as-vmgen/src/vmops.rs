#[cfg(feature = "default-as")]
use fwm_as::tree::SyntaxItem;
#[cfg(feature = "default-vm")]
use fwm_base::{opcode::OPCodeKind, vm::RegisterKind};

use alloc::{vec, vec::Vec};

/// Virtual Machine defination.
pub trait VMInfo {
    /// Type of OPCodes
    type OPCode;
    /// Type of registers
    type Register;

    /// Returns all opcodes
    fn get_all_opcodes() -> Vec<Self::OPCode>;
    /// Returns static opcode name
    fn get_opcode_name(v: &Self::OPCode) -> &'static str;
    /// Returns static opcode id
    fn get_opcode_id(v: &Self::OPCode) -> u16;

    /// Returns all registers
    fn get_all_registers() -> Vec<Self::Register>;
    /// Return static register name
    fn get_register_name(v: &Self::Register) -> &'static str;
    /// Returns static register ID
    fn get_register_id(v: &Self::Register) -> u8;
}

#[derive(Clone, PartialEq, Eq, Default, Debug)]
pub struct VMInfoBuilder {
    pub opcodes: Vec<(&'static str, u16)>,
    pub registers: Vec<(&'static str, u8)>,
}

impl VMInfoBuilder {
    /// Creates new empty [`VMInfoBuilder`]
    pub fn new() -> Self {
        Default::default()
    }

    /// Build new [`VMInfoBuilder`] from [`VMInfo`].
    pub fn from_vm_opcodes<T: VMInfo>() -> Self {
        let mut s = Self::new();

        for opcode in T::get_all_opcodes() {
            s.opcodes
                .push((T::get_opcode_name(&opcode), T::get_opcode_id(&opcode)));
        }
        for reg in T::get_all_registers() {
            s.registers
                .push((T::get_register_name(&reg), T::get_register_id(&reg)));
        }

        s
    }

    /// Converts self to [`SyntaxItem`]s.
    #[cfg(feature = "default-as")]
    pub fn to_syntax_items(self) -> Vec<SyntaxItem<'static>> {
        self.opcodes
            .into_iter()
            .map(|(op, v)| SyntaxItem::OPCodeDef(op, v))
            .chain(
                self.registers
                    .into_iter()
                    .map(|(reg, v)| SyntaxItem::RegisterDef(reg, v)),
            )
            .collect()
    }
}

/// FWM Virtual machine info. See [`VMInfoBuilder`] for more.
#[cfg(feature = "default-vm")]
pub struct FWMInfo;

#[cfg(feature = "default-vm")]
impl VMInfo for FWMInfo {
    type OPCode = OPCodeKind;
    type Register = (&'static str, u8);

    fn get_all_opcodes() -> Vec<Self::OPCode> {
        Vec::from(OPCodeKind::VARIANTS)
    }
    fn get_opcode_name(v: &Self::OPCode) -> &'static str {
        v.name()
    }
    fn get_opcode_id(v: &Self::OPCode) -> u16 {
        v.as_raw()
    }

    fn get_all_registers() -> Vec<Self::Register> {
        vec![
            ("fa0", RegisterKind::FA(0).to_register()),
            ("fa1", RegisterKind::FA(1).to_register()),
            ("fa2", RegisterKind::FA(2).to_register()),
            ("fa3", RegisterKind::FA(3).to_register()),
            ("fa4", RegisterKind::FA(4).to_register()),
            ("fa5", RegisterKind::FA(5).to_register()),
            ("fa6", RegisterKind::FA(6).to_register()),

            ("sc", RegisterKind::SC.to_register()),
            ("sp", RegisterKind::SP.to_register()),

            ("r0", RegisterKind::R(0).to_register()),
            ("r1", RegisterKind::R(1).to_register()),
            ("r2", RegisterKind::R(2).to_register()),
            ("r3", RegisterKind::R(3).to_register()),
            ("r4", RegisterKind::R(4).to_register()),
            ("r5", RegisterKind::R(5).to_register()),
            ("r6", RegisterKind::R(6).to_register()),
            ("r7", RegisterKind::R(7).to_register()),
            ("r8", RegisterKind::R(8).to_register()),

            ("sys", RegisterKind::SYS.to_register()),
            ("cmp", RegisterKind::CMP.to_register()),
            ("sig", RegisterKind::SIG.to_register()),
            ("wrr", RegisterKind::WRR.to_register()),
            ("e1", RegisterKind::E1.to_register()),
            ("e2", RegisterKind::E2.to_register()),
            ("e3", RegisterKind::E3.to_register()),
        ]
    }
    fn get_register_name(v: &Self::Register) -> &'static str {
        v.0
    }
    fn get_register_id(v: &Self::Register) -> u8 {
        v.1
    }
}
