//! # `yaxpeax-lc87`, a decoder for the LC87 instruction set
//!
//! the LC87 instruction set is used in the LC87 series of microcontrollers, originally developed
//! by Sanyo, whose semiconductor division was acquired by [ON Semiconductor in
//! 2011](https://www.onsemi.com/PowerSolutions/newsItem.do?article=2458). LC87 parts are typically
//! named `LC87*`, are all 8-bit controllers, and range between 10-pin 8kb-of-flash and 100-pin
//! 256kb-of-flash sizes.
//!
//! in theory there exists an `LC87 Series Users's Manual` but it appears to have never existed
//! online in original Japanese, or English translation. (the existence of an English translation
//! is suspected but unconfirmed). by coincidence, LC87 instructions are described in the public
//! `LC872H00` datasheet, describing specifically `LC872H00` parts. because the instruction set is
//! shared across the LC87 family of microcontrollers, the instruction set listing in this manual
//! describes the instruction set of the rest of the family.
//!
//! datasheet: [`ANDLC872H00-D.PDF`](https://www.onsemi.com/pub/Collateral/ANDLC872H00-D.PDF).  
//! `sha256: 9cefe73a252468bbbfb81a28e59cb9444c4c49586a616c873958b39ad4fa7b35`
//!
//! ## usage
//!
//! the fastest way to decode an lc87 instruction is through
//! [`InstDecoder::decode_slice()`]:
//! ```
//! use yaxpeax_lc87::InstDecoder;
//!
//! let inst = InstDecoder::decode_slice(&[0x0a, 0x10, 0x3f]).unwrap();
//!
//! assert_eq!("bp 0010h, 2, $+0x3f", inst.to_string());
//! ```
//!
//! opcodes and operands are available on the decoded instruction, as well as its length and
//! operand count:
//! ```
//! use yaxpeax_lc87::{InstDecoder, Operand};
//!
//! let inst = InstDecoder::decode_slice(&[0x0a, 0x10, 0x3f]).unwrap();
//!
//! assert_eq!("bp 0010h, 2, $+0x3f", inst.to_string());
//! assert_eq!(inst.operand_count(), 3);
//! assert_eq!(inst.len(), 3);
//! assert_eq!(inst.operand(0).unwrap(), Operand::AbsU16 { addr: 0x0010 });
//! assert_eq!(inst.operand(1).unwrap(), Operand::BitIndex { index: 2 });
//! ```
//!
//! additionally, `yaxpeax-lc87` implements `yaxpeax-arch` traits for generic use, such as
//! [`yaxpeax_arch::LengthedInstruction`]. [`yaxpeax_arch::Arch`] is implemented by
//! the unit struct [`LC87`].
//!
//! ## `#![no_std]`
//!
//! `yaxpeax-lc87` should support `no_std` usage, but this is entirely untested.

#![no_std]

mod display;

use yaxpeax_arch::{AddressDiff, Arch, Decoder, LengthedInstruction, Reader, StandardDecodeError};

/// a trivial struct for [`yaxpeax_arch::Arch`] to be implemented on. it's only interesting for the
/// associated type parameters.
#[derive(Hash, Eq, PartialEq, Debug, Copy, Clone)]
pub struct LC87;

impl Arch for LC87 {
    type Address = u16;
    type Word = u8;
    type Instruction = Instruction;
    type Decoder = InstDecoder;
    type DecodeError = StandardDecodeError;
    type Operand = Operand;
}

/// an `lc87` instruction.
///
/// `lc87` instructions have an [`Opcode`] and up to three [`Operand`]s. they are no more than four
/// bytes long.
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub struct Instruction {
    opcode: Opcode,
    operands: [Operand; 3],
    operand_count: u8,
    length: u8,
}

impl Default for Instruction {
    fn default() -> Instruction {
        Instruction {
            opcode: Opcode::NOP,
            operands: [Operand::Nothing, Operand::Nothing, Operand::Nothing],
            operand_count: 0,
            length: 0,
        }
    }
}

impl Instruction {
    fn reset_operands(&mut self) {
        self.operands = [Operand::Nothing, Operand::Nothing, Operand::Nothing];
        self.operand_count = 0;
    }

    fn with_operand(&mut self, operand: Operand) {
        self.operands[self.operand_count as usize] = operand;
        self.operand_count += 1;
    }

    pub fn len(&self) -> u8 {
        self.length
    }

    pub fn operand_count(&self) -> u8 {
        self.operand_count
    }

    pub fn operand(&self, idx: u8) -> Option<Operand> {
        self.operands.get(idx as usize).cloned()
    }
}

impl LengthedInstruction for Instruction {
    type Unit = AddressDiff<<LC87 as Arch>::Address>;
    fn min_size() -> Self::Unit {
        AddressDiff::from_const(1)
    }
    fn len(&self) -> Self::Unit {
        AddressDiff::from_const(self.length as u16)
    }
}

impl yaxpeax_arch::Instruction for Instruction {
    fn well_defined(&self) -> bool { true }
}

/// an operand for an `lc87` instruction.
#[derive(Copy, Clone, Hash, PartialEq, Eq)]
pub enum Operand {
    /// no operand in this position.
    ///
    /// reaching this as a user of `yaxpeax_lc87` is almost certainly a bug. `Instruction::operand`
    /// will return `None` rather than `Operand::Nothing`.
    Nothing,
    /// branch to the absolute address `addr`.
    BranchAbsU17 { addr: u32 },
    /// branch to the relative address `rel` (`PC` + `inst.len()` + `rel`).
    BranchRelU12 { rel: u16 }, // in practice it looks like all branches are forward?
    /// an 8-bit immediate.
    ///
    /// the meaning of this immediate is opcode-dependent, but usually a value used for a bitwise
    /// or arithmetic operation.
    ImmU8 { imm: u8 },
    /// a 16-bit immediate.
    ///
    /// this is only used for the wide `mov` that loads both `A` and `B` registers at once. `A`
    /// gets the low byte, `B` gets the high byte.
    ImmU16 { imm: u16 },
    /// a memory access to an absolute 16-bit address.
    AbsU16 { addr: u16 },
    /// an address of a bit in some byte.
    ///
    /// this is coupled with some memory operand which specifies the byte in question. the usage of
    /// the bit selected by address/bit varies by opcode.
    BitIndex { index: u8 },
    /// a memory access to the address specified by indirect register `Rn`.
    ///
    /// n may only be in the range `[0, 63]`, inclusive. indirect registers are pairs of bytes `n *
    /// 2` and `n * 2 + 1` from zero. for example, indirect register 5 would select the address
    /// formed by the word at memory `0x0a` and `0x0b`.
    IndirectReg { n: u8 },
    /// a memory access to the address specified by indirect register `Rn` plus signed displacement
    /// from register `C`.
    ///
    /// n may only be in the range `[0, 63]`, inclusive. indirect registers are pairs of bytes `n *
    /// 2` and `n * 2 + 1` from zero. for example, indirect register 5 would select the address
    /// formed by the word at memory `0x0a` and `0x0b`.
    IndirectRegPlusC { n: u8 },
    /// a memory access to the address specified by indirect register `R0` plus the signed offset
    /// `off`.
    ///
    /// `off` may only be in the range `[-64, 64]`, inclusive.
    R0Offset { off: i8 },
}

/// an `lc87` instruction's operation.
///
/// instruction descriptions are best referenced from the
/// [`lc87` manual](https://www.onsemi.com/pub/Collateral/ANDLC872H00-D.PDF) for the moment.
#[allow(non_camel_case_types)]
#[derive(Copy, Clone, Hash, PartialEq, Eq)]
pub enum Opcode {
    ADD,
    ADDC,
    ADDDC,
    AND,
    BE,
    BN,
    BNE,
    BNM,
    BNZ,
    BNZW,
    BP,
    BPC,
    BPM,
    BR,
    BZ,
    CALL,
    CLR1,
    CLR1M,
    DBNZ,
    DBZ,
    DEC,
    DECL,
    DECW,
    DIV16,
    DIV24,
    FADD,
    FADDC,
    FADDCW,
    FADDW,
    FAND,
    FANDW,
    FNOR,
    FNORW,
    FOR,
    FORW,
    FSUB,
    FSUBC,
    FSUBCW,
    FSUBW,
    FXOR,
    FXORW,
    INC,
    INCL,
    INCW,
    JMP,
    LD,
    LDCW,
    LDW,
    LDX,
    MOV,
    MUL16,
    MUL24,
    NOP,
    NOT1,
    NOT1M,
    OR,
    POP,
    POPW,
    POP_BA,
    POP_P,
    PUHS_BA,
    PUSH,
    PUSHW,
    PUSH_P,
    RCALL,
    RCALLA,
    RET,
    RETI,
    ROL,
    ROLC,
    ROR,
    RORC,
    SET1,
    SET1M,
    ST,
    STW,
    STX,
    SUB,
    SUBC,
    XCH,
    XCHW,
}

/// an `lc87` instruction decoder.
///
/// there are no decode options for `lc87`, so this is a trivial struct that exists only for the
/// [`yaxpeax_arch::Decoder`] trait impl.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct InstDecoder { }

impl InstDecoder {
    /// decode a slice of bytes into an instruction (or error)
    ///
    /// this is just a higher-level interface to the [`InstDecoder`] impl of
    /// [`yaxpeax_arch::Decoder`].
    pub fn decode_slice(data: &[u8]) -> Result<Instruction, <LC87 as Arch>::DecodeError> {
        use yaxpeax_arch::U8Reader;

        InstDecoder::default()
            .decode(&mut U8Reader::new(data))
    }
}

impl Default for InstDecoder {
    fn default() -> Self {
        InstDecoder { }
    }
}

impl Decoder<LC87> for InstDecoder {
    fn decode_into<T: Reader<<LC87 as Arch>::Address, <LC87 as Arch>::Word>>(&self, inst: &mut Instruction, words: &mut T) -> Result<(), <LC87 as Arch>::DecodeError> {
        inst.length = 0;
        inst.reset_operands();
        words.mark();
        let word = words.next()?;

        use Opcode::*;
        use Operand::*;
        const fn invalid<T>() -> Result<T, StandardDecodeError> {
            Err(StandardDecodeError::InvalidOpcode)
        }

        let low = word & 0x0f;
        if low == 0 {
            const LOW_ZERO_OPCODE_TABLE: [Result<Opcode, StandardDecodeError>; 16] = [
                Ok(NOP),    Ok(RCALLA), Ok(JMP),    Ok(CALL),
                Ok(NOP),    invalid(),  Ok(PUHS_BA),Ok(POP_BA),
                Ok(PUSH_P), Ok(POP_P),  Ok(RET),    Ok(RETI),
                Ok(ROR),    Ok(RORC),   Ok(ROL),    Ok(ROLC),
            ];
            inst.opcode = LOW_ZERO_OPCODE_TABLE[(word as usize) >> 4]?;
            if word == 0x20 || word == 0x30 {
                inst.with_operand(BranchAbsU17 {
                    addr:
                        ((word as u32 & 1) << 16) |
                        ((words.next()? as u32) << 8) |
                        words.next()? as u32
                });
            } else if word == 0x40 {
                let mut selector = words.next()?;
                selector = (selector << 2) | (selector >> 6);
                if selector > 3 {
                    return Err(StandardDecodeError::InvalidOpcode);
                } else {
                    inst.opcode = [DIV16, MUL16, DIV24, MUL24][selector as usize];
                }
            }
        } else if low == 1 {
            const LOW_ONE_OPCODE_TABLE: [Opcode; 16] = [
                BE,     BNE,    JMP,    CALL,
                BNZ,    BNZW,   PUSH,   LDX,
                LD,     STX,    ADD,    ADDDC,
                SUB,    SUBC,   OR,     AND,
            ];
            inst.opcode = LOW_ONE_OPCODE_TABLE[(word as usize) >> 4];
            if word < 0x20 { // word == 0x01 || word == 0x11
                inst.with_operand(ImmU8 { imm: words.next()? });
                inst.with_operand(BranchRelU12 { rel: words.next()? as u16 });
            } else if word < 0x40 { // word == 0x21 || word == 0x31
                inst.with_operand(BranchAbsU17 {
                    addr:
                        ((word as u32 & 1) << 16) |
                        ((words.next()? as u32) << 8) |
                        words.next()? as u32
                });
            } else if word < 0x60 { // word == 0x41 || word == 0x51
                inst.with_operand(BranchRelU12 { rel: words.next()? as u16 });
            } else if word == 0x71 || word == 0x91 {
                inst.with_operand(typical_operand_decode(2, words)?);
            } else {
                inst.with_operand(ImmU8 { imm: words.next()? });
            }
        } else if low <= 6 {
            const LOW_OPCODE_TABLE: [Opcode; 16] = [
                BE,   BNE,  DBNZ, DBZ,
                MOV,  XCH,  PUSH, POP,
                LD,   ST,   ADD,  ADDC,
                SUB,  SUBC, OR,   AND,
            ];

            inst.opcode = LOW_OPCODE_TABLE[(word as usize) >> 4];
            inst.with_operand(typical_operand_decode(word & 7, words)?);
            if inst.opcode == MOV {
                inst.with_operand(ImmU8 { imm: words.next()? });
                let (op_0, op_1) = inst.operands.split_at_mut(1);
                core::mem::swap(&mut op_0[0], &mut op_1[0]);
            }
        } else if low == 7 {
            const LOW_SEVEN_OPCODE_TABLE: [Opcode; 16] = [
                LDW,    STW,    PUSHW,  POPW,
                LDW,    XCHW,   PUSHW,   POPW,
                LDW,    STW,    BPC,    NOT1M,
                BNM,    CLR1M,  BPM,    SET1M,
            ];
            inst.opcode = LOW_SEVEN_OPCODE_TABLE[(word as usize) >> 4];

            if word < 0x40 { // 0x07, 0x17, 0x27, 0x37
                inst.with_operand(typical_operand_decode(2, words)?);
            } else if word < 0x50 { // 0x47
                inst.with_operand(ImmU16 {
                    imm: (words.next()? as u16) | ((words.next()? as u16) << 8)
                })
            } else if word < 0xa0 { // 0x57, 0x67, 0x77, 0x87, 0x97
                inst.with_operand(typical_operand_decode(6, words)?);
            } else {
                let low = words.next()?;
                let high = words.next()?;

                inst.with_operand(AbsU16 { addr: ((high as u16 & 0x3f) << 8) | (low as u16) });
                inst.with_operand(BitIndex { index: high >> 5 });
                let (op_0, op_1) = inst.operands.split_at_mut(1);
                core::mem::swap(&mut op_0[0], &mut op_1[0]);
                if word & 0b0000_0000 == 0 {
                    inst.with_operand(BranchRelU12 { rel: words.next()? as u16 });
                }
            }
        } else { // the upper half of opcode space by low nibble: 0bXXXX_1XXX.
            // there's a batch of opcodes that use the low three bits as operands, another large
            // chunk of instruction space
            let opc_bits = word >> 5;
            const HIGH_OPCODE_TABLE: [Option<Opcode>; 8] = [
                Some(BP),    Some(BN),    Some(RCALL), Some(BR),
                None,        Some(NOT1),  Some(CLR1),  Some(SET1),
            ];
            if let Some(opc) = HIGH_OPCODE_TABLE[opc_bits as usize] {
                inst.opcode = opc;
                if opc_bits == 2 || opc_bits == 3 {
                    inst.with_operand(BranchRelU12 {
                        rel:
                            ((word as u16) & 0b00001_0000) << 7 |
                            ((word as u16) & 0b00000_0111) << 8 |
                            words.next()? as u16
                    });
                } else {
                    let mut addr = words.next()? as u16;
                    if word & 0b0001_0000 != 0 {
                        addr += 0xfe00;
                    }
                    inst.with_operand(AbsU16 { addr });
                    inst.with_operand(BitIndex { index: word & 7 });

                    if word < 0x40 {
                        inst.with_operand(BranchRelU12 { rel: words.next()? as u16 });
                    }
                }
            } else {
                if word < 0x90 {
                    if word < 0x89 {
                        inst.opcode = LDCW;
                        inst.with_operand(typical_operand_decode(2, words)?);
                    } else if word < 0x8a {
                        inst.opcode = BZ;
                        inst.with_operand(BranchRelU12 { rel: words.next()? as u16 });
                    } else if word < 0x8e {
                        inst.opcode = INC;
                        inst.with_operand(typical_operand_decode(word & 7, words)?);
                    } else if word < 0x8f {
                        inst.opcode = INCL;
                        inst.with_operand(typical_operand_decode(6, words)?);
                    } else {
                        inst.opcode = INCW;
                        inst.with_operand(typical_operand_decode(word & 7, words)?);
                    }
                } else {
                    if word < 0x99 {
                        const OPC_98_TABLE: [Opcode; 16] = [
                            FADD,   FADDC,  FSUB,   FSUBC,
                            FNOR,   FAND,   FOR,    FXOR,
                            FADDW,  FADDCW, FSUBW,  FSUBCW,
                            FNORW,  FANDW,  FORW,   FXORW,
                        ];
                        let word = words.next()? as usize;
                        let word = (word >> 4) | (word << 4);
                        if word >= 16 {
                            return Err(StandardDecodeError::InvalidOpcode);
                        }
                        inst.opcode = OPC_98_TABLE[word as usize];
                    } else if word < 0x9a {
                        inst.opcode = BNZ;
                        inst.with_operand(BranchRelU12 { rel: words.next()? as u16 });
                    } else if word < 0x9e {
                        inst.opcode = DEC;
                        inst.with_operand(typical_operand_decode(word & 7, words)?);
                    } else if word < 0x9f {
                        inst.opcode = DECL;
                        inst.with_operand(typical_operand_decode(6, words)?);
                    } else {
                        inst.opcode = DECW;
                        inst.with_operand(typical_operand_decode(word & 7, words)?);
                    }
                }
            }
        }

        inst.length = words.offset() as u8;
        Ok(())
    }
}

fn typical_operand_decode<T: Reader<<LC87 as Arch>::Address, <LC87 as Arch>::Word>>(operand_kind: u8, words: &mut T) -> Result<Operand, <LC87 as Arch>::DecodeError> {
    // all of these are at least one additional word..
    let operand = words.next()?;

    match operand_kind {
        2 => {
            if operand < 0x80 {
                if operand & 1 == 0 {
                    Ok(Operand::IndirectReg { n: (operand >> 1) & 0x3f })
                } else {
                    Ok(Operand::IndirectRegPlusC { n: (operand >> 1) & 0x3f })
                }
            } else {
                Ok(Operand::R0Offset { off: (((operand & 0x7f) as i8) << 1) >> 1 })
            }
        }
        3 => {
            Ok(Operand::AbsU16 { addr: operand as u16 + 0xfe00 })
        }
        4 => {
            Ok(Operand::AbsU16 { addr: operand as u16 })
        }
        5 => {
            Ok(Operand::AbsU16 { addr: operand as u16 + 0x100 })
        }
        6 => {
            let high = words.next()?;
            Ok(Operand::AbsU16 { addr: operand as u16 | ((high as u16) << 8) })
        }
        _ => {
            unreachable!()
        }
    }
}
