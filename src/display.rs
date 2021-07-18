use core::fmt;

impl fmt::Display for crate::Instruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.opcode)?;
        for i in 0..self.operand_count {
            f.write_str(" ")?;
            write!(f, "{:?}", self.operands[i as usize])?;
            if i + 1 < self.operand_count {
                f.write_str(",")?;
            }
        }
        Ok(())
    }
}

impl fmt::Debug for crate::Operand {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        <crate::Operand as fmt::Display>::fmt(self, f)
    }
}

impl fmt::Display for crate::Operand {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use crate::Operand::*;
        match self {
            Nothing => { Ok(()) },
            BranchAbsU17 { addr } => {
                if addr < &10 {
                    write!(f, "{}", addr)
                } else {
                    write!(f, "0x{:x}", addr)
                }
            }
            BranchRelU12 { rel } => {
                if rel < &10 {
                    write!(f, "$+{}", rel)
                } else {
                    write!(f, "$+0x{:x}", rel)
                }
            }
            ImmU8 { imm } => {
                write!(f, "#{:02x}h", imm)
            }
            ImmU16 { imm } => {
                write!(f, "#{:04x}h", imm)
            }
            AbsU16 { addr } => {
                write!(f, "{:04x}h", addr)
            }
            BitIndex { index } => {
                write!(f, "{}", index)
            }
            IndirectReg { n } => {
                write!(f, "[R{}]", n)
            }
            IndirectRegPlusC { n } => {
                write!(f, "[R{}, C]", n)
            }
            R0Offset { off } => {
                if off < &10 {
                    write!(f, "[{}]", off)
                } else {
                    write!(f, "[{:x}h]", off)
                }
            }
        }
    }
}

impl fmt::Debug for crate::Opcode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        <crate::Opcode as fmt::Display>::fmt(self, f)
    }
}

impl fmt::Display for crate::Opcode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use crate::Opcode::*;
        match self {
            ADD => f.write_str("add"),
            ADDC => f.write_str("addc"),
            ADDDC => f.write_str("adddc"),
            AND => f.write_str("and"),
            BE => f.write_str("be"),
            BN => f.write_str("bn"),
            BNE => f.write_str("bne"),
            BNM => f.write_str("bnm"),
            BNZ => f.write_str("bnz"),
            BNZW => f.write_str("bnzw"),
            BP => f.write_str("bp"),
            BPC => f.write_str("bpc"),
            BPM => f.write_str("bpm"),
            BR => f.write_str("br"),
            BZ => f.write_str("bz"),
            CALL => f.write_str("call"),
            CLR1 => f.write_str("clr1"),
            CLR1M => f.write_str("clr1m"),
            DBNZ => f.write_str("dbnz"),
            DBZ => f.write_str("dbz"),
            DEC => f.write_str("dec"),
            DECL => f.write_str("decl"),
            DECW => f.write_str("decw"),
            DIV16 => f.write_str("div16"),
            DIV24 => f.write_str("div24"),
            FADD => f.write_str("fadd"),
            FADDC => f.write_str("faddc"),
            FADDCW => f.write_str("faddcw"),
            FADDW => f.write_str("faddw"),
            FAND => f.write_str("fand"),
            FANDW => f.write_str("fandw"),
            FNOR => f.write_str("fnor"),
            FNORW => f.write_str("fnorw"),
            FOR => f.write_str("for"),
            FORW => f.write_str("forw"),
            FSUB => f.write_str("fsub"),
            FSUBC => f.write_str("fsubc"),
            FSUBCW => f.write_str("fsubcw"),
            FSUBW => f.write_str("fsubw"),
            FXOR => f.write_str("fxor"),
            FXORW => f.write_str("fxorw"),
            INC => f.write_str("inc"),
            INCL => f.write_str("incl"),
            INCW => f.write_str("incw"),
            JMP => f.write_str("jmp"),
            LD => f.write_str("ld"),
            LDCW => f.write_str("ldcw"),
            LDW => f.write_str("ldw"),
            LDX => f.write_str("ldx"),
            MOV => f.write_str("mov"),
            MUL16 => f.write_str("mul16"),
            MUL24 => f.write_str("mul24"),
            NOP => f.write_str("nop"),
            NOT1 => f.write_str("not1"),
            NOT1M => f.write_str("not1m"),
            OR => f.write_str("or"),
            POP => f.write_str("pop"),
            POPW => f.write_str("popw"),
            POP_BA => f.write_str("pop_ba"),
            POP_P => f.write_str("pop_p"),
            PUHS_BA => f.write_str("puhs_ba"),
            PUSH => f.write_str("push"),
            PUSHW => f.write_str("pushw"),
            PUSH_P => f.write_str("push_p"),
            RCALL => f.write_str("rcall"),
            RCALLA => f.write_str("rcalla"),
            RET => f.write_str("ret"),
            RETI => f.write_str("reti"),
            ROL => f.write_str("rol"),
            ROLC => f.write_str("rolc"),
            ROR => f.write_str("ror"),
            RORC => f.write_str("rorc"),
            SET1 => f.write_str("set1"),
            SET1M => f.write_str("set1m"),
            ST => f.write_str("st"),
            STW => f.write_str("stw"),
            STX => f.write_str("stx"),
            SUB => f.write_str("sub"),
            SUBC => f.write_str("subc"),
            XCH => f.write_str("xch"),
            XCHW => f.write_str("xchw"),
        }
    }
}
