//! ARM64 instruction encoding
//!
//! ARM64 uses fixed-width 32-bit instructions, which is simpler than x86's
//! variable-length encoding but requires different strategies for large constants.

use crate::arch::traits::{PhysicalInstruction, InstructionSink, EncodeError};
use super::{PInst, PReg, POperand, PAMode, Cond, OperandSize};

impl PhysicalInstruction for PInst {
    fn encode(&self, sink: &mut impl InstructionSink) -> Result<(), EncodeError> {
        use PInst::*;
        
        match self {
            Fallthrough { .. } => {
                // No code emitted for fallthrough
                Ok(())
            }
            
            // MOV between registers
            Mov { dst, src, size } => {
                // MOV is encoded as ORR with zero register
                // ORR Xd, XZR, Xm  or  ORR Wd, WZR, Wm
                let sf = match size {
                    OperandSize::Size64 => 1,
                    OperandSize::Size32 => 0,
                };
                
                let insn = 0b0_10_10001_00_0 << 21  // ORR (shifted register)
                    | (sf << 31)                      // 64-bit = 1, 32-bit = 0
                    | (src.index() as u32) << 16      // Rm
                    | (0b11111) << 5                  // Rn = XZR/WZR
                    | (dst.index() as u32);           // Rd
                    
                sink.emit_bytes(&insn.to_le_bytes());
                Ok(())
            }
            
            // Load immediate
            MovImm { dst, imm, size } => {
                encode_mov_imm(sink, *dst, *imm, *size)
            }
            
            // Arithmetic operations
            Add { dst, src1, src2, size } => {
                encode_arithmetic(sink, ArithOp::Add, *dst, *src1, src2, *size)
            }
            
            Sub { dst, src1, src2, size } => {
                encode_arithmetic(sink, ArithOp::Sub, *dst, *src1, src2, *size)
            }
            
            // Multiplication
            Mul { dst, src1, src2, size } => {
                // MADD Xd, Xn, Xm, XZR (multiply-add with zero)
                let sf = match size {
                    OperandSize::Size32 => 0,
                    OperandSize::Size64 => 1,
                };
                let insn = (sf << 31) | 0x1b000000u32
                    | ((src2.index() as u32) << 16)
                    | (0x1f << 10) // XZR
                    | ((src1.index() as u32) << 5)
                    | (dst.index() as u32);
                sink.emit_bytes(&insn.to_le_bytes());
                Ok(())
            }
            
            // Signed division
            Sdiv { dst, src1, src2, size } => {
                // SDIV Xd, Xn, Xm
                let sf = match size {
                    OperandSize::Size32 => 0,
                    OperandSize::Size64 => 1,
                };
                let insn = (sf << 31) | 0x1ac00c00u32
                    | ((src2.index() as u32) << 16)
                    | ((src1.index() as u32) << 5)
                    | (dst.index() as u32);
                sink.emit_bytes(&insn.to_le_bytes());
                Ok(())
            }
            
            // Unsigned division
            Udiv { dst, src1, src2, size } => {
                // UDIV Xd, Xn, Xm
                let sf = match size {
                    OperandSize::Size32 => 0,
                    OperandSize::Size64 => 1,
                };
                let insn = (sf << 31) | 0x1ac00800u32
                    | ((src2.index() as u32) << 16)
                    | ((src1.index() as u32) << 5)
                    | (dst.index() as u32);
                sink.emit_bytes(&insn.to_le_bytes());
                Ok(())
            }
            
            // Comparison
            Cmp { lhs, rhs, size } => {
                // CMP is SUB with discarded result (Rd = XZR)
                let sf = match size {
                    OperandSize::Size32 => 0,
                    OperandSize::Size64 => 1,
                };
                match rhs {
                    POperand::Reg(rm) => {
                        // SUBS XZR, Xn, Xm
                        let insn = (sf << 31) | 0x6b000000u32 | 0x1f // XZR as dst
                            | ((rm.index() as u32) << 16)
                            | ((lhs.index() as u32) << 5);
                        sink.emit_bytes(&insn.to_le_bytes());
                    }
                    POperand::Imm(imm) => {
                        // SUBS XZR, Xn, #imm
                        if *imm <= 0xfff {
                            let insn = (sf << 31) | 0x71000000u32 | 0x1f // XZR as dst
                                | ((*imm as u32) << 10)
                                | ((lhs.index() as u32) << 5);
                            sink.emit_bytes(&insn.to_le_bytes());
                        } else {
                            return Err(EncodeError::InvalidFormat(
                                format!("CMP immediate {} out of range", imm)
                            ));
                        }
                    }
                }
                Ok(())
            }
            
            // Return instruction
            Ret => {
                // RET = 0xd65f03c0 (return using LR/X30)
                sink.emit_bytes(&0xd65f03c0u32.to_le_bytes());
                Ok(())
            }
            
            // System call
            Svc { imm } => {
                // SVC #imm
                let insn = 0xd4000001u32 | ((*imm as u32 & 0xffff) << 5);
                sink.emit_bytes(&insn.to_le_bytes());
                Ok(())
            }
            
            // Load address (PC-relative)
            Adr { dst, offset } => {
                // ADR Xd, #offset
                // offset is in range +/- 1MB (21-bit signed)
                if *offset < -(1 << 20) || *offset >= (1 << 20) {
                    return Err(EncodeError::InvalidFormat(
                        format!("ADR offset {} out of range", offset)
                    ));
                }
                
                let imm_lo = (*offset & 0x3) as u32;
                let imm_hi = ((*offset >> 2) & 0x7ffff) as u32;
                
                let insn = 0x10000000u32  // ADR opcode
                    | (imm_lo << 29)
                    | (imm_hi << 5)
                    | (dst.index() as u32);
                    
                sink.emit_bytes(&insn.to_le_bytes());
                Ok()
            }
            
            // Branch instructions
            Bl { offset } => {
                // BL (Branch with Link)
                // offset is in range +/- 128MB (26-bit signed * 4)
                if *offset < -(1 << 27) || *offset >= (1 << 27) {
                    return Err(EncodeError::InvalidFormat(
                        format!("BL offset {} out of range", offset)
                    ));
                }
                
                let imm26 = ((*offset >> 2) & 0x3ffffff) as u32;
                let insn = 0x94000000u32 | imm26;
                sink.emit_bytes(&insn.to_le_bytes());
                Ok(())
            }
            
            _ => Err(EncodeError::NotImplemented("instruction encoding")),
        }
    }
}

/// Arithmetic operation types
enum ArithOp {
    Add,
    Sub,
}

/// Encode arithmetic operation (ADD/SUB)
fn encode_arithmetic(
    sink: &mut impl InstructionSink,
    op: ArithOp,
    dst: PReg,
    src1: PReg,
    src2: &POperand,
    size: OperandSize,
) -> Result<(), EncodeError> {
    match src2 {
        POperand::Reg(src2_reg) => {
            // Register form: ADD Xd, Xn, Xm
            let sf = match size {
                OperandSize::Size64 => 1,
                OperandSize::Size32 => 0,
            };
            
            let opc = match op {
                ArithOp::Add => 0b00,
                ArithOp::Sub => 0b10,
            };
            
            let insn = (sf << 31)
                | (opc << 29)
                | (0b01011 << 24)
                | (0b00_0 << 21)           // shift type = LSL, amount = 0
                | (src2_reg.index() as u32) << 16
                | (src1.index() as u32) << 5
                | (dst.index() as u32);
                
            sink.emit_bytes(&insn.to_le_bytes());
            Ok(())
        }
        
        POperand::Imm(imm) => {
            // Immediate form: ADD Xd, Xn, #imm
            encode_arithmetic_imm(sink, op, dst, src1, *imm, size)
        }
    }
}

/// Encode arithmetic with immediate
fn encode_arithmetic_imm(
    sink: &mut impl InstructionSink,
    op: ArithOp,
    dst: PReg,
    src: PReg,
    imm: u64,
    size: OperandSize,
) -> Result<(), EncodeError> {
    // Check if immediate fits in 12 bits
    if imm > 0xfff {
        return Err(EncodeError::InvalidFormat(
            format!("Immediate {} too large for ADD/SUB", imm)
        ));
    }
    
    let sf = match size {
        OperandSize::Size64 => 1,
        OperandSize::Size32 => 0,
    };
    
    let opc = match op {
        ArithOp::Add => 0b00,
        ArithOp::Sub => 0b01,
    };
    
    let insn = (sf << 31)
        | (opc << 29)
        | (0b10001 << 24)
        | ((imm as u32 & 0xfff) << 10)
        | (src.index() as u32) << 5
        | (dst.index() as u32);
        
    sink.emit_bytes(&insn.to_le_bytes());
    Ok(())
}

/// Encode MOV immediate
fn encode_mov_imm(
    sink: &mut impl InstructionSink,
    dst: PReg,
    imm: u64,
    size: OperandSize,
) -> Result<(), EncodeError> {
    // For now, use MOVZ (move with zero) for small positive constants
    // TODO: Handle larger constants with MOVK sequences
    
    match size {
        OperandSize::Size32 => {
            if imm > 0xffff {
                return Err(EncodeError::NotImplemented("large immediate"));
            }
            
            // MOVZ Wd, #imm16
            let insn = 0b0_10_100101_00 << 21
                | ((imm as u32 & 0xffff) << 5)
                | (dst.index() as u32);
                
            sink.emit_bytes(&insn.to_le_bytes());
            Ok(())
        }
        
        OperandSize::Size64 => {
            if imm > 0xffff {
                // For larger values, we'd need multiple instructions
                // For now, just handle 16-bit values
                return Err(EncodeError::NotImplemented("large 64-bit immediate"));
            }
            
            // MOVZ Xd, #imm16
            let insn = 0b1_10_100101_00 << 21  // sf=1 for 64-bit
                | ((imm as u32 & 0xffff) << 5)
                | (dst.index() as u32);
                
            sink.emit_bytes(&insn.to_le_bytes());
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arch::arm64::{X0, X1, X2, X16};
    
    struct TestSink {
        bytes: Vec<u8>,
    }
    
    impl InstructionSink for TestSink {
        fn emit_bytes(&mut self, bytes: &[u8]) {
            self.bytes.extend_from_slice(bytes);
        }
        
        fn offset(&self) -> usize {
            self.bytes.len()
        }
    }
    
    #[test]
    fn test_ret_encoding() {
        let mut sink = TestSink { bytes: vec![] };
        let inst = PInst::Ret;
        inst.encode(&mut sink).unwrap();
        
        assert_eq!(sink.bytes, vec![0xc0, 0x03, 0x5f, 0xd6]);
    }
    
    #[test]
    fn test_mov_reg_encoding() {
        let mut sink = TestSink { bytes: vec![] };
        let inst = PInst::Mov {
            dst: X0,
            src: X1,
            size: OperandSize::Size64,
        };
        inst.encode(&mut sink).unwrap();
        
        // ORR X0, XZR, X1
        // Expected: 0xaa0103e0
        assert_eq!(sink.bytes, vec![0xe0, 0x03, 0x01, 0xaa]);
    }
    
    #[test]
    fn test_arm64_exit_42() {
        let mut sink = TestSink { bytes: vec![] };
        
        // mov w0, #42
        let mov_inst = PInst::MovImm {
            dst: X0,
            imm: 42,
            size: OperandSize::Size32,
        };
        mov_inst.encode(&mut sink).unwrap();
        
        // mov x16, #1 (exit syscall)
        let syscall_inst = PInst::MovImm {
            dst: X16,
            imm: 1,
            size: OperandSize::Size64,
        };
        syscall_inst.encode(&mut sink).unwrap();
        
        // svc #0
        let svc_inst = PInst::Svc { imm: 0 };
        svc_inst.encode(&mut sink).unwrap();
        
        // Check generated code matches expected
        let expected = vec![
            0x40, 0x05, 0x80, 0x52, // mov w0, #42
            0x30, 0x00, 0x80, 0xd2, // mov x16, #1
            0x01, 0x00, 0x00, 0xd4, // svc #0
        ];
        
        assert_eq!(sink.bytes, expected);
        println!("ARM64 exit(42) code generation successful!");
    }
}