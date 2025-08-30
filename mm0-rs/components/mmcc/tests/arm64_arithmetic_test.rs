//! Tests for ARM64 arithmetic instruction encoding

use mmcc::arch::arm64::{
    PInst, OperandSize, POperand, PReg, X0, X1, X2, X3, X4, X5,
};
use mmcc::arch::traits::{InstructionSink, PhysicalInstruction};

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
fn test_arm64_add_immediate() {
    let mut sink = TestSink { bytes: vec![] };
    
    // ADD X0, X1, #42
    let inst = PInst::Add {
        dst: X0,
        src1: X1,
        src2: POperand::Imm(42),
        size: OperandSize::Size64,
    };
    
    inst.encode(&mut sink).unwrap();
    
    // Expected encoding: 0x91010a20
    // ADD X0, X1, #42 => 1001 0001 0000 0001 0000 1010 0010 0000
    //                   = 91 01 0a 20 (little endian)
    assert_eq!(sink.bytes, vec![0x20, 0x0a, 0x01, 0x91]);
}

#[test]
fn test_arm64_add_register() {
    let mut sink = TestSink { bytes: vec![] };
    
    // ADD X0, X1, X2
    let inst = PInst::Add {
        dst: X0,
        src1: X1,
        src2: POperand::Reg(X2),
        size: OperandSize::Size64,
    };
    
    inst.encode(&mut sink).unwrap();
    
    // Expected encoding: 0x8b020020
    // ADD X0, X1, X2 => 1000 1011 0000 0010 0000 0000 0010 0000
    //                 = 8b 02 00 20 (little endian)
    assert_eq!(sink.bytes, vec![0x20, 0x00, 0x02, 0x8b]);
}

#[test]
fn test_arm64_sub_immediate() {
    let mut sink = TestSink { bytes: vec![] };
    
    // SUB X3, X4, #100
    let inst = PInst::Sub {
        dst: X3,
        src1: X4,
        src2: POperand::Imm(100),
        size: OperandSize::Size64,
    };
    
    inst.encode(&mut sink).unwrap();
    
    // Expected encoding: 0xd1019083
    // SUB X3, X4, #100 => 1101 0001 0000 0001 1001 0000 1000 0011
    //                   = d1 01 90 83 (little endian)
    assert_eq!(sink.bytes, vec![0x83, 0x90, 0x01, 0xd1]);
}

#[test]
fn test_arm64_mul() {
    let mut sink = TestSink { bytes: vec![] };
    
    // MUL X0, X1, X2
    let inst = PInst::Mul {
        dst: X0,
        src1: X1,
        src2: X2,
        size: OperandSize::Size64,
    };
    
    inst.encode(&mut sink).unwrap();
    
    // Expected encoding: 0x9b027c20
    // MADD X0, X1, X2, XZR => 1001 1011 0000 0010 0111 1100 0010 0000
    //                       = 9b 02 7c 20 (little endian)
    assert_eq!(sink.bytes, vec![0x20, 0x7c, 0x02, 0x9b]);
}

#[test]
fn test_arm64_sdiv() {
    let mut sink = TestSink { bytes: vec![] };
    
    // SDIV X5, X3, X4
    let inst = PInst::Sdiv {
        dst: X5,
        src1: X3,
        src2: X4,
        size: OperandSize::Size64,
    };
    
    inst.encode(&mut sink).unwrap();
    
    // Expected encoding: 0x9ac40c65
    // SDIV X5, X3, X4 => 1001 1010 1100 0100 0000 1100 0110 0101
    //                  = 9a c4 0c 65 (little endian)
    assert_eq!(sink.bytes, vec![0x65, 0x0c, 0xc4, 0x9a]);
}

#[test]
fn test_arm64_cmp_register() {
    let mut sink = TestSink { bytes: vec![] };
    
    // CMP X1, X2
    let inst = PInst::Cmp {
        lhs: X1,
        rhs: POperand::Reg(X2),
        size: OperandSize::Size64,
    };
    
    inst.encode(&mut sink).unwrap();
    
    // Expected encoding: 0xeb02003f
    // SUBS XZR, X1, X2 => 1110 1011 0000 0010 0000 0000 0011 1111
    //                   = eb 02 00 3f (little endian)
    assert_eq!(sink.bytes, vec![0x3f, 0x00, 0x02, 0xeb]);
}

#[test]
fn test_arm64_cmp_immediate() {
    let mut sink = TestSink { bytes: vec![] };
    
    // CMP X0, #0
    let inst = PInst::Cmp {
        lhs: X0,
        rhs: POperand::Imm(0),
        size: OperandSize::Size64,
    };
    
    inst.encode(&mut sink).unwrap();
    
    // Expected encoding: 0xf100001f
    // SUBS XZR, X0, #0 => 1111 0001 0000 0000 0000 0000 0001 1111
    //                   = f1 00 00 1f (little endian)
    assert_eq!(sink.bytes, vec![0x1f, 0x00, 0x00, 0xf1]);
}

#[test]
fn test_arm64_simple_calculator_sequence() {
    // Test a simple calculation: (10 + 5) * 3 - 2
    let mut sink = TestSink { bytes: vec![] };
    
    let instructions = vec![
        // MOV X0, #10
        PInst::MovImm {
            dst: X0,
            imm: 10,
            size: OperandSize::Size64,
        },
        // MOV X1, #5
        PInst::MovImm {
            dst: X1,
            imm: 5,
            size: OperandSize::Size64,
        },
        // ADD X2, X0, X1  (X2 = 10 + 5 = 15)
        PInst::Add {
            dst: X2,
            src1: X0,
            src2: POperand::Reg(X1),
            size: OperandSize::Size64,
        },
        // MOV X3, #3
        PInst::MovImm {
            dst: X3,
            imm: 3,
            size: OperandSize::Size64,
        },
        // MUL X4, X2, X3  (X4 = 15 * 3 = 45)
        PInst::Mul {
            dst: X4,
            src1: X2,
            src2: X3,
            size: OperandSize::Size64,
        },
        // SUB X5, X4, #2  (X5 = 45 - 2 = 43)
        PInst::Sub {
            dst: X5,
            src1: X4,
            src2: POperand::Imm(2),
            size: OperandSize::Size64,
        },
        // MOV X0, X5  (return value)
        PInst::Mov {
            dst: X0,
            src: X5,
            size: OperandSize::Size64,
        },
        // RET
        PInst::Ret,
    ];
    
    for inst in instructions {
        inst.encode(&mut sink).unwrap();
    }
    
    // Verify we generated valid ARM64 code
    assert_eq!(sink.bytes.len(), 8 * 4); // 8 instructions, 4 bytes each
    
    // Check the first instruction (MOV X0, #10)
    assert_eq!(&sink.bytes[0..4], &[0x40, 0x01, 0x80, 0xd2]);
    
    // Check the last instruction (RET)
    assert_eq!(&sink.bytes[28..32], &[0xc0, 0x03, 0x5f, 0xd6]);
}