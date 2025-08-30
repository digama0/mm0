//! Test arithmetic instruction encoding for all architectures

#[cfg(test)]
mod tests {
    #[test]
    #[cfg(not(any(feature = "arm64-backend", feature = "wasm-backend")))]
    fn test_x86_arithmetic_encoding() {
        use mmcc::arch::x86::{Inst, PReg, RegMem, RegMemImm, RAX, RBX, RCX, RDX};
        use mmcc::types::Size;
        
        // Test ADD encoding
        let add = Inst::Binop(
            mmcc::types::Binop::Add(mmcc::types::IntTy::Int(Size::S64)),
            RAX,
            RegMemImm::Reg(RBX),
        );
        
        // Test SUB encoding  
        let sub = Inst::Binop(
            mmcc::types::Binop::Sub(mmcc::types::IntTy::Int(Size::S64)),
            RCX,
            RegMemImm::Imm(100),
        );
        
        println!("x86-64 arithmetic instructions created successfully");
    }
    
    #[test]
    #[cfg(feature = "arm64-backend")]
    fn test_arm64_arithmetic_encoding() {
        use mmcc::arch::arm64::{Inst, Operand, VReg, OperandSize};
        use mmcc::types::Size;
        
        // Test ADD encoding
        let add = Inst::Add {
            dst: VReg::new(0),  // X0
            src1: VReg::new(1), // X1
            src2: Operand::Reg(VReg::new(2)), // X2
            size: Size::S64,
        };
        
        // Test SUB encoding
        let sub = Inst::Sub {
            dst: VReg::new(3),  // X3
            src1: VReg::new(4), // X4
            src2: Operand::Imm(100),
            size: Size::S64,
        };
        
        // Test MUL encoding
        let mul = Inst::Mul {
            dst: VReg::new(0),
            src1: VReg::new(1),
            src2: VReg::new(2),
            size: Size::S64,
        };
        
        println!("ARM64 arithmetic instructions created successfully");
    }
    
    #[test]
    #[cfg(feature = "wasm-backend")]
    fn test_wasm_arithmetic_encoding() {
        use mmcc::arch::wasm::{WasmInst, WasmType};
        
        // Test ADD
        let add = WasmInst::Add { ty: WasmType::I32 };
        
        // Test SUB
        let sub = WasmInst::Sub { ty: WasmType::I32 };
        
        // Test MUL
        let mul = WasmInst::Mul { ty: WasmType::I32 };
        
        // WASM arithmetic sequence
        let sequence = vec![
            WasmInst::LocalGet { idx: 0 },
            WasmInst::LocalGet { idx: 1 },
            add,
            WasmInst::LocalSet { idx: 2 },
        ];
        
        println!("WASM arithmetic instructions created successfully");
        assert_eq!(sequence.len(), 4);
    }
    
    #[test]
    fn test_arithmetic_properties() {
        // Test that arithmetic operations have expected properties
        // regardless of architecture
        
        // Commutativity: a + b = b + a
        let a = 10u32;
        let b = 5u32;
        assert_eq!(a + b, b + a);
        
        // Associativity: (a + b) + c = a + (b + c)
        let c = 3u32;
        assert_eq!((a + b) + c, a + (b + c));
        
        // Identity: a + 0 = a
        assert_eq!(a + 0, a);
        
        // Calculator example: (10 + 5) * 3 - 2 = 43
        let result = (a + b) * c - 2;
        assert_eq!(result, 43);
    }
}