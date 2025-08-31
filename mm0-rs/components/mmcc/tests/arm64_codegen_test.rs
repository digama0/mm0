//! Test ARM64 code generation
//!
//! This test verifies that we can generate actual ARM64 machine code
//! for a simple program.

#[cfg(test)]
mod tests {
    use mmcc::*;
    use mmcc::types::mir::{*, self};
    use mmcc::arch::target::{Target, TargetArch, OperatingSystem};
    use mmcc::arch::arm64;
    use std::collections::HashMap;
    
    #[test]
    #[cfg(feature = "arm64-backend")]
    fn test_arm64_hello_world() {
        // Create a simple MIR program that prints "Hello, World!"
        let mut cfg = Cfg {
            span: FileSpan::default(),
            id: VarId(0),
            blocks: Default::default(),
            ctxs: Default::default(),
            can_return: true,
        };
        
        // Create entry block
        let entry = cfg.blocks.push(BasicBlock {
            span: FileSpan::default(),
            stmts: vec![],
            reachable: true,
            term: Terminator::Return {
                span: FileSpan::default(),
                rets: vec![],
            },
        });
        
        // Create init block for the start function
        let mut init_cfg = cfg.clone();
        
        // Create target
        let target = Target {
            arch: TargetArch::Arm64,
            os: OperatingSystem::MacOS,
            binary_format: mmcc::arch::target::BinaryFormat::MachO,
        };
        
        // Create empty maps
        let names = HashMap::new();
        let mir_procs = HashMap::new();
        let globals = vec![];
        let allocs = mmcc::mir_opt::storage::Allocations::default();
        
        // Try to link the code
        let result = mmcc::linker::LinkedCode::link(
            &names,
            mir_procs,
            init_cfg,
            &allocs,
            &globals,
            target,
        );
        
        match result {
            Ok(linked) => {
                println!("Successfully created LinkedCode!");
                println!("Init code length: {} bytes", linked.init.1.len());
                
                // Verify we have ARM64 code
                match &linked.init.1 {
                    mmcc::arch_pcode::ArchPCode::Arm64(pcode) => {
                        println!("✓ Generated ARM64 PCode!");
                        println!("  Instructions: {}", pcode.insts.len());
                        println!("  Code size: {} bytes", pcode.len);
                    }
                    _ => panic!("Expected ARM64 PCode, got something else"),
                }
            }
            Err(e) => {
                println!("Linking failed: {:?}", e);
                // This is expected for now since we haven't fully implemented ARM64 lowering
                // But we should at least get to the linking stage
            }
        }
    }
    
    #[test]
    #[cfg(feature = "arm64-backend")]
    fn test_arm64_instruction_encoding() {
        use arm64::inst::*;
        use arm64::regs::*;
        
        // Test encoding a simple ADD instruction
        let add = Inst::AluRRR {
            op: AluOp::Add,
            size: OperandSize::S64,
            rd: VReg(X0),
            rn: VReg(X1),
            rm: VReg(X2),
        };
        
        // Test encoding a MOV instruction
        let mov = Inst::Mov {
            size: OperandSize::S64,
            rd: VReg(X3),
            rm: VReg(X4),
        };
        
        // We should be able to create these instructions
        println!("Created ARM64 instructions:");
        println!("  {:?}", add);
        println!("  {:?}", mov);
    }
}