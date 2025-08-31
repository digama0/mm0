//! ARM64 architecture tests

#[cfg(test)]
mod tests {
    use crate::{Compiler, Idx, Symbol, intern};
    use crate::types::{Binop, Size, Spanned, VarId, hir::ProcKind, ast::*};
    use crate::arch::target::{Target, TargetArch, OperatingSystem};
    
    #[test]
    fn test_arm64_simple_exit() {
        let mut compiler = Compiler::new(());
        
        // Set ARM64 target
        compiler.set_target(Target {
            arch: TargetArch::Arm64,
            os: OperatingSystem::MacOS,
        });
        
        // Create a simple main function that exits with code 0
        let main = Spanned::dummy(ItemKind::Proc {
            intrinsic: None,
            kind: ProcKind::Main,
            name: Spanned::dummy(intern("main")),
            tyargs: 0,
            args: Box::new([]),
            outs: Box::new([]),
            rets: Box::new([]),
            variant: None,
            body: Block {
                stmts: vec![],
                expr: None,
            },
        });
        
        compiler.add(&main, Default::default(), ()).unwrap();
        let code = compiler.finish().unwrap();
        
        // Check that we have ARM64 code
        assert_eq!(code.target.arch, TargetArch::Arm64);
        
        // Verify the init code is ARM64
        assert!(code.init.1.with_arm64(|_| true).unwrap_or(false), 
                "Expected ARM64 code but got {:?}", code.init.1.arch());
                
        println!("ARM64 test passed! Generated code for {:?}", code.target);
    }
    
    #[test]
    fn test_arm64_addition() {
        let mut compiler = Compiler::new(());
        
        // Set ARM64 target
        compiler.set_target(Target {
            arch: TargetArch::Arm64,
            os: OperatingSystem::MacOS,
        });
        
        // Create main function that computes 2 + 2 == 4
        let main = Spanned::dummy(ItemKind::Proc {
            intrinsic: None,
            kind: ProcKind::Main,
            name: Spanned::dummy(intern("main")),
            tyargs: 0,
            args: Box::new([]),
            outs: Box::new([]),
            rets: Box::new([]),
            variant: None,
            body: Block {
                stmts: vec![Spanned::dummy(StmtKind::Expr(ExprKind::Assert(
                    Box::new(Spanned::dummy(ExprKind::Binop(Binop::Eq,
                        Box::new(Spanned::dummy(ExprKind::Typed(
                            Box::new(Spanned::dummy(ExprKind::Binop(Binop::Add,
                                Box::new(Spanned::dummy(ExprKind::Int(2.into()))),
                                Box::new(Spanned::dummy(ExprKind::Int(2.into())))
                            ))),
                            Box::new(Spanned::dummy(TypeKind::UInt(Size::S32)))
                        ))),
                        Box::new(Spanned::dummy(ExprKind::Int(4.into())))
                    )))
                )))],
                expr: None,
            },
        });
        
        compiler.add(&main, Default::default(), ()).unwrap();
        let code = compiler.finish().unwrap();
        
        // Check that we have ARM64 code
        assert_eq!(code.target.arch, TargetArch::Arm64);
        
        // Verify the init code is ARM64
        assert!(code.init.1.with_arm64(|_| true).unwrap_or(false), 
                "Expected ARM64 code but got {:?}", code.init.1.arch());
                
        println!("ARM64 addition test passed!");
    }
}