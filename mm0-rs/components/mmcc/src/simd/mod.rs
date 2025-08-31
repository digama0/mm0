//! Unified SIMD abstraction layer
//! 
//! This module provides a unified interface for SIMD operations across
//! x86-64 (SSE), ARM64 (NEON), and WebAssembly (SIMD128).

use crate::types::mir::{SimdTy, SimdOp};
#[cfg(not(any(feature = "arm64-backend", feature = "wasm-backend")))]
use crate::arch::x86;
#[cfg(feature = "arm64-backend")]
use crate::arch::arm64;
#[cfg(feature = "wasm-backend")]
use crate::arch::wasm;
use crate::types::vcode::{VCode, Inst as VInst, VReg};

/// Architecture-specific SIMD lowering
pub trait SimdLowering {
    /// Lower a SIMD operation to architecture-specific instructions
    fn lower_simd_op(
        &mut self,
        op: &SimdOp,
        dst: VReg,
        args: &[VReg],
    ) -> Result<(), String>;
}

/// x86-64 SSE lowering
#[cfg(not(any(feature = "arm64-backend", feature = "wasm-backend")))]
impl SimdLowering for VCode<x86::Inst> {
    fn lower_simd_op(
        &mut self,
        op: &SimdOp,
        dst: VReg,
        args: &[VReg],
    ) -> Result<(), String> {
        use x86::Inst;
        
        match op {
            // Load/Store operations
            SimdOp::Load(SimdTy::V128) => {
                if args.len() != 1 {
                    return Err("SIMD load expects 1 argument".into());
                }
                // For now, assume args[0] contains the address in a general register
                // In practice, we'd need to construct an Amode from the address
                self.emit(Inst::Movups { 
                    dst, 
                    src: x86::RegMem::Reg(args[0]) // Simplified for now
                });
            }
            
            SimdOp::Store(SimdTy::V128) => {
                if args.len() != 2 {
                    return Err("SIMD store expects 2 arguments".into());
                }
                // args[0] = address, args[1] = value
                // Simplified - in practice need proper Amode construction
                unimplemented!("SIMD store needs proper Amode support");
            }
            
            // Arithmetic operations
            SimdOp::Add(SimdTy::V4F32) => {
                if args.len() != 2 {
                    return Err("SIMD add expects 2 arguments".into());
                }
                self.emit(Inst::Addps {
                    dst,
                    src1: args[0],
                    src2: x86::RegMem::Reg(args[1]),
                });
            }
            
            SimdOp::Sub(SimdTy::V4F32) => {
                if args.len() != 2 {
                    return Err("SIMD sub expects 2 arguments".into());
                }
                self.emit(Inst::Subps {
                    dst,
                    src1: args[0],
                    src2: x86::RegMem::Reg(args[1]),
                });
            }
            
            SimdOp::Mul(SimdTy::V4F32) => {
                if args.len() != 2 {
                    return Err("SIMD mul expects 2 arguments".into());
                }
                self.emit(Inst::Mulps {
                    dst,
                    src1: args[0],
                    src2: x86::RegMem::Reg(args[1]),
                });
            }
            
            SimdOp::Div(SimdTy::V4F32) => {
                if args.len() != 2 {
                    return Err("SIMD div expects 2 arguments".into());
                }
                self.emit(Inst::Divps {
                    dst,
                    src1: args[0],
                    src2: x86::RegMem::Reg(args[1]),
                });
            }
            
            // Integer operations
            SimdOp::Add(SimdTy::V4I32) => {
                if args.len() != 2 {
                    return Err("SIMD add expects 2 arguments".into());
                }
                self.emit(Inst::Paddd {
                    dst,
                    src1: args[0],
                    src2: x86::RegMem::Reg(args[1]),
                });
            }
            
            SimdOp::Sub(SimdTy::V4I32) => {
                if args.len() != 2 {
                    return Err("SIMD sub expects 2 arguments".into());
                }
                self.emit(Inst::Psubd {
                    dst,
                    src1: args[0],
                    src2: x86::RegMem::Reg(args[1]),
                });
            }
            
            SimdOp::Mul(SimdTy::V4I32) => {
                if args.len() != 2 {
                    return Err("SIMD mul expects 2 arguments".into());
                }
                self.emit(Inst::Pmulld {
                    dst,
                    src1: args[0],
                    src2: x86::RegMem::Reg(args[1]),
                });
            }
            
            // Comparisons
            SimdOp::Eq(SimdTy::V4F32) => {
                if args.len() != 2 {
                    return Err("SIMD eq expects 2 arguments".into());
                }
                self.emit(Inst::Cmpeqps {
                    dst,
                    src1: args[0],
                    src2: x86::RegMem::Reg(args[1]),
                });
            }
            
            SimdOp::Lt(SimdTy::V4F32) => {
                if args.len() != 2 {
                    return Err("SIMD lt expects 2 arguments".into());
                }
                self.emit(Inst::Cmpltps {
                    dst,
                    src1: args[0],
                    src2: x86::RegMem::Reg(args[1]),
                });
            }
            
            SimdOp::Le(SimdTy::V4F32) => {
                if args.len() != 2 {
                    return Err("SIMD le expects 2 arguments".into());
                }
                self.emit(Inst::Cmpleps {
                    dst,
                    src1: args[0],
                    src2: x86::RegMem::Reg(args[1]),
                });
            }
            
            SimdOp::Eq(SimdTy::V4I32) => {
                if args.len() != 2 {
                    return Err("SIMD eq expects 2 arguments".into());
                }
                self.emit(Inst::Pcmpeqd {
                    dst,
                    src1: args[0],
                    src2: x86::RegMem::Reg(args[1]),
                });
            }
            
            SimdOp::Gt(SimdTy::V4I32) => {
                if args.len() != 2 {
                    return Err("SIMD gt expects 2 arguments".into());
                }
                self.emit(Inst::Pcmpgtd {
                    dst,
                    src1: args[0],
                    src2: x86::RegMem::Reg(args[1]),
                });
            }
            
            // Shuffle operations
            SimdOp::Shuffle { imm } => {
                if args.len() != 2 {
                    return Err("SIMD shuffle expects 2 arguments".into());
                }
                self.emit(Inst::Shufps {
                    dst,
                    src1: args[0],
                    src2: x86::RegMem::Reg(args[1]),
                    imm: *imm,
                });
            }
            
            // Conversions
            SimdOp::CvtI32ToF32 => {
                if args.len() != 1 {
                    return Err("SIMD cvt expects 1 argument".into());
                }
                self.emit(Inst::Cvtdq2ps {
                    dst,
                    src: x86::RegMem::Reg(args[0]),
                });
            }
            
            SimdOp::CvtF32ToI32 => {
                if args.len() != 1 {
                    return Err("SIMD cvt expects 1 argument".into());
                }
                self.emit(Inst::Cvtps2dq {
                    dst,
                    src: x86::RegMem::Reg(args[0]),
                });
            }
            
            // Horizontal operations
            SimdOp::HAdd(SimdTy::V4F32) => {
                if args.len() != 2 {
                    return Err("SIMD hadd expects 2 arguments".into());
                }
                self.emit(Inst::Haddps {
                    dst,
                    src1: args[0],
                    src2: x86::RegMem::Reg(args[1]),
                });
            }
            
            SimdOp::DotProduct { imm } => {
                if args.len() != 2 {
                    return Err("SIMD dpps expects 2 arguments".into());
                }
                self.emit(Inst::Dpps {
                    dst,
                    src1: args[0],
                    src2: x86::RegMem::Reg(args[1]),
                    imm: *imm,
                });
            }
            
            _ => return Err(format!("Unsupported SIMD operation for x86: {:?}", op)),
        }
        
        Ok(())
    }
}

/// ARM64 NEON lowering
#[cfg(feature = "arm64-backend")]
impl SimdLowering for VCode<arm64::inst::Inst> {
    fn lower_simd_op(
        &mut self,
        op: &SimdOp,
        dst: VReg,
        args: &[VReg],
    ) -> Result<(), String> {
        use arm64::inst::{Inst, VectorType};
        
        match op {
            // Load/Store operations
            SimdOp::Load(SimdTy::V128) => {
                if args.len() != 1 {
                    return Err("SIMD load expects 1 argument".into());
                }
                // Simplified - need proper AMode construction
                unimplemented!("SIMD load needs proper AMode support");
            }
            
            SimdOp::Store(SimdTy::V128) => {
                if args.len() != 2 {
                    return Err("SIMD store expects 2 arguments".into());
                }
                unimplemented!("SIMD store needs proper AMode support");
            }
            
            // Arithmetic operations
            SimdOp::Add(SimdTy::V4F32) => {
                if args.len() != 2 {
                    return Err("SIMD add expects 2 arguments".into());
                }
                self.emit(Inst::FaddV {
                    dst,
                    src1: args[0],
                    src2: args[1],
                    ty: VectorType::V4S,
                });
            }
            
            SimdOp::Sub(SimdTy::V4F32) => {
                if args.len() != 2 {
                    return Err("SIMD sub expects 2 arguments".into());
                }
                self.emit(Inst::FsubV {
                    dst,
                    src1: args[0],
                    src2: args[1],
                    ty: VectorType::V4S,
                });
            }
            
            SimdOp::Mul(SimdTy::V4F32) => {
                if args.len() != 2 {
                    return Err("SIMD mul expects 2 arguments".into());
                }
                self.emit(Inst::FmulV {
                    dst,
                    src1: args[0],
                    src2: args[1],
                    ty: VectorType::V4S,
                });
            }
            
            SimdOp::Div(SimdTy::V4F32) => {
                if args.len() != 2 {
                    return Err("SIMD div expects 2 arguments".into());
                }
                self.emit(Inst::FdivV {
                    dst,
                    src1: args[0],
                    src2: args[1],
                    ty: VectorType::V4S,
                });
            }
            
            // Integer operations
            SimdOp::Add(SimdTy::V4I32) => {
                if args.len() != 2 {
                    return Err("SIMD add expects 2 arguments".into());
                }
                self.emit(Inst::AddV {
                    dst,
                    src1: args[0],
                    src2: args[1],
                    ty: VectorType::V4S,
                });
            }
            
            SimdOp::Sub(SimdTy::V4I32) => {
                if args.len() != 2 {
                    return Err("SIMD sub expects 2 arguments".into());
                }
                self.emit(Inst::SubV {
                    dst,
                    src1: args[0],
                    src2: args[1],
                    ty: VectorType::V4S,
                });
            }
            
            SimdOp::Mul(SimdTy::V4I32) => {
                if args.len() != 2 {
                    return Err("SIMD mul expects 2 arguments".into());
                }
                self.emit(Inst::MulV {
                    dst,
                    src1: args[0],
                    src2: args[1],
                    ty: VectorType::V4S,
                });
            }
            
            // Comparisons
            SimdOp::Eq(SimdTy::V4F32) => {
                if args.len() != 2 {
                    return Err("SIMD eq expects 2 arguments".into());
                }
                self.emit(Inst::FcmeqV {
                    dst,
                    src1: args[0],
                    src2: args[1],
                    ty: VectorType::V4S,
                });
            }
            
            // TODO: Handle Gt by swapping operands with Lt
            // SimdOp::Gt(SimdTy::V4F32) => { ... }
            
            // TODO: Handle Ge by swapping operands with Le  
            // SimdOp::Ge(SimdTy::V4F32) => { ... }
            
            SimdOp::Eq(SimdTy::V4I32) => {
                if args.len() != 2 {
                    return Err("SIMD eq expects 2 arguments".into());
                }
                self.emit(Inst::CmeqV {
                    dst,
                    src1: args[0],
                    src2: args[1],
                    ty: VectorType::V4S,
                });
            }
            
            // TODO: Handle integer Gt by swapping operands with Lt
            // SimdOp::Gt(SimdTy::V4I32) => { ... }
            
            // Conversions
            SimdOp::Convert(from_ty, to_ty) => {
                match (from_ty, to_ty) {
                    (SimdTy::V4I32, SimdTy::V4F32) => {
                        if args.len() != 1 {
                            return Err("SIMD cvt expects 1 argument".into());
                        }
                        self.emit(Inst::ScvtfV {
                            dst,
                            src: args[0],
                            ty: VectorType::V4S,
                        });
                    }
                    (SimdTy::V4F32, SimdTy::V4I32) => {
                        if args.len() != 1 {
                            return Err("SIMD cvt expects 1 argument".into());
                        }
                        self.emit(Inst::FcvtzsV {
                            dst,
                            src: args[0],
                            ty: VectorType::V4S,
                        });
                    }
                    _ => return Err(format!("Unsupported SIMD conversion: {:?} to {:?}", from_ty, to_ty)),
                }
            }
            
            // Reduction operations
            // TODO: HAdd (horizontal add) could potentially be mapped to Sum reduction
            // SimdOp::HAdd(SimdTy::V4F32) => { ... }
            
            _ => return Err(format!("Unsupported SIMD operation for ARM64: {:?}", op)),
        }
        
        Ok(())
    }
}

/// WebAssembly SIMD128 lowering
#[cfg(feature = "wasm-backend")]
impl SimdLowering for VCode<wasm::WasmInst> {
    fn lower_simd_op(
        &mut self,
        op: &SimdOp,
        dst: VReg,
        args: &[VReg],
    ) -> Result<(), String> {
        use wasm::WasmInst;
        
        // For WASM, dst is not used directly since it's stack-based
        // The result is pushed onto the stack
        let _ = dst;
        
        match op {
            // Load/Store operations
            SimdOp::Load(SimdTy::V128) => {
                if args.len() != 1 {
                    return Err("SIMD load expects 1 argument".into());
                }
                // Push address onto stack
                // For WASM, VReg index is used directly as local index
                // In a real implementation, we'd need proper VReg to local mapping
                let idx = args[0].0.0.index() as u32;
                self.emit(WasmInst::LocalGet { idx });
                // Load v128
                self.emit(WasmInst::V128Load { offset: 0, align: 4 });
            }
            
            SimdOp::Store(SimdTy::V128) => {
                if args.len() != 2 {
                    return Err("SIMD store expects 2 arguments".into());
                }
                // Push address
                // For WASM, VReg index is used directly as local index
                // In a real implementation, we'd need proper VReg to local mapping
                let idx = args[0].0.0.index() as u32;
                self.emit(WasmInst::LocalGet { idx });
                // Push value
                // For WASM, VReg index is used directly as local index
                let idx = args[1].0.0.index() as u32;
                self.emit(WasmInst::LocalGet { idx });
                // Store
                self.emit(WasmInst::V128Store { offset: 0, align: 4 });
            }
            
            // Arithmetic operations
            SimdOp::Add(SimdTy::V4F32) => {
                if args.len() != 2 {
                    return Err("SIMD add expects 2 arguments".into());
                }
                // For WASM, VReg index is used directly as local index
                // In a real implementation, we'd need proper VReg to local mapping
                let idx = args[0].0.0.index() as u32;
                self.emit(WasmInst::LocalGet { idx });
                // For WASM, VReg index is used directly as local index
                let idx = args[1].0.0.index() as u32;
                self.emit(WasmInst::LocalGet { idx });
                self.emit(WasmInst::F32x4Add);
            }
            
            SimdOp::Sub(SimdTy::V4F32) => {
                if args.len() != 2 {
                    return Err("SIMD sub expects 2 arguments".into());
                }
                // For WASM, VReg index is used directly as local index
                // In a real implementation, we'd need proper VReg to local mapping
                let idx = args[0].0.0.index() as u32;
                self.emit(WasmInst::LocalGet { idx });
                // For WASM, VReg index is used directly as local index
                let idx = args[1].0.0.index() as u32;
                self.emit(WasmInst::LocalGet { idx });
                self.emit(WasmInst::F32x4Sub);
            }
            
            SimdOp::Mul(SimdTy::V4F32) => {
                if args.len() != 2 {
                    return Err("SIMD mul expects 2 arguments".into());
                }
                // For WASM, VReg index is used directly as local index
                // In a real implementation, we'd need proper VReg to local mapping
                let idx = args[0].0.0.index() as u32;
                self.emit(WasmInst::LocalGet { idx });
                // For WASM, VReg index is used directly as local index
                let idx = args[1].0.0.index() as u32;
                self.emit(WasmInst::LocalGet { idx });
                self.emit(WasmInst::F32x4Mul);
            }
            
            SimdOp::Div(SimdTy::V4F32) => {
                if args.len() != 2 {
                    return Err("SIMD div expects 2 arguments".into());
                }
                // For WASM, VReg index is used directly as local index
                // In a real implementation, we'd need proper VReg to local mapping
                let idx = args[0].0.0.index() as u32;
                self.emit(WasmInst::LocalGet { idx });
                // For WASM, VReg index is used directly as local index
                let idx = args[1].0.0.index() as u32;
                self.emit(WasmInst::LocalGet { idx });
                self.emit(WasmInst::F32x4Div);
            }
            
            // Integer operations
            SimdOp::Add(SimdTy::V4I32) => {
                if args.len() != 2 {
                    return Err("SIMD add expects 2 arguments".into());
                }
                // For WASM, VReg index is used directly as local index
                // In a real implementation, we'd need proper VReg to local mapping
                let idx = args[0].0.0.index() as u32;
                self.emit(WasmInst::LocalGet { idx });
                // For WASM, VReg index is used directly as local index
                let idx = args[1].0.0.index() as u32;
                self.emit(WasmInst::LocalGet { idx });
                self.emit(WasmInst::I32x4Add);
            }
            
            SimdOp::Sub(SimdTy::V4I32) => {
                if args.len() != 2 {
                    return Err("SIMD sub expects 2 arguments".into());
                }
                // For WASM, VReg index is used directly as local index
                // In a real implementation, we'd need proper VReg to local mapping
                let idx = args[0].0.0.index() as u32;
                self.emit(WasmInst::LocalGet { idx });
                // For WASM, VReg index is used directly as local index
                let idx = args[1].0.0.index() as u32;
                self.emit(WasmInst::LocalGet { idx });
                self.emit(WasmInst::I32x4Sub);
            }
            
            SimdOp::Mul(SimdTy::V4I32) => {
                if args.len() != 2 {
                    return Err("SIMD mul expects 2 arguments".into());
                }
                // For WASM, VReg index is used directly as local index
                // In a real implementation, we'd need proper VReg to local mapping
                let idx = args[0].0.0.index() as u32;
                self.emit(WasmInst::LocalGet { idx });
                // For WASM, VReg index is used directly as local index
                let idx = args[1].0.0.index() as u32;
                self.emit(WasmInst::LocalGet { idx });
                self.emit(WasmInst::I32x4Mul);
            }
            
            // Comparisons
            SimdOp::Eq(SimdTy::V4F32) => {
                if args.len() != 2 {
                    return Err("SIMD eq expects 2 arguments".into());
                }
                // For WASM, VReg index is used directly as local index
                // In a real implementation, we'd need proper VReg to local mapping
                let idx = args[0].0.0.index() as u32;
                self.emit(WasmInst::LocalGet { idx });
                // For WASM, VReg index is used directly as local index
                let idx = args[1].0.0.index() as u32;
                self.emit(WasmInst::LocalGet { idx });
                self.emit(WasmInst::F32x4Eq);
            }
            
            SimdOp::Lt(SimdTy::V4F32) => {
                if args.len() != 2 {
                    return Err("SIMD lt expects 2 arguments".into());
                }
                // For WASM, VReg index is used directly as local index
                // In a real implementation, we'd need proper VReg to local mapping
                let idx = args[0].0.0.index() as u32;
                self.emit(WasmInst::LocalGet { idx });
                // For WASM, VReg index is used directly as local index
                let idx = args[1].0.0.index() as u32;
                self.emit(WasmInst::LocalGet { idx });
                self.emit(WasmInst::F32x4Lt);
            }
            
            SimdOp::Le(SimdTy::V4F32) => {
                if args.len() != 2 {
                    return Err("SIMD le expects 2 arguments".into());
                }
                // For WASM, VReg index is used directly as local index
                // In a real implementation, we'd need proper VReg to local mapping
                let idx = args[0].0.0.index() as u32;
                self.emit(WasmInst::LocalGet { idx });
                // For WASM, VReg index is used directly as local index
                let idx = args[1].0.0.index() as u32;
                self.emit(WasmInst::LocalGet { idx });
                self.emit(WasmInst::F32x4Le);
            }
            
            SimdOp::Eq(SimdTy::V4I32) => {
                if args.len() != 2 {
                    return Err("SIMD eq expects 2 arguments".into());
                }
                // For WASM, VReg index is used directly as local index
                // In a real implementation, we'd need proper VReg to local mapping
                let idx = args[0].0.0.index() as u32;
                self.emit(WasmInst::LocalGet { idx });
                // For WASM, VReg index is used directly as local index
                let idx = args[1].0.0.index() as u32;
                self.emit(WasmInst::LocalGet { idx });
                self.emit(WasmInst::I32x4Eq);
            }
            
            SimdOp::Gt(SimdTy::V4I32) => {
                if args.len() != 2 {
                    return Err("SIMD gt expects 2 arguments".into());
                }
                // For WASM, VReg index is used directly as local index
                // In a real implementation, we'd need proper VReg to local mapping
                let idx = args[0].0.0.index() as u32;
                self.emit(WasmInst::LocalGet { idx });
                // For WASM, VReg index is used directly as local index
                let idx = args[1].0.0.index() as u32;
                self.emit(WasmInst::LocalGet { idx });
                self.emit(WasmInst::I32x4GtS);
            }
            
            // Conversions
            SimdOp::CvtI32ToF32 => {
                if args.len() != 1 {
                    return Err("SIMD cvt expects 1 argument".into());
                }
                // For WASM, VReg index is used directly as local index
                // In a real implementation, we'd need proper VReg to local mapping
                let idx = args[0].0.0.index() as u32;
                self.emit(WasmInst::LocalGet { idx });
                self.emit(WasmInst::F32x4ConvertI32x4S);
            }
            
            SimdOp::CvtF32ToI32 => {
                if args.len() != 1 {
                    return Err("SIMD cvt expects 1 argument".into());
                }
                // For WASM, VReg index is used directly as local index
                // In a real implementation, we'd need proper VReg to local mapping
                let idx = args[0].0.0.index() as u32;
                self.emit(WasmInst::LocalGet { idx });
                self.emit(WasmInst::I32x4TruncSatF32x4S);
            }
            
            _ => return Err(format!("Unsupported SIMD operation for WASM: {:?}", op)),
        }
        
        Ok(())
    }
}