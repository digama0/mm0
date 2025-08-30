#!/usr/bin/env cargo +nightly -Zscript

//! Test ARM64 arithmetic instruction encoding directly
//! Run with: cargo +nightly -Zscript test_arm64_arith.rs

fn main() {
    println!("Testing ARM64 arithmetic instruction encoding...");
    
    // Test ADD X0, X1, #42
    let add_imm = encode_add_imm(0, 1, 42, true);
    println!("ADD X0, X1, #42 = 0x{:08x}", add_imm);
    assert_eq!(add_imm, 0x9100a820, "ADD immediate encoding incorrect");
    
    // Test ADD X0, X1, X2
    let add_reg = encode_add_reg(0, 1, 2, true);
    println!("ADD X0, X1, X2 = 0x{:08x}", add_reg);
    assert_eq!(add_reg, 0x8b020020, "ADD register encoding incorrect");
    
    // Test SUB X3, X4, #100
    let sub_imm = encode_sub_imm(3, 4, 100, true);
    println!("SUB X3, X4, #100 = 0x{:08x}", sub_imm);
    assert_eq!(sub_imm, 0xb1019083, "SUB immediate encoding incorrect");
    
    // Test MUL X0, X1, X2
    let mul = encode_mul(0, 1, 2, true);
    println!("MUL X0, X1, X2 = 0x{:08x}", mul);
    assert_eq!(mul, 0x9b027c20, "MUL encoding incorrect");
    
    // Test SDIV X5, X3, X4
    let sdiv = encode_sdiv(5, 3, 4, true);
    println!("SDIV X5, X3, X4 = 0x{:08x}", sdiv);
    assert_eq!(sdiv, 0x9ac40c65, "SDIV encoding incorrect");
    
    // Test CMP X1, X2
    let cmp_reg = encode_cmp_reg(1, 2, true);
    println!("CMP X1, X2 = 0x{:08x}", cmp_reg);
    assert_eq!(cmp_reg, 0xeb02003f, "CMP register encoding incorrect");
    
    // Test CMP X0, #0
    let cmp_imm = encode_cmp_imm(0, 0, true);
    println!("CMP X0, #0 = 0x{:08x}", cmp_imm);
    assert_eq!(cmp_imm, 0xf100001f, "CMP immediate encoding incorrect");
    
    println!("\nAll tests passed! ✅");
}

// ARM64 instruction encoding functions

fn encode_add_imm(dst: u32, src: u32, imm: u32, is_64bit: bool) -> u32 {
    let sf = if is_64bit { 1 } else { 0 };
    (sf << 31) | (0b00 << 29) | (0b10001 << 24) | ((imm & 0xfff) << 10) | (src << 5) | dst
}

fn encode_add_reg(dst: u32, src1: u32, src2: u32, is_64bit: bool) -> u32 {
    let sf = if is_64bit { 1 } else { 0 };
    (sf << 31) | (0b00 << 29) | (0b01011 << 24) | (src2 << 16) | (src1 << 5) | dst
}

fn encode_sub_imm(dst: u32, src: u32, imm: u32, is_64bit: bool) -> u32 {
    let sf = if is_64bit { 1 } else { 0 };
    // SUB immediate uses opc=01
    (sf << 31) | (0b01 << 29) | (0b10001 << 24) | ((imm & 0xfff) << 10) | (src << 5) | dst
}

fn encode_mul(dst: u32, src1: u32, src2: u32, is_64bit: bool) -> u32 {
    let sf = if is_64bit { 1 } else { 0 };
    // MADD with XZR as accumulator (Rd = Rn * Rm + XZR = Rn * Rm)
    (sf << 31) | 0x1b000000 | (src2 << 16) | (0x1f << 10) | (src1 << 5) | dst
}

fn encode_sdiv(dst: u32, src1: u32, src2: u32, is_64bit: bool) -> u32 {
    let sf = if is_64bit { 1 } else { 0 };
    (sf << 31) | 0x1ac00c00 | (src2 << 16) | (src1 << 5) | dst
}

fn encode_cmp_reg(lhs: u32, rhs: u32, is_64bit: bool) -> u32 {
    let sf = if is_64bit { 1 } else { 0 };
    // SUBS XZR, Xn, Xm
    (sf << 31) | 0x6b000000 | 0x1f | (rhs << 16) | (lhs << 5)
}

fn encode_cmp_imm(lhs: u32, imm: u32, is_64bit: bool) -> u32 {
    let sf = if is_64bit { 1 } else { 0 };
    // SUBS XZR, Xn, #imm
    (sf << 31) | 0x71000000 | 0x1f | ((imm & 0xfff) << 10) | (lhs << 5)
}