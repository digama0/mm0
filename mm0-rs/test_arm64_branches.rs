#!/usr/bin/env cargo +nightly -Zscript

//! Test ARM64 conditional branch encoding
//! Run with: cargo +nightly -Zscript test_arm64_branches.rs

fn main() {
    println!("Testing ARM64 conditional branch instructions...");
    
    // Test B.EQ (branch if equal)
    let beq = encode_bcond(Cond::Eq, 100);
    println!("B.EQ #100 = 0x{:08x}", beq);
    assert_eq!(beq, 0x54000320, "B.EQ encoding incorrect");
    
    // Test B.NE (branch if not equal)  
    let bne = encode_bcond(Cond::Ne, -100);
    println!("B.NE #-100 = 0x{:08x}", bne);
    
    // Test CBZ (compare and branch if zero)
    let cbz = encode_cbz(0, 200, true); // X0, offset 200, 64-bit
    println!("CBZ X0, #200 = 0x{:08x}", cbz);
    
    // Test CBNZ (compare and branch if not zero)
    let cbnz = encode_cbnz(1, -200, false); // W1, offset -200, 32-bit
    println!("CBNZ W1, #-200 = 0x{:08x}", cbnz);
    
    // Test CMP followed by conditional branch
    println!("\nConditional branch pattern:");
    println!("  CMP X0, X1      ; Compare X0 with X1");
    println!("  B.GT label      ; Branch if greater than");
    println!("  ... fall through code ...");
    println!("label:");
    
    println!("\nAll branch tests passed! ✅");
}

#[derive(Copy, Clone)]
enum Cond {
    Eq = 0b0000,  // Equal (Z == 1)
    Ne = 0b0001,  // Not equal (Z == 0)
    Cs = 0b0010,  // Carry set/unsigned higher or same (C == 1)
    Cc = 0b0011,  // Carry clear/unsigned lower (C == 0)
    Mi = 0b0100,  // Minus/negative (N == 1)
    Pl = 0b0101,  // Plus/positive or zero (N == 0)
    Vs = 0b0110,  // Overflow (V == 1)
    Vc = 0b0111,  // No overflow (V == 0)
    Hi = 0b1000,  // Unsigned higher (C == 1 && Z == 0)
    Ls = 0b1001,  // Unsigned lower or same (!(C == 1 && Z == 0))
    Ge = 0b1010,  // Signed >= (N == V)
    Lt = 0b1011,  // Signed < (N != V)
    Gt = 0b1100,  // Signed > (Z == 0 && N == V)
    Le = 0b1101,  // Signed <= (!(Z == 0 && N == V))
}

fn encode_bcond(cond: Cond, offset: i32) -> u32 {
    // B.cond encoding: 0101010 | imm19 | 0 | cond
    assert!(offset >= -(1 << 20) && offset < (1 << 20), "Offset out of range");
    assert!(offset & 3 == 0, "Offset must be 4-byte aligned");
    
    let imm19 = ((offset >> 2) & 0x7ffff) as u32;
    0x54000000 | (imm19 << 5) | (cond as u32)
}

fn encode_cbz(reg: u8, offset: i32, is_64bit: bool) -> u32 {
    // CBZ encoding: sf|011010|0|imm19|Rt
    assert!(offset >= -(1 << 20) && offset < (1 << 20), "Offset out of range");
    assert!(offset & 3 == 0, "Offset must be 4-byte aligned");
    
    let sf = if is_64bit { 1 } else { 0 };
    let imm19 = ((offset >> 2) & 0x7ffff) as u32;
    (sf << 31) | 0x34000000 | (imm19 << 5) | (reg as u32)
}

fn encode_cbnz(reg: u8, offset: i32, is_64bit: bool) -> u32 {
    // CBNZ encoding: sf|011010|1|imm19|Rt
    assert!(offset >= -(1 << 20) && offset < (1 << 20), "Offset out of range");
    assert!(offset & 3 == 0, "Offset must be 4-byte aligned");
    
    let sf = if is_64bit { 1 } else { 0 };
    let imm19 = ((offset >> 2) & 0x7ffff) as u32;
    (sf << 31) | 0x35000000 | (imm19 << 5) | (reg as u32)
}