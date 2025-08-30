fn main() {
    println!("Testing ARM64 function call encoding...");
    
    // Test BL encoding for different offsets
    test_bl_encoding(0);      // Call to same location
    test_bl_encoding(0x1000); // Call 4KB forward
    test_bl_encoding(-0x1000); // Call 4KB backward
    
    // Test BLR encoding
    println!("\nBLR X1 encoding: 0x{:08x}", encode_blr(1));
    println!("BLR X30 encoding: 0x{:08x}", encode_blr(30));
    
    println!("\nFunction calls ready for integration!");
}

fn test_bl_encoding(offset: i32) {
    let encoded = encode_bl(offset);
    println!("BL offset {:#x} = 0x{:08x}", offset, encoded);
}

fn encode_bl(offset: i32) -> u32 {
    assert!(offset >= -(1 << 27) && offset < (1 << 27));
    assert!(offset & 3 == 0);
    let imm26 = ((offset >> 2) & 0x3ffffff) as u32;
    0x94000000 | imm26
}

fn encode_blr(reg: u8) -> u32 {
    0xd63f0000 | ((reg as u32) << 5)
}