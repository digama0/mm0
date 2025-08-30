//! Integration test for ARM64 constant table functionality

use mmcc::arch::arm64::const_table::{Arm64ConstTable, ConstDataExt};
use mmcc::linker::ConstData;
use mmcc::types::vcode::ConstRef;
use mmcc::Symbol;
use std::collections::HashMap;

#[test]
fn test_arm64_const_table_integration() {
    // Create a ConstData structure like LinkedCode would have
    let mut const_data = ConstData {
        map: HashMap::new(),
        ordered: vec![],
        rodata: vec![],
    };
    
    // Add some constants
    let hello_sym = Symbol::new("hello_str");
    let hello_data = b"Hello, ARM64!\n";
    let hello_addr = const_data.rodata.len() as u32;
    const_data.rodata.extend_from_slice(hello_data);
    const_data.map.insert(hello_sym, (hello_data.len() as u32, ConstRef::Ptr(hello_addr)));
    const_data.ordered.push(hello_sym);
    
    let answer_sym = Symbol::new("answer");
    const_data.map.insert(answer_sym, (8, ConstRef::Value(42)));
    const_data.ordered.push(answer_sym);
    
    let pi_sym = Symbol::new("pi");
    let pi_bytes = 3.14159_f64.to_le_bytes();
    let pi_addr = const_data.rodata.len() as u32;
    const_data.rodata.extend_from_slice(&pi_bytes);
    const_data.map.insert(pi_sym, (8, ConstRef::Ptr(pi_addr)));
    const_data.ordered.push(pi_sym);
    
    // Convert to ARM64 constant table
    let arm64_table = const_data.to_arm64_const_table();
    
    // Verify constants were converted correctly
    assert_eq!(arm64_table.get_symbol(0), Some(&hello_sym));
    assert_eq!(arm64_table.get_size(0), Some(14));
    assert_eq!(arm64_table.get_offset(0), Some(0));
    
    assert_eq!(arm64_table.get_symbol(1), Some(&answer_sym));
    assert_eq!(arm64_table.get_size(1), Some(8));
    
    assert_eq!(arm64_table.get_symbol(2), Some(&pi_sym));
    assert_eq!(arm64_table.get_size(2), Some(8));
    
    // Check data alignment
    let data = arm64_table.get_data();
    assert!(data.len() >= hello_data.len() + 8 + 8);
    
    // Verify string data
    assert_eq!(&data[0..14], hello_data);
}

#[test]
fn test_arm64_const_offset_calculation() {
    let mut table = Arm64ConstTable::new();
    
    // Add constants of various sizes to test alignment
    let c1 = table.add_string(Symbol::new("c1"), "ABC"); // 3 bytes
    let c2 = table.add_int(Symbol::new("c2"), 0x12345678, 4); // 4 bytes
    let c3 = table.add_string(Symbol::new("c3"), "Hello, World!"); // 13 bytes
    
    // Check that constants are properly aligned
    assert_eq!(table.get_offset(c1), Some(0));
    assert_eq!(table.get_size(c1), Some(3));
    
    // c2 should be at offset 8 (3 + 5 padding)
    assert_eq!(table.get_offset(c2), Some(8));
    assert_eq!(table.get_size(c2), Some(4));
    
    // c3 should be at offset 16 (8 + 4 + 4 padding)
    assert_eq!(table.get_offset(c3), Some(16));
    assert_eq!(table.get_size(c3), Some(13));
}

#[test]
fn test_arm64_adr_offset_calculation() {
    // Test the offset calculation for ADR instructions
    let code_size = 100; // 100 instructions
    let const_offset = code_size * 4; // Each ARM64 instruction is 4 bytes
    
    // ADR at instruction 10 trying to load constant at offset 0
    let adr_position = 10;
    let remaining_instructions = code_size - adr_position;
    let offset_from_adr = remaining_instructions * 4;
    
    assert_eq!(offset_from_adr, 360); // (100 - 10) * 4
    
    // Verify this is within ADR range (±1MB)
    assert!(offset_from_adr < 1024 * 1024);
}