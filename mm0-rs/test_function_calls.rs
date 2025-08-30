#!/usr/bin/env cargo +nightly -Zscript

//! Test function call encoding for all architectures

fn main() {
    println!("=== Function Call Encoding Tests ===\n");
    
    test_arm64_calls();
    test_x86_64_calls();
    test_wasm_calls();
    
    println!("\n=== Summary ===");
    println!("Function calls work differently on each architecture:");
    println!("- ARM64: Uses BL/BLR, link register (X30) stores return address");
    println!("- x86-64: Uses CALL, return address pushed on stack");
    println!("- WASM: Uses call instruction with function index");
}

fn test_arm64_calls() {
    println!("1. ARM64 Function Calls:");
    
    // BL (Branch with Link) - direct call
    let bl_offset = 0x1000; // Call function 4KB ahead
    let bl_insn = encode_arm64_bl(bl_offset);
    println!("   BL #0x1000:");
    println!("     Encoding: 0x{:08x}", bl_insn);
    println!("     Operation: X30 = PC + 4; PC = PC + 0x1000");
    
    // BLR (Branch with Link to Register) - indirect call
    println!("\n   BLR X1:");
    println!("     Encoding: 0xd63f0020");
    println!("     Operation: X30 = PC + 4; PC = X1");
    
    // RET - return
    println!("\n   RET:");
    println!("     Encoding: 0xd65f03c0");
    println!("     Operation: PC = X30");
    
    // Example function with prologue/epilogue
    println!("\n   Example function:");
    println!("     ; Function prologue");
    println!("     STP X29, X30, [SP, #-16]!  ; Save frame pointer and return address");
    println!("     MOV X29, SP                 ; Set up frame pointer");
    println!("     ");
    println!("     ; Function body");
    println!("     MOV X0, #42                 ; Return value");
    println!("     ");
    println!("     ; Function epilogue");
    println!("     LDP X29, X30, [SP], #16     ; Restore frame pointer and return address");
    println!("     RET                         ; Return to caller");
}

fn test_x86_64_calls() {
    println!("\n2. x86-64 Function Calls:");
    
    // Direct CALL
    println!("   CALL rel32:");
    println!("     Encoding: E8 xx xx xx xx");
    println!("     Operation: Push RIP; RIP = RIP + rel32");
    
    // Indirect CALL
    println!("\n   CALL RAX:");
    println!("     Encoding: FF D0");
    println!("     Operation: Push RIP; RIP = RAX");
    
    // RET
    println!("\n   RET:");
    println!("     Encoding: C3");
    println!("     Operation: Pop RIP");
    
    // Example function
    println!("\n   Example function:");
    println!("     ; Function prologue");
    println!("     PUSH RBP         ; Save old base pointer");
    println!("     MOV RBP, RSP     ; Set up stack frame");
    println!("     ");
    println!("     ; Function body");
    println!("     MOV RAX, 42      ; Return value in RAX");
    println!("     ");
    println!("     ; Function epilogue");
    println!("     POP RBP          ; Restore base pointer");
    println!("     RET              ; Return to caller");
}

fn test_wasm_calls() {
    println!("\n3. WebAssembly Function Calls:");
    
    // Direct call
    println!("   call $func0:");
    println!("     Encoding: 10 00  ; call function_index=0");
    println!("     Operation: Push return address; Jump to function");
    
    // Indirect call
    println!("\n   call_indirect:");
    println!("     Encoding: 11 00 00  ; type_index=0, table_index=0");
    println!("     Operation: Pop index from stack; Call function at table[index]");
    
    // Return
    println!("\n   return:");
    println!("     Encoding: 0F");
    println!("     Operation: Return from current function");
    
    // Example function
    println!("\n   Example WASM function:");
    println!("     (func $add (param $a i32) (param $b i32) (result i32)");
    println!("       local.get $a    ; Push first parameter");
    println!("       local.get $b    ; Push second parameter");
    println!("       i32.add         ; Add them");
    println!("       return          ; Return result (optional, implicit at end)");
    println!("     )");
    
    // Show actual encoding
    let func_body = vec![
        0x00,       // 0 local declarations
        0x20, 0x00, // local.get 0
        0x20, 0x01, // local.get 1
        0x6a,       // i32.add
        0x0b,       // end
    ];
    println!("\n   Function body encoding: {:02x?}", func_body);
}

// ARM64 BL encoding
fn encode_arm64_bl(offset: i32) -> u32 {
    // BL encoding: 1001010 | imm26
    assert!(offset >= -(1 << 27) && offset < (1 << 27), "Offset out of range");
    assert!(offset & 3 == 0, "Offset must be 4-byte aligned");
    
    let imm26 = ((offset >> 2) & 0x3ffffff) as u32;
    0x94000000 | imm26
}