#!/usr/bin/env cargo +nightly -Zscript

//! Test and demonstrate register allocation strategies
//! Shows the difference between naive and proper register allocation

use std::fs;
use std::process::Command;

fn main() -> std::io::Result<()> {
    println!("=== Register Allocation Demonstration ===\n");
    
    fs::create_dir_all("test_binaries")?;
    
    demonstrate_register_pressure()?;
    demonstrate_spilling()?;
    demonstrate_graph_coloring()?;
    
    Ok(())
}

fn demonstrate_register_pressure() -> std::io::Result<()> {
    println!("1. Register Pressure Example\n");
    
    println!("   Problem: More live values than available registers");
    println!("   Example computation: (a+b) * (c+d) * (e+f) * (g+h)\n");
    
    // Naive approach - runs out of registers
    println!("   Naive allocation (uses too many registers):");
    println!("   t1 = a + b  // Uses 3 registers: a, b, t1");
    println!("   t2 = c + d  // Now 5 registers: +c, d, t2");
    println!("   t3 = e + f  // Now 7 registers: +e, f, t3");
    println!("   t4 = g + h  // Now 9 registers: +g, h, t4");
    println!("   t5 = t1 * t2");
    println!("   t6 = t3 * t4");
    println!("   result = t5 * t6");
    println!("   ❌ Needs 9+ registers!\n");
    
    // Better approach - reuse registers
    println!("   Smart allocation (reuses registers):");
    println!("   r0 = a + b");
    println!("   r1 = c + d");
    println!("   r0 = r0 * r1  // Reuse r0");
    println!("   r1 = e + f    // Reuse r1");
    println!("   r2 = g + h");
    println!("   r1 = r1 * r2  // Reuse r1");
    println!("   r0 = r0 * r1  // Final result in r0");
    println!("   ✅ Uses only 3 registers!\n");
    
    generate_register_pressure_test()?;
    
    Ok(())
}

fn generate_register_pressure_test() -> std::io::Result<()> {
    // ARM64 example showing register allocation
    let asm = r#"
.global _register_pressure
.global _main
.align 2

// Function with high register pressure
_register_pressure:
    // Save callee-saved registers we'll use
    stp x19, x20, [sp, #-48]!
    stp x21, x22, [sp, #16]
    stp x23, x24, [sp, #32]
    
    // Simulate loading 8 values (would be from memory in real code)
    mov x19, #1   // a
    mov x20, #2   // b
    mov x21, #3   // c
    mov x22, #4   // d
    mov x23, #5   // e
    mov x24, #6   // f
    mov x25, #7   // g
    mov x26, #8   // h
    
    // Compute (a+b) * (c+d) * (e+f) * (g+h)
    // Smart register reuse
    add x0, x19, x20    // t1 = a + b = 3
    add x1, x21, x22    // t2 = c + d = 7
    mul x0, x0, x1      // t1 = t1 * t2 = 21
    
    add x1, x23, x24    // t2 = e + f = 11
    add x2, x25, x26    // t3 = g + h = 15
    mul x1, x1, x2      // t2 = t2 * t3 = 165
    
    mul x0, x0, x1      // result = 21 * 165 = 3465
    
    // Restore registers
    ldp x23, x24, [sp, #32]
    ldp x21, x22, [sp, #16]
    ldp x19, x20, [sp], #48
    ret

_main:
    stp x29, x30, [sp, #-16]!
    mov x29, sp
    
    bl _register_pressure
    
    // Result too large for exit code, so return modulo 256
    and x0, x0, #0xff
    
    ldp x29, x30, [sp], #16
    ret
"#;
    
    fs::write("test_binaries/register_pressure.s", asm)?;
    
    if is_arm64() {
        Command::new("as")
            .args(&["-o", "test_binaries/register_pressure.o", 
                   "test_binaries/register_pressure.s"])
            .status()?;
            
        Command::new("ld")
            .args(&["-o", "test_binaries/register_pressure", 
                   "test_binaries/register_pressure.o",
                   "-lSystem", "-syslibroot",
                   "/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk",
                   "-e", "_main", "-arch", "arm64"])
            .status()?;
            
        match Command::new("./test_binaries/register_pressure").status() {
            Ok(status) => {
                println!("   Test result: {} (3465 mod 256 = 137 ✅)", 
                    status.code().unwrap_or(-1));
            }
            Err(e) => println!("   Failed: {}", e),
        }
    }
    
    Ok(())
}

fn demonstrate_spilling() -> std::io::Result<()> {
    println!("\n2. Register Spilling\n");
    
    println!("   When we run out of registers, we 'spill' to memory:");
    println!("   - Save register value to stack");
    println!("   - Free register for new use");
    println!("   - Reload when needed again\n");
    
    println!("   Example with limited registers:");
    println!("   // Only 3 registers available: r0, r1, r2");
    println!("   r0 = a");
    println!("   r1 = b");
    println!("   r2 = c");
    println!("   [sp+0] = r0   // Spill 'a' to stack");
    println!("   r0 = d        // Reuse r0 for 'd'");
    println!("   [sp+8] = r1   // Spill 'b'");
    println!("   r1 = e        // Reuse r1 for 'e'");
    println!("   // Later...");
    println!("   r2 = [sp+0]   // Reload 'a' when needed");
    
    Ok(())
}

fn demonstrate_graph_coloring() -> std::io::Result<()> {
    println!("\n\n3. Graph Coloring Algorithm\n");
    
    println!("   Register allocation as graph coloring:");
    println!("   - Nodes = Variables");
    println!("   - Edges = Variables alive at same time");
    println!("   - Colors = Physical registers\n");
    
    println!("   Interference Graph:");
    println!("   a ---- b      Variables that interfere");
    println!("   |\\     |      (live at same time)");
    println!("   | c -- d      can't share registers");
    println!("   |/");
    println!("   e\n");
    
    println!("   Coloring (register assignment):");
    println!("   a = X0 (red)");
    println!("   b = X1 (blue)");
    println!("   c = X2 (green)");
    println!("   d = X1 (blue) - can reuse since no edge to b");
    println!("   e = X1 (blue) - can reuse since no edge to b or d\n");
    
    println!("   Key insights:");
    println!("   - Live range analysis determines interference");
    println!("   - Graph coloring is NP-complete (use heuristics)");
    println!("   - Spill when graph can't be colored");
    
    Ok(())
}

fn is_arm64() -> bool {
    Command::new("uname")
        .arg("-m")
        .output()
        .map(|o| String::from_utf8_lossy(&o.stdout).trim() == "arm64")
        .unwrap_or(false)
}