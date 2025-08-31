//! MMC Compiler - compiles MMC source files to native code
//! 
//! This is a simple command-line interface for the mmcc compiler.
//! It demonstrates compilation with multiple backend targets.

use std::env;
use std::fs;
use std::io::Write;
use std::process;

fn main() {
    let args: Vec<String> = env::args().collect();
    
    if args.len() < 2 {
        eprintln!("mmc - The MMC Compiler");
        eprintln!();
        eprintln!("Usage: {} <source.mmc> [options]", args[0]);
        eprintln!();
        eprintln!("Options:");
        eprintln!("  -o <output>    Output file (default: a.out)");
        eprintln!("  --target <arch> Target architecture: x86, arm64, wasm");
        eprintln!("  --emit-asm     Emit assembly instead of binary");
        eprintln!();
        eprintln!("Examples:");
        eprintln!("  {} hello.mmc", args[0]);
        eprintln!("  {} hello.mmc -o hello", args[0]);
        eprintln!("  {} hello.mmc --target arm64 --emit-asm", args[0]);
        process::exit(1);
    }

    let input_file = &args[1];
    let mut output_file = "a.out".to_string();
    let mut target_arch = detect_current_arch();
    let mut emit_asm = false;
    
    // Parse command line arguments
    let mut i = 2;
    while i < args.len() {
        match args[i].as_str() {
            "-o" => {
                if i + 1 < args.len() {
                    output_file = args[i + 1].clone();
                    i += 2;
                } else {
                    eprintln!("Error: -o requires an argument");
                    process::exit(1);
                }
            }
            "--target" => {
                if i + 1 < args.len() {
                    target_arch = match args[i + 1].as_str() {
                        "x86" | "x86_64" => "x86_64",
                        "arm64" | "aarch64" => "arm64",
                        "wasm" | "wasm32" => "wasm32",
                        other => {
                            eprintln!("Error: Unknown target architecture: {}", other);
                            process::exit(1);
                        }
                    };
                    i += 2;
                } else {
                    eprintln!("Error: --target requires an argument");
                    process::exit(1);
                }
            }
            "--emit-asm" => {
                emit_asm = true;
                i += 1;
            }
            _ => {
                eprintln!("Error: Unknown option: {}", args[i]);
                process::exit(1);
            }
        }
    }
    
    // Read input file
    let source = match fs::read_to_string(input_file) {
        Ok(content) => content,
        Err(e) => {
            eprintln!("Error reading file '{}': {}", input_file, e);
            process::exit(1);
        }
    };
    
    // Show compilation info
    eprintln!("Compiling {} for {} architecture...", input_file, target_arch);
    
    // For now, demonstrate the compilation process
    // Real implementation would use the mmcc API here
    
    match target_arch {
        "x86_64" => compile_x86(&source, &output_file, emit_asm),
        "arm64" => compile_arm64(&source, &output_file, emit_asm),
        "wasm32" => compile_wasm(&source, &output_file, emit_asm),
        _ => unreachable!(),
    }
}

fn detect_current_arch() -> &'static str {
    #[cfg(target_arch = "x86_64")]
    { "x86_64" }
    
    #[cfg(target_arch = "aarch64")]
    { "arm64" }
    
    #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
    { "wasm32" }
}

fn compile_x86(source: &str, output: &str, emit_asm: bool) {
    eprintln!("Using x86-64 backend");
    
    // Placeholder implementation
    if emit_asm {
        let asm = generate_x86_hello_asm();
        if let Err(e) = fs::write(format!("{}.s", output), asm) {
            eprintln!("Error writing assembly file: {}", e);
            process::exit(1);
        }
        eprintln!("Generated assembly: {}.s", output);
    } else {
        eprintln!("Binary generation not yet implemented");
        eprintln!("Use --emit-asm to see generated assembly");
    }
}

fn compile_arm64(source: &str, output: &str, emit_asm: bool) {
    eprintln!("Using ARM64 backend");
    
    if emit_asm {
        let asm = generate_arm64_hello_asm();
        if let Err(e) = fs::write(format!("{}.s", output), asm) {
            eprintln!("Error writing assembly file: {}", e);
            process::exit(1);
        }
        eprintln!("Generated assembly: {}.s", output);
    } else {
        eprintln!("Binary generation not yet implemented");
        eprintln!("Use --emit-asm to see generated assembly");
    }
}

fn compile_wasm(source: &str, output: &str, emit_asm: bool) {
    eprintln!("Using WebAssembly backend");
    
    if emit_asm {
        let wat = generate_wasm_hello_wat();
        if let Err(e) = fs::write(format!("{}.wat", output), wat) {
            eprintln!("Error writing WAT file: {}", e);
            process::exit(1);
        }
        eprintln!("Generated WebAssembly text: {}.wat", output);
    } else {
        eprintln!("WASM binary generation not yet implemented");
        eprintln!("Use --emit-asm to see generated WAT");
    }
}

// Placeholder assembly generators
fn generate_x86_hello_asm() -> &'static str {
    r#"    .text
    .globl _start
_start:
    # write(1, "Hello, World!\n", 14)
    movl    $1, %eax        # syscall: write
    movl    $1, %edi        # fd: stdout
    leaq    msg(%rip), %rsi # buf: msg
    movl    $14, %edx       # count: 14
    syscall
    
    # exit(0)
    movl    $60, %eax       # syscall: exit
    xorl    %edi, %edi      # status: 0
    syscall

    .data
msg:
    .ascii "Hello, World!\n"
"#
}

fn generate_arm64_hello_asm() -> &'static str {
    r#"    .text
    .align 2
    .globl _start
_start:
    // write(1, "Hello, World!\n", 14)
    mov     x0, #1          // fd: stdout
    adr     x1, msg         // buf: msg
    mov     x2, #14         // count: 14
    mov     x16, #4         // syscall: write (macOS)
    svc     #0x80           // supervisor call
    
    // exit(0)
    mov     x0, #0          // status: 0
    mov     x16, #1         // syscall: exit (macOS)
    svc     #0x80           // supervisor call

    .data
msg:
    .ascii "Hello, World!\n"
"#
}

fn generate_wasm_hello_wat() -> &'static str {
    r#"(module
  ;; Import functions from the host
  (import "wasi_unstable" "fd_write"
    (func $fd_write (param i32 i32 i32 i32) (result i32)))
  (import "wasi_unstable" "proc_exit"
    (func $proc_exit (param i32)))
  
  ;; Memory with initial size of 1 page
  (memory 1)
  (export "memory" (memory 0))
  
  ;; Data segment with hello world message
  (data (i32.const 8) "Hello, World!\n")
  
  ;; Main function
  (func $main (export "_start")
    ;; Prepare iovs for fd_write
    (i32.store (i32.const 0) (i32.const 8))   ;; iov.base = 8
    (i32.store (i32.const 4) (i32.const 14))  ;; iov.len = 14
    
    ;; Call fd_write(1, iovs, 1, nwritten)
    (call $fd_write
      (i32.const 1)    ;; fd: stdout
      (i32.const 0)    ;; iovs: address 0
      (i32.const 1)    ;; iovs_len: 1
      (i32.const 20))  ;; nwritten: address 20
    drop
    
    ;; Exit with code 0
    (i32.const 0)
    (call $proc_exit)
  )
)
"#
}