// Test ARM64 instruction encoding directly

// Include the encoding functions we wrote
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
struct PReg(u8);

impl PReg {
    fn new(idx: u8) -> Self { PReg(idx) }
    fn index(self) -> u8 { self.0 }
}

const X0: PReg = PReg(0);
const X1: PReg = PReg(1);
const X16: PReg = PReg(16);

#[derive(Debug)]
enum OperandSize {
    Size32,
    Size64,
}

fn encode_mov_imm_simple(dst: PReg, imm: u16, size: OperandSize) -> u32 {
    let sf = match size {
        OperandSize::Size64 => 1,
        OperandSize::Size32 => 0,
    };
    
    // MOVZ instruction
    (sf << 31)
        | (0b10_100101 << 23)
        | (0b00 << 21)  // hw = 0 (bits 0-15)
        | ((imm as u32) << 5)
        | (dst.index() as u32)
}

fn encode_svc(imm: u16) -> u32 {
    0xd4000001 | ((imm as u32 & 0xffff) << 5)
}

fn encode_ret() -> u32 {
    0xd65f03c0  // RET using X30/LR
}

fn main() {
    println!("Testing ARM64 instruction encoding:");
    
    // Test MOV X0, #42
    let mov_x0_42 = encode_mov_imm_simple(X0, 42, OperandSize::Size32);
    println!("MOV W0, #42: {:08x} (bytes: {:02x} {:02x} {:02x} {:02x})", 
        mov_x0_42,
        mov_x0_42 as u8,
        (mov_x0_42 >> 8) as u8,
        (mov_x0_42 >> 16) as u8,
        (mov_x0_42 >> 24) as u8
    );
    
    // Test MOV X16, #1 (exit syscall)
    let mov_x16_1 = encode_mov_imm_simple(X16, 1, OperandSize::Size64);
    println!("MOV X16, #1: {:08x}", mov_x16_1);
    
    // Test SVC #0
    let svc_0 = encode_svc(0);
    println!("SVC #0: {:08x}", svc_0);
    
    // Test RET
    let ret = encode_ret();
    println!("RET: {:08x}", ret);
    
    // Generate a complete program
    println!("\nComplete program bytes (exit with code 42):");
    let program = vec![
        mov_x0_42.to_le_bytes(),
        mov_x16_1.to_le_bytes(),
        svc_0.to_le_bytes(),
    ];
    
    for (i, bytes) in program.iter().enumerate() {
        println!("  {:02x} {:02x} {:02x} {:02x}  // instruction {}", 
            bytes[0], bytes[1], bytes[2], bytes[3], i);
    }
}