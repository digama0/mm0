use std::{io::{self, Write}, ops::Index};
use arrayvec::ArrayVec;
use byteorder::{LE, WriteBytesExt};
use crate::{LinkedCode, TEXT_START, arch_pcode::ArchPCode, types::vcode::{GlobalId, ProcId, BlockId}};

pub(crate) const FUNCTION_ALIGN: u32 = 16;

#[inline] fn align_to<const N: u64>(i: u64) -> u64 { (i + N - 1) & !(N - 1) }

#[allow(clippy::cast_lossless, clippy::cast_possible_truncation)]
fn function_pad(pos: u64) -> &'static [u8] {
  &[0; FUNCTION_ALIGN as usize][..(align_to::<{FUNCTION_ALIGN as u64}>(pos) - pos) as usize]
}

impl LinkedCode {
  /// Write this code object to an <code>impl [Write]</code> (such as a file),
  /// as a complete ELF file.
  ///
  /// This can then be executed to run the compiled program.
  #[allow(clippy::cast_lossless)]
  pub fn write_elf(&self, w: &mut impl Write) -> io::Result<()> {
    // Dispatch based on target architecture
    match self.target.arch {
      #[cfg(not(any(feature = "arm64-backend", feature = "wasm-backend")))]
      crate::arch::target::TargetArch::X86_64 => self.write_elf_x86(w),
      #[cfg(feature = "arm64-backend")]
      crate::arch::target::TargetArch::Arm64 => self.write_arm64_executable(w),
      #[cfg(feature = "wasm-backend")]
      crate::arch::target::TargetArch::Wasm32 => self.write_wasm_executable(w),
      _ => {
        // Fallback for unknown architectures
        Err(io::Error::new(io::ErrorKind::Unsupported, 
          format!("Code generation not implemented for {:?}", self.target.arch)))
      }
    }
  }

  /// Write x86-64 ELF file
  #[cfg(not(any(feature = "arm64-backend", feature = "wasm-backend")))]
  #[allow(clippy::cast_lossless)]
  fn write_elf_x86(&self, w: &mut impl Write) -> io::Result<()> {
    const BSS_ALIGN: u64 = 16;
    const HEADER: [u8; 0x60] = [
      // ELF header
      0x7f, b'E', b'L', b'F', // ELF magic
      2, // EI_CLASS = 2 = 64-bit
      1, // EI_DATA = 1 = little endian
      1, // EI_VERSION = 1
      0, // EI_OSABI = 0 = System V
      0, // EI_ABIVERSION = 0
      0, 0, 0, 0, 0, 0, 0, // EI_PAD
      2, 0, // e_type = 2 = ET_EXEC (executable file)
      0x3e, 0, // e_machine = 0x3e = AMD x86-64
      1, 0, 0, 0, // e_version = 1
      0x78, 0, 0x40, 0, 0, 0, 0, 0, // e_entry = 0x400078 (hardcoded)
      0x40, 0, 0, 0, 0, 0, 0, 0, // e_phoff = 0x40 (immediately after the header)
      0, 0, 0, 0, 0, 0, 0, 0, // e_shoff = 0 (no section header)
      0, 0, 0, 0, // e_flags = 0
      0x40, 0, // e_ehsize = 0x40 bytes
      0x38, 0, // e_phentsize = 0x38 (program header table stride)
      1, 0, // e_phnum = 1 (one program header entry)
      0x40, 0, // e_shentsize = 0x40 (section header table stride)
      0, 0, // e_shnum = 0 (section header table entries)
      0, 0, // e_shstrndx = 0 (index of the section name table)
      // total: 64 = 0x40 bytes

      // Program header
      1, 0, 0, 0, // p_type = 1 = PT_LOAD (loadable segment)
      7, 0, 0, 0, // p_flags = 7 = read+write+execute (no page protection)
      0x78, 0, 0, 0, 0, 0, 0, 0, // p_offset = 0x78 = offset of the segment
      0x78, 0, 0x40, 0, 0, 0, 0, 0, // p_vaddr = 0x400078 (virtual addr of the segment)
      0, 0, 0, 0, 0, 0, 0, 0, // p_paddr = 0 (physical addr, unused)
    ];

    let rodata_start = u64::from(TEXT_START + self.text_size);
    let file_end = rodata_start + u64::try_from(self.consts.rodata.len()).expect("overflow");
    let global_start = align_to::<BSS_ALIGN>(file_end);
    let global_end = global_start + u64::from(self.global_size);
    w.write_all(&HEADER)?;
    // p_filesz = size of segment in the file image
    w.write_u64::<LE>(file_end - u64::from(TEXT_START))?;
    // p_memsz = size of segment in memory
    w.write_u64::<LE>(global_end - u64::from(TEXT_START))?;
    // p_align = 2^21 = 0x200000 (segment alignment)
    w.write_u64::<LE>(1 << 21)?;
    // end of program header, now at offset 0x78

    // Ensure we have x86 code
    let init_x86 = self.init.1.with_x86(|pcode| pcode.as_ref()).expect("write_elf_x86 called with non-x86 code");
    
    let mut ctx = InstSink {
      linked: self, proc: init_x86,
      rodata_start: rodata_start.try_into().expect("overflow"),
      proc_start: TEXT_START,
      local_rip: 0,
      buf: ArrayVec::new(),
    };
    ctx.write_to(w)?;
    w.write_all(function_pad(u64::from(TEXT_START + self.init.1.len())))?;

    for &(start, ref code) in &self.funcs.0 {
      let code_x86 = code.with_x86(|pcode| pcode.as_ref()).expect("write_elf_x86 called with non-x86 code");
      ctx.proc = code_x86;
      ctx.proc_start = start;
      ctx.write_to(w)?;
      w.write_all(function_pad(u64::from(code.len())))?;
    }

    w.write_all(&self.consts.rodata)
  }

  /// Write ARM64 executable (currently outputs assembly)
  #[cfg(feature = "arm64-backend")]
  pub fn write_arm64_executable(&self, w: &mut impl Write) -> io::Result<()> {
    // For now, generate simple ARM64 assembly
    writeln!(w, "    .text")?;
    writeln!(w, "    .align 2")?;
    writeln!(w, "    .globl _start")?;
    writeln!(w, "_start:")?;
    
    // Get the ARM64 PCode from the init section
    if let Some(pcode) = self.init.1.with_arm64(|p| Some(p.clone())) {
      // TODO: Implement proper ARM64 instruction encoding
      // For now, just emit a simple exit
      writeln!(w, "    // exit(0)")?;
      writeln!(w, "    mov     x0, #0          // status: 0")?;
      writeln!(w, "    mov     x16, #1         // syscall: exit (macOS)")?;
      writeln!(w, "    svc     #0x80           // supervisor call")?;
    } else {
      return Err(io::Error::new(io::ErrorKind::InvalidData, 
        "Expected ARM64 code but found different architecture"));
    }
    
    Ok(())
  }
  
  /// Write WASM executable (currently outputs WAT)
  #[cfg(feature = "wasm-backend")]
  pub fn write_wasm_executable(&self, w: &mut impl Write) -> io::Result<()> {
    // For now, generate simple WASM text format
    writeln!(w, "(module")?;
    writeln!(w, "  (func $main (export \"_start\")")?;
    writeln!(w, "    ;; Exit with code 0")?;
    writeln!(w, "    i32.const 0")?;
    writeln!(w, "    unreachable")?;
    writeln!(w, "  )")?;
    writeln!(w, ")")?;
    Ok(())
  }
}

#[cfg(not(any(feature = "arm64-backend", feature = "wasm-backend")))]
pub(crate) struct InstSink<'a> {
  linked: &'a LinkedCode,
  proc: &'a crate::regalloc::PCode,
  buf: ArrayVec<u8, 15>,
  proc_start: u32,
  local_rip: u32,
  pub(crate) rodata_start: u32,
}

#[cfg(not(any(feature = "arm64-backend", feature = "wasm-backend")))]
impl InstSink<'_> {
  pub(crate) fn len(&self) -> usize { self.buf.len() }
  pub(crate) fn push_u8(&mut self, n: u8) { self.buf.push(n) }
  pub(crate) fn push_u32(&mut self, n: u32) {
    self.buf.try_extend_from_slice(&n.to_le_bytes()).expect("instruction overflow")
  }
  pub(crate) fn push_u64(&mut self, n: u64) {
    self.buf.try_extend_from_slice(&n.to_le_bytes()).expect("instruction overflow")
  }
  pub(crate) fn set_rex(&mut self, n: u8) { self.buf[0] = n }
  pub(crate) fn update_rip(&mut self, size: u8) { self.local_rip += u32::from(size) }

  pub(crate) fn rip_relative_block(&self, tgt: BlockId) -> i32 {
    let addr = i64::from(self.proc.block_addr[tgt]) - i64::from(self.local_rip);
    i32::try_from(addr).expect("jump out of range")
  }

  pub(crate) fn rip_relative_proc(&self, f: ProcId) -> i32 {
    let addr = i64::from(self.linked.funcs[f].0) - i64::from(self.proc_start + self.local_rip);
    i32::try_from(addr).expect("jump out of range")
  }

  fn write_to(&mut self, w: &mut impl Write) -> io::Result<()> {
    self.local_rip = 0;
    self.proc.insts.0.iter().try_for_each(|inst| {
      // eprintln!("{:?} (layout {:?})", inst, inst.layout_inst());
      inst.write(self);
      // eprintln!("  = {:x?}", self.buf);
      w.write_all(&self.buf)?;
      self.buf.clear();
      Ok(())
    })
  }
}

#[cfg(not(any(feature = "arm64-backend", feature = "wasm-backend")))]
impl Index<GlobalId> for InstSink<'_> {
  type Output = u32;
  fn index(&self, index: GlobalId) -> &Self::Output { &self.linked.globals[index].1 }
}
