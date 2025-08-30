//! Target platform specifications
//!
//! This module handles platform-specific details that vary even within
//! the same architecture (e.g., ARM64 on Linux vs macOS).

use std::fmt::{Debug, Display};

/// Operating system / platform target
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OperatingSystem {
    Linux,
    MacOS,
    Windows,
    // WebAssembly doesn't really have an OS
    Wasi,
    BareWasm,
}

/// Complete target specification
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Target {
    pub arch: TargetArch,
    pub os: OperatingSystem,
}

impl Default for Target {
    fn default() -> Self {
        Target {
            arch: TargetArch::X86_64,
            os: OperatingSystem::Linux,
        }
    }
}

/// Target architectures
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TargetArch {
    X86_64,
    Arm64,
    Wasm32,
    Wasm64,
}

impl Target {
    /// Get the current compilation target
    pub fn current() -> Self {
        #[cfg(all(target_arch = "x86_64", target_os = "linux"))]
        return Target { arch: TargetArch::X86_64, os: OperatingSystem::Linux };
        
        #[cfg(all(target_arch = "x86_64", target_os = "macos"))]
        return Target { arch: TargetArch::X86_64, os: OperatingSystem::MacOS };
        
        #[cfg(all(target_arch = "aarch64", target_os = "linux"))]
        return Target { arch: TargetArch::Arm64, os: OperatingSystem::Linux };
        
        #[cfg(all(target_arch = "aarch64", target_os = "macos"))]
        return Target { arch: TargetArch::Arm64, os: OperatingSystem::MacOS };
        
        #[cfg(target_arch = "wasm32")]
        return Target { arch: TargetArch::Wasm32, os: OperatingSystem::BareWasm };
        
        #[cfg(not(any(
            all(target_arch = "x86_64", any(target_os = "linux", target_os = "macos")),
            all(target_arch = "aarch64", any(target_os = "linux", target_os = "macos")),
            target_arch = "wasm32"
        )))]
        compile_error!("Unsupported target platform");
    }
    
    /// Parse a target triple string
    pub fn from_triple(triple: &str) -> Result<Self, String> {
        let parts: Vec<&str> = triple.split('-').collect();
        
        if parts.len() < 2 {
            return Err(format!("Invalid target triple: {}", triple));
        }
        
        let arch = match parts[0] {
            "x86_64" => TargetArch::X86_64,
            "aarch64" | "arm64" => TargetArch::Arm64,
            "wasm32" => TargetArch::Wasm32,
            "wasm64" => TargetArch::Wasm64,
            _ => return Err(format!("Unknown architecture: {}", parts[0])),
        };
        
        let os = if triple.contains("linux") {
            OperatingSystem::Linux
        } else if triple.contains("darwin") || triple.contains("apple") {
            OperatingSystem::MacOS
        } else if triple.contains("windows") {
            OperatingSystem::Windows
        } else if triple.contains("wasi") {
            OperatingSystem::Wasi
        } else if arch == TargetArch::Wasm32 || arch == TargetArch::Wasm64 {
            OperatingSystem::BareWasm
        } else {
            return Err(format!("Unknown operating system in triple: {}", triple));
        };
        
        Ok(Target { arch, os })
    }
    
    /// Get the syscall convention for this target
    pub fn syscall_convention(&self) -> Option<SyscallConvention> {
        match (self.arch, self.os) {
            (TargetArch::X86_64, OperatingSystem::Linux) => Some(SyscallConvention::X64Linux),
            (TargetArch::X86_64, OperatingSystem::MacOS) => Some(SyscallConvention::X64MacOS),
            (TargetArch::Arm64, OperatingSystem::Linux) => Some(SyscallConvention::Arm64Linux),
            (TargetArch::Arm64, OperatingSystem::MacOS) => Some(SyscallConvention::Arm64MacOS),
            _ => None, // No direct syscalls
        }
    }
}

impl Display for Target {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let arch_str = match self.arch {
            TargetArch::X86_64 => "x86_64",
            TargetArch::Arm64 => "aarch64",
            TargetArch::Wasm32 => "wasm32",
            TargetArch::Wasm64 => "wasm64",
        };
        
        let os_str = match self.os {
            OperatingSystem::Linux => "linux",
            OperatingSystem::MacOS => "apple-darwin",
            OperatingSystem::Windows => "windows",
            OperatingSystem::Wasi => "wasi",
            OperatingSystem::BareWasm => "unknown",
        };
        
        write!(f, "{}-{}", arch_str, os_str)
    }
}

/// System call conventions for different platforms
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SyscallConvention {
    /// x86-64 Linux: syscall number in RAX, args in RDI, RSI, RDX, R10, R8, R9
    X64Linux,
    /// x86-64 macOS: syscall number in RAX with high bit set, same arg registers
    X64MacOS,
    /// ARM64 Linux: syscall number in X8, args in X0-X5
    Arm64Linux,
    /// ARM64 macOS: syscall number in X16, args in X0-X5
    Arm64MacOS,
}

impl SyscallConvention {
    /// Get syscall numbers for common operations
    pub fn syscall_number(&self, op: Syscall) -> Option<i64> {
        use Syscall::*;
        match (self, op) {
            // Linux syscalls
            (SyscallConvention::X64Linux, Read) => Some(0),
            (SyscallConvention::X64Linux, Write) => Some(1),
            (SyscallConvention::X64Linux, Exit) => Some(60),
            
            (SyscallConvention::Arm64Linux, Read) => Some(63),
            (SyscallConvention::Arm64Linux, Write) => Some(64),
            (SyscallConvention::Arm64Linux, Exit) => Some(93),
            
            // macOS syscalls (BSD-based, with high bit set on x64)
            (SyscallConvention::X64MacOS, Exit) => Some(0x2000001),
            (SyscallConvention::X64MacOS, Write) => Some(0x2000004),
            (SyscallConvention::X64MacOS, Read) => Some(0x2000003),
            
            (SyscallConvention::Arm64MacOS, Exit) => Some(1),
            (SyscallConvention::Arm64MacOS, Write) => Some(4),
            (SyscallConvention::Arm64MacOS, Read) => Some(3),
            
            _ => None,
        }
    }
}

/// Common system calls we need to support
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Syscall {
    Read,
    Write,
    Exit,
    // Add more as needed
}