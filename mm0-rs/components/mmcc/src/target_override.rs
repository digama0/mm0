//! Global target override mechanism
//!
//! This module provides a way to set a global target override from the command line,
//! which takes precedence over any target set in the MM1 file.

use std::sync::Mutex;
use crate::arch::target::Target;

/// Global target override, set from command line
static TARGET_OVERRIDE: Mutex<Option<Target>> = Mutex::new(None);

/// Set the global target override
pub fn set_target_override(target: Target) {
    *TARGET_OVERRIDE.lock().unwrap() = Some(target);
}

/// Get the global target override, if any
pub fn get_target_override() -> Option<Target> {
    TARGET_OVERRIDE.lock().unwrap().clone()
}

/// Parse a target string like "x86_64-linux" into a Target
pub fn parse_target(s: &str) -> Result<Target, String> {
    use crate::arch::target::{TargetArch, OperatingSystem};
    
    match s {
        "x86_64-linux" => Ok(Target {
            arch: TargetArch::X86_64,
            os: OperatingSystem::Linux,
        }),
        "x86_64-macos" => Ok(Target {
            arch: TargetArch::X86_64,
            os: OperatingSystem::MacOS,
        }),
        "arm64-linux" => Ok(Target {
            arch: TargetArch::Arm64,
            os: OperatingSystem::Linux,
        }),
        "arm64-macos" => Ok(Target {
            arch: TargetArch::Arm64,
            os: OperatingSystem::MacOS,
        }),
        "wasm32" => Ok(Target {
            arch: TargetArch::Wasm32,
            os: OperatingSystem::Wasi,
        }),
        "wasm64" => Ok(Target {
            arch: TargetArch::Wasm64,
            os: OperatingSystem::Wasi,
        }),
        _ => Err(format!("Unknown target '{}'. Valid targets: x86_64-linux, x86_64-macos, arm64-linux, arm64-macos, wasm32, wasm64", s))
    }
}