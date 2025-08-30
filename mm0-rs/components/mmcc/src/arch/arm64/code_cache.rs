//! ARM64 code cache
//!
//! This module provides a temporary workaround to store ARM64 code
//! while the infrastructure expects x86 PCode.

use std::sync::Mutex;
use std::collections::HashMap;
use super::pcode::Arm64PCode;

/// Global cache for ARM64 code
/// Maps from a unique ID to the actual ARM64 code
static ARM64_CODE_CACHE: Mutex<Option<HashMap<u64, Arm64PCode>>> = Mutex::new(None);

/// Counter for generating unique IDs
static NEXT_ID: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);

/// Initialize the cache
pub fn init_cache() {
    let mut cache = ARM64_CODE_CACHE.lock().unwrap();
    if cache.is_none() {
        *cache = Some(HashMap::new());
    }
}

/// Store ARM64 code and return its ID
pub fn store_code(code: Arm64PCode) -> u64 {
    init_cache();
    
    let id = NEXT_ID.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    
    let mut cache = ARM64_CODE_CACHE.lock().unwrap();
    if let Some(map) = cache.as_mut() {
        map.insert(id, code);
    }
    
    eprintln!("ARM64: Cached code with ID {}", id);
    id
}

/// Retrieve ARM64 code by ID
pub fn get_code(id: u64) -> Option<Arm64PCode> {
    let cache = ARM64_CODE_CACHE.lock().unwrap();
    cache.as_ref().and_then(|map| map.get(&id).cloned())
}

/// Clear the cache (useful for testing)
pub fn clear_cache() {
    let mut cache = ARM64_CODE_CACHE.lock().unwrap();
    if let Some(map) = cache.as_mut() {
        map.clear();
    }
    // Reset the ID counter
    NEXT_ID.store(1, std::sync::atomic::Ordering::SeqCst);
}