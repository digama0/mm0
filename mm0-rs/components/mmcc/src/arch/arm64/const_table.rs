//! ARM64 constant table management
//!
//! This module handles the storage and lookup of constants for ARM64 code generation.
//! Constants are stored in a data section after the code and accessed via PC-relative
//! addressing using the ADR instruction.

use std::collections::HashMap;
use crate::Symbol;
use crate::types::vcode::ConstRef;

/// ARM64 constant table
#[derive(Clone, Debug, Default)]
pub struct Arm64ConstTable {
    /// Map from symbol to (size, offset) in the constant data section
    constants: HashMap<Symbol, (u32, u32)>,
    /// The actual constant data
    data: Vec<u8>,
    /// Map from constant ID to symbol
    id_to_symbol: Vec<Symbol>,
}

impl Arm64ConstTable {
    /// Create a new empty constant table
    pub fn new() -> Self {
        Self::default()
    }
    
    /// Add a constant to the table and return its ID
    pub fn add_constant(&mut self, symbol: Symbol, data: &[u8]) -> u32 {
        // Check if constant already exists
        if let Some(&(_, _)) = self.constants.get(&symbol) {
            // Find the existing ID
            return self.id_to_symbol.iter()
                .position(|s| s == &symbol)
                .expect("symbol in constants but not in id_to_symbol") as u32;
        }
        
        // Align to 8 bytes for better performance
        let padding = (8 - (self.data.len() % 8)) % 8;
        self.data.extend(std::iter::repeat(0).take(padding));
        
        let offset = self.data.len() as u32;
        let size = data.len() as u32;
        
        // Add the constant data
        self.data.extend_from_slice(data);
        
        // Record the constant
        self.constants.insert(symbol, (size, offset));
        let id = self.id_to_symbol.len() as u32;
        self.id_to_symbol.push(symbol);
        
        id
    }
    
    /// Add a string constant
    pub fn add_string(&mut self, symbol: Symbol, s: &str) -> u32 {
        self.add_constant(symbol, s.as_bytes())
    }
    
    /// Add an integer constant
    pub fn add_int(&mut self, symbol: Symbol, value: u64, size: u32) -> u32 {
        let bytes = match size {
            1 => vec![value as u8],
            2 => (value as u16).to_le_bytes().to_vec(),
            4 => (value as u32).to_le_bytes().to_vec(),
            8 => value.to_le_bytes().to_vec(),
            _ => panic!("Invalid integer size: {}", size),
        };
        self.add_constant(symbol, &bytes)
    }
    
    /// Get the offset of a constant by ID
    pub fn get_offset(&self, id: u32) -> Option<u32> {
        self.id_to_symbol.get(id as usize)
            .and_then(|symbol| self.constants.get(symbol))
            .map(|&(_, offset)| offset)
    }
    
    /// Get the size of a constant by ID
    pub fn get_size(&self, id: u32) -> Option<u32> {
        self.id_to_symbol.get(id as usize)
            .and_then(|symbol| self.constants.get(symbol))
            .map(|&(size, _)| size)
    }
    
    /// Get the symbol for a constant ID
    pub fn get_symbol(&self, id: u32) -> Option<&Symbol> {
        self.id_to_symbol.get(id as usize)
    }
    
    /// Get all constant data
    pub fn get_data(&self) -> &[u8] {
        &self.data
    }
    
    /// Check if the table is empty
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }
    
    /// Get the total size of constant data
    pub fn size(&self) -> u32 {
        self.data.len() as u32
    }
}

/// Extension trait to integrate with LinkedCode's ConstData
pub trait ConstDataExt {
    /// Convert LinkedCode constants to ARM64 constant table
    fn to_arm64_const_table(&self) -> Arm64ConstTable;
}

impl ConstDataExt for crate::linker::ConstData {
    fn to_arm64_const_table(&self) -> Arm64ConstTable {
        let mut table = Arm64ConstTable::new();
        
        // Process constants in order
        for &symbol in &self.ordered {
            let (size, const_ref) = &self.map[&symbol];
            
            match const_ref {
                ConstRef::Value(val) => {
                    // Add immediate value as constant
                    table.add_int(symbol, *val, *size);
                }
                ConstRef::Ptr(addr) => {
                    // Extract data from rodata section
                    let data = &self.rodata[*addr as usize..(*addr + *size) as usize];
                    table.add_constant(symbol, data);
                }
            }
        }
        
        table
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_const_table_basic() {
        let mut table = Arm64ConstTable::new();
        
        // Add a string constant
        let hello_sym = crate::intern("hello");
        let id1 = table.add_string(hello_sym, "Hello, World!\n");
        assert_eq!(id1, 0);
        
        // Add an integer constant
        let num_sym = crate::intern("answer");
        let id2 = table.add_int(num_sym, 42, 4);
        assert_eq!(id2, 1);
        
        // Check offsets
        assert_eq!(table.get_offset(0), Some(0));
        assert_eq!(table.get_size(0), Some(14)); // "Hello, World!\n"
        
        // Second constant should be aligned to 8 bytes
        assert_eq!(table.get_offset(1), Some(16)); // 14 + 2 padding
        assert_eq!(table.get_size(1), Some(4));
        
        // Check symbols
        assert_eq!(table.get_symbol(0), Some(&hello_sym));
        assert_eq!(table.get_symbol(1), Some(&num_sym));
    }
    
    #[test]
    fn test_duplicate_constants() {
        let mut table = Arm64ConstTable::new();
        
        let sym = crate::intern("const");
        let id1 = table.add_string(sym, "test");
        let id2 = table.add_string(sym, "test"); // Same symbol
        
        // Should return the same ID
        assert_eq!(id1, id2);
        assert_eq!(table.id_to_symbol.len(), 1);
    }
}