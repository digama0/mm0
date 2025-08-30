# ARM64 Proof System Design

## Problem Statement

The MM0 compiler's proof system is currently hardcoded for x86 architecture due to:
1. Direct re-export of x86 types as defaults (`pub use x86::*`)
2. Proof generation tightly coupled to x86 instruction semantics
3. No abstraction layer between architecture-specific code and proofs

## Current Workaround Issues

Our current approach (caching ARM64 code while returning fake x86) is **unsafe** because:
- It breaks MM0's verification guarantees
- The returned x86 code doesn't correspond to actual ARM64 behavior
- Proofs generated are meaningless for the actual executed code

## Proposed Architecture

### Phase 1: Minimal Viable Proof Abstraction

1. **Remove x86 default exports**
   - Replace `pub use x86::*` with explicit imports
   - Create architecture-agnostic type aliases

2. **Add Architecture Trait**
   ```rust
   trait ArchProof {
       type Inst: ProofInst;
       type Reg: ProofReg;
       
       fn prove_move(&self, dst: Self::Reg, src: Self::Reg) -> Proof;
       fn prove_syscall(&self, num: u32, args: &[Self::Reg]) -> Proof;
       fn prove_call(&self, target: ProcId, args: &[Self::Reg]) -> Proof;
   }
   ```

3. **Create Abstract Proof IR**
   ```rust
   enum ProofInst {
       Move { dst: AbstractReg, src: AbstractReg },
       Call { target: ProcId, args: Vec<AbstractReg> },
       Syscall { num: u32, args: Vec<AbstractReg> },
       Return { value: Option<AbstractReg> },
   }
   ```

### Phase 2: Implement ARM64 Proofs

1. **ARM64 Semantic Model**
   - Define ARM64 instruction semantics in MM0
   - Create proof rules for each instruction type
   - Verify syscall conventions match OS expectations

2. **Proof Generation**
   - Implement `ArchProof` for ARM64
   - Generate proofs that match ARM64 semantics
   - Ensure calling convention compliance

### Phase 3: Verification

1. **Test Suite**
   - Verify ARM64 proofs for basic programs
   - Compare with x86 proofs for equivalent programs
   - Ensure both produce valid ELF theorems

2. **Documentation**
   - Document ARM64 instruction semantics
   - Explain proof obligations for each instruction
   - Provide examples of verified ARM64 programs

## Implementation Strategy

### Safe Incremental Approach

1. **Don't break x86** - Keep existing x86 proof path working
2. **Add parallel ARM64 path** - Build alongside, not replacing
3. **Gradual abstraction** - Extract common patterns iteratively
4. **Verify at each step** - Ensure proofs remain valid

### Current Status

- ✅ ARM64 code generation works
- ✅ Identified proof system coupling
- ⚠️  Unsafe workaround in place
- 🎯 Need proper abstraction layer

## Next Steps

1. Create a feature branch for proof abstraction
2. Start with minimal trait definition
3. Implement for x86 first (ensure no regression)
4. Then implement for ARM64
5. Remove workaround only after verification works