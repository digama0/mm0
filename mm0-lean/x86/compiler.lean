import x86.assembly

noncomputable theory
namespace mmc

open x86 (wsize regnum)
def proc_loc := nat
def block_loc := nat

inductive irm
| reg : regnum → irm

inductive inst
| seq : inst → inst → inst
| mov : wsize → inst
| push : irm → inst

inductive blocks
| seq : blocks → blocks → blocks
| entry : proc_loc → inst → blocks
| block : block_loc → inst → blocks

inductive epilogue
| free : nat → epilogue → epilogue
| pop : regnum → epilogue → epilogue
| ret : epilogue

axiom prop : Type
axiom expr : Type

structure gctx :=
(content : string)
(result : prop)

axiom tctx : Type
axiom ret_abi : Type

structure pctx1 :=
(G : gctx)
(ret : ret_abi)
(sp_max : nat)

structure pctx :=
(G : gctx)
(P : pctx1)
instance pctx_coe : has_coe pctx gctx := ⟨pctx.G⟩

inductive ok_assembled : pctx → blocks → Prop

inductive labels
| and : labels → labels → labels
| one : block_loc → tctx → labels

structure label_group :=
(variant : expr)
(labs : labels)

structure bctx :=
(G : pctx)
(labs : list label_group)
instance bctx_coe : has_coe bctx pctx := ⟨bctx.G⟩

axiom flags : Type

inductive lctx : Type
| reg : tctx → lctx
| prologue : epilogue → nat → tctx → lctx
| with_flags : flags → tctx → lctx
| defer : inst → lctx → lctx
instance lctx_coe : has_coe tctx lctx := ⟨lctx.reg⟩

noncomputable def lctx.tctx: lctx → tctx
| (lctx.reg t) := t
| (lctx.prologue _ _ t) := t
| (lctx.with_flags _ t) := t
| (lctx.defer _ l) := l.tctx

def lctx.push_variant : expr → lctx → lctx
| _ l := l

inductive ok_epi : bctx → tctx → epilogue → nat → Prop

inductive ok_inst : bctx → lctx → inst → Prop

inductive ok_insts : bctx → lctx → inst → lctx → Prop

inductive ok_weak : bctx → lctx → lctx → Prop

inductive ok_block : bctx → block_loc → lctx → Prop
| weak {G P Q ip} : ok_weak G P Q → ok_block G ip Q → ok_block G ip P

inductive ok_proc : gctx → proc_loc → inst → Prop

end mmc