import x86.lemmas

namespace x86

inductive arg : Type
| imm : qword → arg
| reg : regnum → arg
| mem : option scale_index → base → ℤ → arg
| label : ℕ → arg
| loc : ℕ → ℤ → arg

inductive directive
| label : ℕ → directive
| loc : ℕ → arg → directive

inductive asm1
| unop : unop → wsize → arg → asm1
| binop : binop → wsize → arg → arg → asm1
| mul : wsize → arg → asm1
| div : wsize → arg → asm1
| lea : wsize → arg → arg → asm1

| movsx : wsize → arg → arg → wsize → asm1
| movzx : wsize → arg → arg → wsize → asm1
| xchg : wsize → arg → regnum → asm1
| cmpxchg : wsize → arg → regnum → asm1
| xadd : wsize → arg → regnum → asm1
| cmov : cond_code → wsize → arg → arg → asm1
| setcc : cond_code → bool → arg → asm1

| jump : arg → asm1
| jcc : cond_code → ℕ → asm1
| call : arg → asm1
| ret : qword → asm1
| push : arg → asm1
| pop : arg → asm1
| leave : asm1

| cmc
| clc
| stc
| syscall

| exact : ast → asm1

inductive asm
| nil : asm
| cons : asm1 → asm → asm
| dir : directive → asm
| seq : asm → asm → asm
| block : asm → asm

def arg.offset : arg → ℤ → option arg
| (arg.mem si b v) w := some $ arg.mem si b (v + w)
| (arg.loc i v) w := some $ arg.loc i (v + w)
| _ _ := none

inductive assemble_imm_rm (locs : list arg) : arg → imm_rm → Prop
| imm (q) : assemble_imm_rm (arg.imm q) (imm_rm.imm q)
| reg (r) : assemble_imm_rm (arg.reg r) (imm_rm.rm (RM.reg r))
| mem (si b q) : assemble_imm_rm
  (arg.mem si b (bitvec.to_int q)) (imm_rm.rm (RM.mem si b q))
| loc (i off a rm) :
  (locs.nth i).bind (λ a, a.offset off) = some a →
  assemble_imm_rm a rm → assemble_imm_rm (arg.loc i off) rm

def assemble_imm (locs : list arg) (a : arg) (q : qword) : Prop :=
assemble_imm_rm locs a (imm_rm.imm q)

def assemble_RM (locs : list arg) (a : arg) (rm : RM) : Prop :=
assemble_imm_rm locs a (imm_rm.rm rm)

def assemble_ds (locs : list arg) (d s : arg) : dest_src → Prop
| (dest_src.Rm_i rm q) := assemble_RM locs d rm ∧ assemble_imm locs s q
| (dest_src.Rm_r rm r) := assemble_RM locs d rm ∧ assemble_RM locs s (RM.reg r)
| (dest_src.R_rm r rm) := assemble_RM locs d (RM.reg r) ∧ assemble_RM locs s rm

inductive assemble1 (locs : list arg) (labs : list qword)
  (rip : qword) : asm1 → ast → Prop
| unop (op sz a rm) :
  assemble_RM locs a rm →
  assemble1 (asm1.unop op sz a) (ast.unop op sz rm)
| binop (op sz d s ds) :
  assemble_ds locs d s ds →
  assemble1 (asm1.binop op sz d s) (ast.binop op sz ds)
| mul (sz a rm) :
  assemble_RM locs a rm →
  assemble1 (asm1.mul sz a) (ast.mul sz rm)
| div (sz a rm) :
  assemble_RM locs a rm →
  assemble1 (asm1.div sz a) (ast.div sz rm)
| lea (sz d s ds) :
  assemble_ds locs d s ds →
  assemble1 (asm1.lea sz d s) (ast.lea sz ds)
| movsx (sz d s sz2 ds) :
  assemble_ds locs d s ds →
  assemble1 (asm1.movsx sz d s sz2) (ast.movsx sz ds sz2)
| xchg (sz a rm r) :
  assemble_RM locs a rm →
  assemble1 (asm1.xchg sz a r) (ast.xchg sz rm r)
| cmpxchg (sz a rm r) :
  assemble_RM locs a rm →
  assemble1 (asm1.cmpxchg sz a r) (ast.cmpxchg sz rm r)
| xadd (sz a rm r) :
  assemble_RM locs a rm →
  assemble1 (asm1.xadd sz a r) (ast.xadd sz rm r)
| cmov (c sz d s ds) :
  assemble_ds locs d s ds →
  assemble1 (asm1.cmov c sz d s) (ast.cmov c sz ds)
| setcc (c b a rm) :
  assemble_RM locs a rm →
  assemble1 (asm1.setcc c b a) (ast.setcc c b rm)
| jump (a rm) :
  assemble_RM locs a rm →
  assemble1 (asm1.jump a) (ast.jump rm)
| jcc (c i q) :
  labs.nth i = some q →
  assemble1 (asm1.jcc c i) (ast.jcc c (rip - q))
| call (a rm) :
  assemble_imm_rm locs a rm →
  assemble1 (asm1.call a) (ast.call rm)
| ret (q) : assemble1 (asm1.ret q) (ast.ret q)
| push (a rm) :
  assemble_imm_rm locs a rm →
  assemble1 (asm1.push a) (ast.push rm)
| pop (a rm) :
  assemble_RM locs a rm →
  assemble1 (asm1.pop a) (ast.pop rm)
| leave : assemble1 asm1.leave ast.leave
| cmc : assemble1 asm1.cmc ast.cmc
| clc : assemble1 asm1.clc ast.clc
| stc : assemble1 asm1.stc ast.stc
| syscall : assemble1 asm1.syscall ast.syscall
| exact (a) : assemble1 (asm1.exact a) a

inductive assemble (locs : list arg) :
  list qword → qword → asm → list byte → qword → Prop
| nil (labs rip) : assemble labs rip asm.nil [] rip
| asm1 (labs rip a ast as l l₂ rip') :
  assemble1 locs labs rip a ast →
  decode ast l →
  assemble labs (rip + ↑l.length) as l₂ rip' →
  assemble labs rip (asm.cons a as) (l ++ l₂) rip'
| label (labs rip i) :
  list.nth labs i = some rip →
  assemble labs rip (asm.dir (directive.label i)) [] rip
| loc (labs i arg rip) :
  locs.nth i = some arg →
  assemble labs rip (asm.dir (directive.loc i arg)) [] rip
| seq (labs rip as1 as2 l1 l2 rip1 rip2) :
  assemble labs rip as1 l1 rip1 →
  assemble labs rip1 as2 l2 rip2 →
  assemble labs rip (asm.seq as1 as2) (l1 ++ l2) rip2
| block (labs rip rip1 as l rip') :
  assemble (rip1 :: labs) rip as l rip' →
  assemble labs rip (asm.block as) l rip'

end x86