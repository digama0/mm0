import .lemmas

-- High level assembly: a view of x86 that abstracts
-- the shape of memory a bit
namespace hla

def data := list byte

open x86

def disjoint_block : qword × ℕ → qword × ℕ → Prop
| (a, n) (b, m) := a.to_nat + n ≤ b.to_nat ∧ b.to_nat + m ≤ a.to_nat

structure hla :=
-- a list of disjoint memory blocks, and whether they are R or RW
(mem : list (bool × qword × ℕ))
-- a list of function labels, and local labels
(code : list ((qword × ℕ) × (list qword × list byte)))
(disj : list.pairwise disjoint_block
  (mem.map prod.snd ++ code.map prod.fst))

structure hla.ok (H : hla) (k : config) : Prop :=
(mem : ∀ b q n, (b, q, n) ∈ H.mem →
  ∃ v, list.length v = n ∧ k.mem.read' (cond b (perm.R + perm.W) perm.R) q v)
(code : ∀ q n ll v, ((q, n), (ll, v)) ∈ H.code →
  (list.length v = n ∧ k.mem.read' (perm.R + perm.X) q v) ∧
  (∀ l ∈ ll, q.to_nat ≤ (l:qword).to_nat ∧ l.to_nat < q.to_nat + n))

def hla.config (H : hla) := {k // H.ok k}

inductive arg : Type
| imm : qword → arg
| reg : regnum → arg
| mem : option scale_index → base → ℤ → arg
| label : ℕ → arg
| llabel : ℕ → ℕ → arg

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

| push : arg → asm1
| pop : arg → asm1
| leave : asm1

| cmc
| clc
| stc
| syscall -- regular syscalls that return are not terminators

inductive terminator
| jump : arg → terminator
| jcc : cond_code → ℕ → ℕ → terminator
| call : ℕ → ℕ → terminator
| syscall_exit : terminator -- exit syscall doesn't return
| ret : terminator

inductive bblock
| cons : asm1 → bblock → bblock
| term : terminator → bblock

inductive assemble_label (H : hla) : arg → qword → Prop
| label (i c) :
  H.code.nth i = some c →
  assemble_label (arg.label i) c.1.1
| llabel (i n c q) :
  H.code.nth i = some c →
  c.2.1.nth n = some q →
  assemble_label (arg.llabel i n) q

inductive assemble_imm_rm : arg → imm_rm → Prop
| imm (q) : assemble_imm_rm (arg.imm q) (imm_rm.imm q)
| reg (r) : assemble_imm_rm (arg.reg r) (imm_rm.rm (RM.reg r))
| mem (si b q) : assemble_imm_rm
  (arg.mem si b (bitvec.to_int q)) (imm_rm.rm (RM.mem si b q))

def assemble_imm (a : arg) (q : qword) : Prop :=
assemble_imm_rm a (imm_rm.imm q)

def assemble_RM (a : arg) (rm : RM) : Prop :=
assemble_imm_rm a (imm_rm.rm rm)

def assemble_ds (d s : arg) : dest_src → Prop
| (dest_src.Rm_i rm q) := assemble_RM d rm ∧ assemble_imm s q
| (dest_src.Rm_r rm r) := assemble_RM d rm ∧ assemble_RM s (RM.reg r)
| (dest_src.R_rm r rm) := assemble_RM d (RM.reg r) ∧ assemble_RM s rm

def code_pred := hla → list qword → qword → list byte → Prop

def asm1.pred' : asm1 → ast → Prop
| (asm1.unop op sz a) v := ∃ rm,
  assemble_RM a rm ∧
  ast.unop op sz rm = v
| (asm1.binop op sz d s) v := ∃ ds,
  assemble_ds d s ds ∧
  ast.binop op sz ds = v
| (asm1.mul sz a) v := ∃ rm,
  assemble_RM a rm ∧
  ast.mul sz rm = v
| (asm1.div sz a) v := ∃ rm,
  assemble_RM a rm ∧
  ast.div sz rm = v
| (asm1.lea sz d s) v := ∃ ds,
  assemble_ds d s ds ∧
  ast.lea sz ds = v
| (asm1.movsx sz d s sz2) v := ∃ ds,
  assemble_ds d s ds ∧
  ast.movsx sz ds sz2 = v
| (asm1.movzx sz d s sz2) v := ∃ ds,
  assemble_ds d s ds ∧
  ast.movzx sz ds sz2 = v
| (asm1.xchg sz a r) v := ∃ rm,
  assemble_RM a rm ∧
  ast.xchg sz rm r = v
| (asm1.cmpxchg sz a r) v := ∃ rm,
  assemble_RM a rm ∧
  ast.cmpxchg sz rm r = v
| (asm1.xadd sz a r) v := ∃ rm,
  assemble_RM a rm ∧
  ast.xadd sz rm r = v
| (asm1.cmov c sz d s) v := ∃ ds,
  assemble_ds d s ds ∧
  ast.cmov c sz ds = v
| (asm1.setcc c b a) v := ∃ rm,
  assemble_RM a rm ∧
  ast.setcc c b rm = v
| (asm1.push a) v := ∃ rm,
  assemble_imm_rm a rm ∧
  ast.push rm = v
| (asm1.pop a) v := ∃ rm,
  assemble_RM a rm ∧
  ast.pop rm = v
| asm1.leave v := ast.leave = v
| asm1.cmc v := ast.cmc = v
| asm1.clc v := ast.clc = v
| asm1.stc v := ast.stc = v
| asm1.syscall v := ast.syscall = v

def asm1.pred (a : asm1) : code_pred :=
λ _ _ _ v, ∃ a', a.pred' a' ∧ decode a' v

def terminator.pred : terminator → code_pred
| (terminator.jump a) H labs rip v := ∃ q,
  assemble_label H a q ∧
  decode (ast.jcc cond_code.always (q - rip)) v
| (terminator.jcc c i e) H labs rip v := ∃ q,
  labs.nth i = some q ∧
  decode (ast.jcc c (q - rip)) v ∧
  labs.nth e = some (q + v.length)
| (terminator.call f e) H labs rip v := ∃ q,
  assemble_label H (arg.label f) q ∧
  decode (ast.call (imm_rm.imm q)) v ∧
  labs.nth e = some (q + v.length)
| terminator.syscall_exit H labs rip v :=
  decode ast.syscall v -- this is ensured to be 'exit' syscall elsewhere
| terminator.ret H labs rip v :=
  decode (ast.ret 0) v

def code_pred.cons (c1 c2 : code_pred) : code_pred :=
λ H labs rip v,
  ∃ v1 v2, v = v1 ++ v2 ∧
    c1 H labs rip v1 ∧
    c2 H labs (rip + v1.length) v2

def bblock.pred : bblock → code_pred
| (bblock.cons a b) := a.pred.cons b.pred
| (bblock.term t) := t.pred

def code_pred.ok (C : code_pred) (H : hla) (k : config) (labs : list qword) :=
∃ v, C H labs k.rip v ∧ k.mem.read' (perm.R + perm.X) k.rip v

def code_pred.nil : code_pred := λ _ _ _ v, v = []

inductive bblocks.pred' (H : hla) (labs : list qword) :
  list bblock → list qword → qword → list byte → Prop
| nil (rip v) : bblocks.pred' [] [] rip v
| cons (qs b bs rip v1 v2) :
  bblock.pred b H labs rip v1 →
  bblocks.pred' bs qs (rip + v1.length) v2 →
  bblocks.pred' (b :: bs) (rip :: qs) rip (v1 ++ v2)

def hla.blocks (H : hla) (l : list (list bblock)) : Prop :=
∀ i q n ll v, H.code.nth i = some ((q, n), (ll, v)) →
  ∃ bs, l.nth i = some bs ∧ bblocks.pred' H ll bs ll q v

theorem code_pred.cons_ok {a b H k labs}
  (h : (code_pred.cons a b).ok H k labs) : a.ok H k labs := sorry

theorem bblock.exec_cons (H : hla) {k k' : config} (hk : H.ok k)
  {l} (hl : H.blocks l)
  {labs a b} (hb : (bblock.cons a b).pred.ok H k labs) :
  k.step k' ↔
  ∃ a l,
    k.mem.readX k.rip l ∧
    decode a l ∧
    ((do
      write_rip (k.rip + bitvec.of_nat _ l.length),
      execute a) k).P () k' :=
begin
  rcases code_pred.cons_ok hb with ⟨l, ⟨a', h1, h2⟩, h3⟩,
  sorry
end

end hla