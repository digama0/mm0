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

inductive mem_base : Type
| abs (off : ℤ) : mem_base -- only valid for LEA arithmetic
| mem (arena off : ℕ) : mem_base -- uses RIP-relative offset
| reg : regnum → ℤ → mem_base

inductive arg : Type
| imm : qword → arg
| reg : regnum → arg
| mem : option scale_index → mem_base → arg
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

def mem_base.to_base (H : hla) (rip : qword) : mem_base → base → qword → Prop
| (mem_base.abs q) b off := b = base.none ∧ off = q
| (mem_base.mem i a) b off := ∃ c,
  H.mem.nth i = some c ∧
  b = base.rip ∧ off = c.2.1 + a - rip
| (mem_base.reg r q) b off := b = base.reg r ∧ off = q

def arg.imm_rm (H : hla) (rip : qword) : arg → imm_rm → Prop
| (arg.reg r) rm := rm = imm_rm.rm (RM.reg r)
| (arg.mem ix b) rm := ∃ b' o,
  mem_base.to_base H rip b b' o ∧
  rm = imm_rm.rm (RM.mem ix b' o)
| (arg.imm q) rm := imm_rm.imm q = rm
| _ _ := false

def arg.imm_rm' (H : hla) (a : arg) : pstate config imm_rm :=
pstate.assert $ λ k rm, a.imm_rm H k.rip rm

def arg.rm (H : hla) (rip : qword) (a : arg) (rm : RM) : Prop :=
arg.imm_rm H rip a (imm_rm.rm rm)

def arg.rm' (H : hla) (a : arg) : pstate config RM :=
pstate.assert $ λ k rm, a.rm H k.rip rm

def assemble_ds (H : hla) (rip : qword) (d s : arg) : dest_src → Prop
| (dest_src.Rm_i rm q) := arg.rm H rip d rm ∧ s = arg.imm q
| (dest_src.Rm_r rm r) := arg.rm H rip d rm ∧ s = arg.reg r
| (dest_src.R_rm r rm) := arg.rm H rip d (RM.reg r) ∧ arg.rm H rip s rm

def code_pred := hla → list qword → qword → list byte → Prop

def asm1.pred' (H : hla) (rip : qword) : asm1 → ast → Prop
| (asm1.unop op sz a) v := ∃ rm,
  a.rm H rip rm ∧
  ast.unop op sz rm = v
| (asm1.binop op sz d s) v := ∃ ds,
  assemble_ds H rip d s ds ∧
  ast.binop op sz ds = v
| (asm1.mul sz a) v := ∃ rm,
  a.rm H rip rm ∧
  ast.mul sz rm = v
| (asm1.div sz a) v := ∃ rm,
  a.rm H rip rm ∧
  ast.div sz rm = v
| (asm1.lea sz d s) v := ∃ ds,
  assemble_ds H rip d s ds ∧
  ast.lea sz ds = v
| (asm1.movsx sz d s sz2) v := ∃ ds,
  assemble_ds H rip d s ds ∧
  ast.movsx sz ds sz2 = v
| (asm1.movzx sz d s sz2) v := ∃ ds,
  assemble_ds H rip d s ds ∧
  ast.movzx sz ds sz2 = v
| (asm1.xchg sz a r) v := ∃ rm,
  a.rm H rip rm ∧
  ast.xchg sz rm r = v
| (asm1.cmpxchg sz a r) v := ∃ rm,
  a.rm H rip rm ∧
  ast.cmpxchg sz rm r = v
| (asm1.xadd sz a r) v := ∃ rm,
  a.rm H rip rm ∧
  ast.xadd sz rm r = v
| (asm1.cmov c sz d s) v := ∃ ds,
  assemble_ds H rip d s ds ∧
  ast.cmov c sz ds = v
| (asm1.setcc c b a) v := ∃ rm,
  a.rm H rip rm ∧
  ast.setcc c b rm = v
| (asm1.push a) v := ∃ rm,
  a.imm_rm H rip rm ∧
  ast.push rm = v
| (asm1.pop a) v := ∃ rm,
  a.rm H rip rm ∧
  ast.pop rm = v
| asm1.leave v := ast.leave = v
| asm1.cmc v := ast.cmc = v
| asm1.clc v := ast.clc = v
| asm1.stc v := ast.stc = v
| asm1.syscall v := ast.syscall = v

-- theorem arg.imm_rm.determ {a rm1 rm2} : arg.imm_rm a rm1 → a.imm_rm rm2 → rm1 = rm2 :=
-- by cases a; rintro ⟨⟩ ⟨⟩; refl

-- theorem arg.rm.determ {a rm1 rm2} : arg.rm a rm1 → arg.rm a rm2 → rm1 = rm2 :=
-- by cases a; rintro ⟨⟩ ⟨⟩; refl

-- def HLEA.hla_ok (H : hla) : EA → wsize → Prop
-- | (EA.m q) sz := ∃ c, c ∈ H.mem ∧ _
-- | _ sz := true

inductive HLEA
| i : qword → HLEA
| r : regnum → HLEA
| m : ℕ → ℕ → HLEA
| abs : qword → HLEA

def HLEA.to_ea (H : hla) : HLEA → EA → Prop
| (HLEA.i q) ea := ea = EA.i q
| (HLEA.r r) ea := ea = EA.r r
| (HLEA.m i a) ea := ∃ c, H.mem.nth i = some c ∧ ea = EA.m (c.2.1 + a)
| (HLEA.abs q) ea := ea = EA.m q

theorem HLEA.to_ea.determ {H ea ea1 ea2}
  (h1 : HLEA.to_ea H ea ea1) (h2 : HLEA.to_ea H ea ea2) : ea1 = ea2 :=
begin
  cases ea; try { exact h1.trans h2.symm },
  rcases h1 with ⟨c1, a1, rfl⟩, rcases h2 with ⟨c2, a2, rfl⟩,
  cases a1.symm.trans a2, exact rfl
end

def HLEA.to_ea' (H : hla) (ea : HLEA) : pstate config EA :=
pstate.assert $ λ _ ea', HLEA.to_ea H ea ea'

-- def EA.hla_ok (H : hla) (ea : EA) (sz : wsize) : Prop :=
-- ∃ ea', HLEA.ea H sz ea ea'

-- def arg.ea (k : config) (a : arg) (ea : EA) : Prop :=
-- ∃ rm, arg.imm_rm a rm ∧ imm_rm.ea k rm = ea

def index_ea' (k : config) : option scale_index → ℤ
| none := 0
| (some ⟨s, i⟩) := nat.shiftl 1 s.to_nat * (k.regs i).to_int

@[simp] theorem index_ea'_coe {k ix} : (index_ea' k ix : qword) = index_ea k ix :=
begin
  cases ix, refl,
  cases ix, simp [index_ea', index_ea, bitvec.coe_shl, bitvec.coe_to_int],
end

inductive mem_base.ea (H : hla) (k : config) (ix : ℤ) : mem_base → HLEA → Prop
| abs (i) : mem_base.ea (mem_base.abs i) (HLEA.abs (ix + i : ℤ))
| mem (i a a' : ℕ) : (ix + a : ℤ) = a' →
  mem_base.ea (mem_base.mem i a) (HLEA.m i a')
| reg (r off) (a' : ℕ) (i c) :
  H.mem.nth i = some c →
  ix + (k.regs r).to_int + off - c.2.1.to_nat = a' →
  mem_base.ea (mem_base.reg r off) (HLEA.m i a')
| reg_abs (r off) :
  mem_base.ea (mem_base.reg r off) (HLEA.abs (ix + (k.regs r).to_int + off : ℤ))

def arg.ea (H : hla) (k : config) : arg → HLEA → Prop
| (arg.imm q) ea := ea = HLEA.i q
| (arg.reg r) ea := ea = HLEA.r r
| (arg.mem ix b) ea := mem_base.ea H k (index_ea' k ix) b ea
| _ _ := false

def arg.ea' (H : hla) (a : arg) : pstate config HLEA :=
pstate.assert $ λ k ea, a.ea H k ea

-- theorem arg.ea.determ {k a ea1 ea2} : arg.ea k a ea1 → a.ea k ea2 → ea1 = ea2 :=
-- by rintro ⟨_, h1, rfl⟩ ⟨_, h2, rfl⟩; cases h1.determ h2; refl

theorem arg.imm_rm.ea {H a rm k ea}
  (h1 : arg.ea H k a ea)
  (h2 : arg.imm_rm H k.rip a rm) : ea.to_ea H (rm.ea k) :=
begin
  cases a,
  { cases h1, cases h2, exact rfl },
  { cases h1, cases h2, exact rfl },
  { rcases h2 with ⟨b, q, h, rfl⟩,
    rcases h1 with i | ⟨i, a, a', h3⟩ |
      ⟨r, off, a', i, c, h3, h4⟩ | ⟨r, off⟩;
    dsimp [imm_rm.ea, RM.ea, HLEA.to_ea],
    { rcases h with ⟨rfl, rfl⟩, simp [base.ea] },
    { rcases h with ⟨c, h, rfl, rfl⟩,
      refine ⟨_, h, _⟩,
      have h3 := congr_arg (coe : ℤ → qword) h3, simp at h3, rw ← h3,
      simp [base.ea], ring },
    { rcases h with ⟨rfl, rfl⟩,
      refine ⟨_, h3, _⟩,
      have h4 := congr_arg (coe : ℤ → qword) h4, simp at h4, rw ← h4,
      simp [base.ea, bitvec.coe_to_nat, bitvec.coe_to_int] },
    { rcases h with ⟨rfl, rfl⟩, simp [base.ea, bitvec.coe_to_int] } },
  { cases h1 },
  { cases h1 }
end

theorem arg.rm.ea {H a rm k ea}
  (h1 : arg.ea H k a ea)
  (h2 : arg.rm H k.rip a rm) : ea.to_ea H (rm.ea k) :=
arg.imm_rm.ea h1 h2

theorem assemble_ds.src {H d s ds k ea}
  (h : assemble_ds H (k:config).rip d s ds)
  (h2 : arg.ea H k s ea) : ea.to_ea H (ea_src k ds) :=
begin
  cases ds; cases h,
  { subst s, cases h2, exact rfl },
  { subst s, cases h2, exact rfl },
  { dsimp [ea_src], exact h_right.ea h2 },
end

theorem assemble_ds.dest {H d s ds k ea}
  (h : assemble_ds H (k:config).rip d s ds)
  (h2 : arg.ea H k d ea) : ea.to_ea H (ea_dest k ds) :=
by cases ds; cases h; exact h_left.ea h2

def HLEA.read (H : hla) (k : config) (sz : wsize) (w : bitvec sz.to_nat) : HLEA → Prop
| (HLEA.i i) := w = EXTZ i
| (HLEA.r r) := (EA.r r).read k sz w
| (HLEA.m i a) :=
  let n := sz.to_nat / 8 in
  ∃ c v,
    H.mem.nth i = some c ∧
    c.2.1.to_nat + n ≤ c.2.2 ∧
    k.mem.read (c.2.1 + a) v ∧
    bits_to_byte n w v
| (HLEA.abs _) := false -- absolute addresses are not for reading

theorem HLEA.to_ea.read {H ea ea' k sz w}
  (h1 : HLEA.to_ea H ea ea')
  (h2 : ea.read H k sz w) : ea'.read k sz w :=
begin
  cases ea,
  { cases h1, exact h2 },
  { cases h1, exact h2 },
  { rcases h1 with ⟨c, h1, rfl⟩,
    rcases h2 with ⟨c', v', h1', e2, h2⟩, cases h1.symm.trans h1',
    exact ⟨_, h2⟩ },
  { cases h2 }
end

theorem HLEA.read.determ {H ea k sz w1 w2} :
  HLEA.read H k sz w1 ea → ea.read H k sz w2 → w1 = w2 :=
begin
  cases ea,
  { rintro ⟨⟩ ⟨⟩, refl },
  { exact λ h1, h1.determ },
  { rintro ⟨c1, v1, a1, b1, d1, e1⟩ ⟨c2, v2, a2, b2, d2, e2⟩,
    cases a1.symm.trans a2,
    cases d1.determ_len d2 (e1.1.trans e2.1.symm),
    exact bits_to_byte.determ_l e1 e2 },
  { rintro ⟨⟩ }
end

def HLEA.readq (H : hla) (k : config) (ea : HLEA) (sz : wsize) (q : qword) : Prop :=
∃ w, ea.read H k sz w ∧ q = EXTZ w

theorem HLEA.to_ea.readq {H ea ea' k sz w}
  (h : HLEA.to_ea H ea ea') : ea.readq H k sz w → ea'.readq k sz w
| ⟨w, h1, h2⟩ := ⟨_, h.read h1, h2⟩

theorem HLEA.readq.determ {H ea k sz w1 w2} :
  HLEA.readq H k ea sz w1 → ea.readq H k sz w2 → w1 = w2
| ⟨w, h1, e1⟩ ⟨w2, h2, e2⟩ :=
  by cases h1.determ h2; exact e1.trans e2.symm

def HLEA.read' (H : hla) (ea : HLEA) (sz : wsize) : pstate config qword :=
pstate.assert $ λ k, ea.readq H k sz

def arg.read (H : hla) (k : config) (a : arg) (sz : wsize) (w : bitvec sz.to_nat) : Prop :=
∃ ea, arg.ea H k a ea ∧ ea.read H k sz w

def arg.readq (H : hla) (k : config) (a : arg) (sz : wsize) (q : qword) : Prop :=
∃ ea, arg.ea H k a ea ∧ ea.readq H k sz q

def arg.read' (H : hla) (a : arg) (sz : wsize) : pstate config qword :=
pstate.assert $ λ k, a.readq H k sz

def HLEA.write (H : hla) (k : config) (sz : wsize) (w : bitvec sz.to_nat) (k' : config) : HLEA → Prop
| (HLEA.r r) := k' = config.write_reg k r sz w
| (HLEA.m i a) :=
  let n := sz.to_nat / 8 in
  ∃ q m v,
    H.mem.nth i = some (tt, (q, m)) ∧
    q.to_nat + n ≤ m ∧
    bits_to_byte n w v ∧
    k.write_mem (q + a) v k'
| _ := false

def HLEA.writeq (H : hla) (k : config) (ea : HLEA) (sz : wsize) (q : qword) (k' : config) : Prop :=
ea.write H k sz (EXTZ q) k'

theorem HLEA.write.determ {H ea k sz w k1 k2} :
  HLEA.write H k sz w k1 ea → ea.write H k sz w k2 → k1 = k2 :=
begin
  cases ea,
  { rintro ⟨⟩ },
  { rintro ⟨⟩ ⟨⟩, refl, },
  { rintro ⟨q1, m1, v1, a1, b1, c1, d1⟩ ⟨q2, m2, v2, a2, b2, c2, d2⟩,
    cases a1.symm.trans a2,
    cases bits_to_byte.determ c1 c2,
    exact d1.determ d2 },
  { rintro ⟨⟩ },
end

theorem HLEA.writeq.determ {H ea k sz w k1 k2} :
  HLEA.writeq H k ea sz w k1 → ea.writeq H k sz w k2 → k1 = k2 :=
HLEA.write.determ

theorem HLEA.to_ea.write {H ea ea' k k' sz w}
  (h1 : HLEA.to_ea H ea ea')
  (h2 : ea.write H k sz w k') : ea'.write k sz w k' :=
begin
  cases ea,
  { cases h2 },
  { cases h2, cases h1, constructor },
  { rcases h2 with ⟨q, m, v, e1, e2, e3, e4⟩,
    rcases h1 with ⟨c, e1', rfl⟩, cases e1.symm.trans e1',
    exact EA.write.m e3 e4 },
  { cases h2 }
end

theorem HLEA.to_ea.writeq {H ea ea' k k' sz w}
  (h : HLEA.to_ea H ea ea') : ea.writeq H k sz w k' → ea'.writeq k sz w k' :=
h.write

def HLEA.write' (H : hla) (ea : HLEA) (sz : wsize) (q : qword) : pstate config unit :=
pstate.lift $ λ k _ k', ea.writeq H k sz q k'

def arg.writeq (H : hla) (k : config) (a : arg) (sz : wsize) (q : qword) (k' : config) : Prop :=
∃ ea, arg.ea H k a ea ∧ ea.writeq H k sz q k'

def arg.write' (H : hla) (a : arg) (sz : wsize) (q : qword) : pstate config unit :=
pstate.lift $ λ k _ k', a.writeq H k sz q k'

def asm1.exec (H : hla) : asm1 → pstate config unit
| (asm1.unop op sz rm) := do
  ea ← rm.ea' H,
  w ← ea.read' H sz,
  ea' ← ea.to_ea' H,
  write_unop sz w ea' op
| (asm1.binop op sz d s) := do
  ea ← d.ea' H,
  d' ← ea.read' H sz,
  s' ← s.read' H sz,
  ea' ← ea.to_ea' H,
  write_binop sz ea' d' s' op
| (asm1.mul sz r) := do
  eax ← (EA.r RAX).read' sz,
  src ← r.read' H sz,
  execute._match_2 sz eax src sz,
  erase_flags
| (asm1.div sz r) := do
  eax ← (EA.r RAX).read' sz,
  edx ← (EA.r RDX).read' sz,
  let n := edx.to_nat * (2 ^ sz.to_nat) + eax.to_nat,
  d ← bitvec.to_nat <$> r.read' H sz,
  pstate.assert $ λ _ (_:unit), d ≠ 0 ∧ n / d < 2 ^ sz.to_nat,
  (EA.r RAX).write' sz (bitvec.of_nat _ (n / d)),
  (EA.r RDX).write' sz (bitvec.of_nat _ (n % d)),
  erase_flags
| (asm1.lea sz d s) := do
  src ← s.ea' H,
  ea' ← src.to_ea' H,
  d.write' H sz ea'.addr
| (asm1.movsx sz1 d s sz2) := do
  w ← pstate.assert $ λ k, s.read H k sz1,
  d.write' H sz2 (EXTZ (EXTS w : bitvec sz2.to_nat))
| (asm1.movzx sz1 d s sz2) := do
  w ← pstate.assert $ λ k, s.read H k sz1,
  d.write' H sz2 (EXTZ w)
| (asm1.xchg sz r n) := do
  let src := EA.r n,
  dst ← r.ea' H,
  val_src ← src.read' sz,
  val_dst ← dst.read' H sz,
  src.write' sz val_dst,
  dst.write' H sz val_src
| (asm1.cmpxchg sz r n) := do
  let src := EA.r n,
  let acc := EA.r RAX,
  dst ← r.ea' H,
  val_dst ← dst.read' H sz,
  val_acc ← acc.read' sz,
  write_binop sz src val_acc val_dst binop.cmp,
  if val_acc = val_dst then
    src.read' sz >>= dst.write' H sz
  else acc.write' sz val_dst
| (asm1.xadd sz r n) := do
  let src := EA.r n,
  dst ← r.ea' H >>= HLEA.to_ea' H,
  val_src ← src.read' sz,
  val_dst ← dst.read' sz,
  src.write' sz val_dst,
  write_binop sz dst val_src val_dst binop.add
| (asm1.cmov c sz d s) := do
  k ← pstate.get,
  when (c.read k.flags) $ s.read' H sz >>= d.write' H sz
| (asm1.setcc c b r) := do
  k ← pstate.get,
  r.write' H (wsize.Sz8 b) (EXTZ $ bitvec.singleton $ c.read k.flags)
| (asm1.push i) := i.imm_rm' H >>= push
| (asm1.pop r) := r.rm' H >>= pop
| asm1.leave := do
  (EA.r RBP).read' wsize.Sz64 >>= (EA.r RSP).write' wsize.Sz64,
  pop (RM.reg RBP)
| asm1.clc := write_flags $ λ _ f, {CF := ff, ..f}
| asm1.cmc := write_flags $ λ _ f, {CF := bnot f.CF, ..f}
| asm1.stc := write_flags $ λ _ f, {CF := tt, ..f}
| asm1.syscall := pstate.fail

def noIO_rel (P : config → config → Prop) : kcfg → kcfg → Prop
| ⟨i, o, k⟩ ⟨i', o', k'⟩ := i = i' ∧ o = o' ∧ P k k'

def asm1.kexec (H : hla) : kcfg → kcfg → asm1 → Prop
| ⟨i, o, k⟩ ⟨i', o', k'⟩ asm1.syscall := ∃ k1 k2 ret,
  config.isIO k k1 ∧
  exec_io i o k1 (k1.regs RAX) i' o' k2 ret →
  k' = k2.set_reg RAX ret
| ⟨i, o, k⟩ ⟨i', o', k'⟩ a := i = i' ∧ o = o' ∧ a.exec H k k'

def asm1.pred (a : asm1) : code_pred :=
λ H _ rip v, ∃ a', a.pred' H rip a' ∧ decode a' v

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
  decode (ast.call (imm_rm.imm (q - rip))) v ∧
  labs.nth e = some (q + v.length)
| terminator.syscall_exit H labs rip v :=
  decode ast.syscall v -- this is ensured to be 'exit' syscall elsewhere
| terminator.ret H labs rip v :=
  decode (ast.ret 0) v

def terminator.exec (H : hla) (labs : list qword) (k : config) (k' : config ⊕ qword) : terminator → Prop
| (terminator.jump a) := ∃ q,
  assemble_label H a q ∧
  k' = sum.inl {rip := q, ..k}
| (terminator.jcc c i e) := ∃ q,
  labs.nth (cond (c.read k.flags) i e) = some q ∧
  k' = sum.inl {rip := q, ..k}
| (terminator.call f e) := ∃ k1 w q,
  labs.nth e = some w ∧
  push_aux w k k1 ∧
  assemble_label H (arg.label f) q ∧
  k' = sum.inl {rip := q, ..k}
| terminator.syscall_exit := ∃ q, config.exit k q ∧ k' = sum.inr q
| terminator.ret := ∃ k1, pop_rip k k1 ∧ k' = sum.inl k1

def code_pred.cons (c1 c2 : code_pred) : code_pred :=
λ H labs rip v,
  ∃ v1 v2, v = v1 ++ v2 ∧
    c1 H labs rip v1 ∧
    c2 H labs (rip + v1.length) v2

def bblock.pred : bblock → code_pred
| (bblock.cons a b) := a.pred.cons b.pred
| (bblock.term t) := t.pred

structure kexit := (input output : list byte) (exit_code : qword)

def bblock.kexec (H : hla) (labs : list qword) : bblock → kcfg → kcfg ⊕ kexit → Prop
| (bblock.cons a b) k k' := ∃ k1, a.kexec H k k1 ∧ b.kexec k1 k'
| (bblock.term t) ⟨i, o, k⟩ (sum.inl ⟨i', o', k'⟩) :=
   i = i' ∧ o = o' ∧ t.exec H labs k (sum.inl k')
| (bblock.term t) ⟨i, o, k⟩ (sum.inr ⟨i', o', c⟩) :=
   i = i' ∧ o = o' ∧ t.exec H labs k (sum.inr c)

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

theorem asm1.exec_ok {H k a a'}
  (ha : asm1.pred' H (k:config).rip a a') :
  execute a' k ≤ a.exec H k :=
begin
  cases a,
  case hla.asm1.unop : op sz a {
    rcases ha with ⟨rm, h1, rfl⟩,
    rintro ⟨⟨_, _, h2, rfl⟩, R⟩,
    rcases R _ _ ⟨h2, rfl⟩ with ⟨⟨_, _, h3, rfl⟩, R⟩,
    rcases R _ _ ⟨h3, rfl⟩ with ⟨⟨_, _, h4, rfl⟩, R⟩,
    refine ⟨⟨⟨_, _, ⟨⟩⟩, _⟩, _⟩,
    { rintro _ _ ⟨⟩,
      have A := h1.ea h2,
      have B := A.readq h3,
      refine ⟨⟨_, _, B, rfl⟩, _⟩,
      rintro _ _ ⟨h, rfl⟩, cases B.determ h,
      exact R _ _ ⟨A, rfl⟩ },
    { rintro _ _ ⟨_, _, ⟨⟩, _, _, ⟨B1, rfl⟩, B2⟩,
      have A := h1.ea h2,
      cases (A.readq h3).determ B1,
      exact ⟨_, _, ⟨h2, rfl⟩, _, _, ⟨h3, rfl⟩, _, _, ⟨A, rfl⟩, B2⟩ } },
  case hla.asm1.binop : op sz d s {
    rcases ha with ⟨ds, h1, rfl⟩,
    rintro ⟨⟨dst, _, h2, rfl⟩, R⟩,
    rcases R _ _ ⟨h2, rfl⟩ with ⟨⟨vd, _, h3, rfl⟩, R⟩,
    rcases R _ _ ⟨h3, rfl⟩ with ⟨⟨vs, _, h4, rfl⟩, R⟩,
    rcases R _ _ ⟨h4, rfl⟩ with ⟨⟨_, _, h5, rfl⟩, R⟩,
    rcases id h4 with ⟨src, A1, A2⟩,
    have A3 := h1.src A1,
    cases h5.determ (h1.dest h2),
    refine ⟨⟨⟨⟨_, _, _⟩, _,
        ⟨_, _, h5.readq h3, (h1.src A1).readq A2⟩, rfl⟩, _⟩, _⟩,
    { rintro ⟨_, _, _⟩ _ ⟨⟨_, _, B1, B2⟩, rfl⟩,
      cases (h5.readq h3).determ B1,
      cases (A3.readq A2).determ B2,
      exact R _ _ ⟨h5, rfl⟩ },
    { rintro _ _ ⟨⟨_, _, _⟩, _, ⟨⟨_, _, B1, B2⟩, rfl⟩, B3⟩,
      cases (h5.readq h3).determ B1,
      cases (A3.readq A2).determ B2,
      refine ⟨_, _, ⟨h2, rfl⟩, _, _, ⟨h3, rfl⟩,
        _, _, ⟨h4, rfl⟩, _, _, ⟨h5, rfl⟩, B3⟩ } },
  case hla.asm1.mul : sz a {
    rcases ha with ⟨rm, h1, rfl⟩,
    rintro ⟨⟨rax, _, h2, rfl⟩, R⟩,
    rcases R _ _ ⟨h2, rfl⟩ with ⟨⟨ad, _, h3, rfl⟩, R⟩,
    rcases id h3 with ⟨ea, A1, A2⟩,
    have A3 := (h1.ea A1).readq A2,
    refine ⟨⟨⟨_, _, h2, rfl⟩, _⟩, _⟩,
    { rintro _ _ ⟨B1, rfl⟩, cases h2.determ B1,
      refine ⟨⟨_, _, ⟨⟩⟩, _⟩, rintro _ _ ⟨⟩,
      refine ⟨⟨_, _, ⟨A3, rfl⟩⟩, _⟩,
      rintro _ _ ⟨B2, rfl⟩, cases A3.determ B2,
      exact R _ _ ⟨h3, rfl⟩ },
    { rintro _ _ ⟨_, _, ⟨B1, rfl⟩, _, _, ⟨⟩, _, _, ⟨B2, rfl⟩, B3⟩,
      cases h2.determ B1, cases A3.determ B2,
      exact ⟨_, _, ⟨h2, rfl⟩, _, _, ⟨h3, rfl⟩, B3⟩ } },
  case hla.asm1.div : sz a {
    rcases ha with ⟨rm, h1, rfl⟩,
    rintro ⟨⟨rax, _, h2, rfl⟩, R⟩,
    rcases R _ _ ⟨h2, rfl⟩ with ⟨⟨rdx, _, h3, rfl⟩, R⟩,
    rcases R _ _ ⟨h3, rfl⟩ with ⟨⟨src, _, h4, rfl⟩, R⟩,
    rcases R _ _ ⟨_, _, h4, rfl⟩ with ⟨⟨_, _, h5, rfl⟩, R⟩,
    rcases id h4 with ⟨_, A1, A2⟩,
    have A3 := (h1.ea A1).readq A2,
    refine ⟨⟨⟨_, _, h2, rfl⟩, _⟩, _⟩,
    { rintro _ _ ⟨B1, rfl⟩, cases h2.determ B1,
      refine ⟨⟨_, _, ⟨h3, rfl⟩⟩, _⟩, rintro _ _ ⟨B2, rfl⟩, cases h3.determ B2,
      refine ⟨⟨_, _, ⟨⟩⟩, _⟩, rintro _ _ ⟨⟩,
      refine ⟨⟨_, _, ⟨A3, rfl⟩⟩, _⟩, rintro _ _ ⟨_, _, B3, rfl⟩, cases A3.determ B3,
      refine ⟨⟨⟨⟩, _, ⟨h5, rfl⟩⟩, _⟩, rintro _ _ ⟨B4, rfl⟩,
      exact R ⟨⟩ _ ⟨h5, rfl⟩ },
    { rintro _ _ ⟨_, _, ⟨B1, rfl⟩, _, _, ⟨B2, rfl⟩, _, _, ⟨⟩,
        _, _, ⟨_, _, B3, rfl⟩, ⟨⟩, _, ⟨B4, rfl⟩, B5⟩,
      cases h2.determ B1, cases h3.determ B2, cases A3.determ B3,
      exact ⟨_, _, ⟨h2, rfl⟩, _, _, ⟨h3, rfl⟩,
        _, _, ⟨_, _, h4, rfl⟩, ⟨⟩, _, ⟨h5, rfl⟩, B5⟩ } },
  case hla.asm1.lea : sz d s {
    rcases ha with ⟨ds, h1, rfl⟩,
    rintro ⟨⟨ea, _, h2, rfl⟩, R⟩,
    rcases R _ _ ⟨h2, rfl⟩ with ⟨⟨ea', _, h3, rfl⟩, R⟩,
    rcases R _ _ ⟨h3, rfl⟩ with ⟨⟨⟩, _, dst, h4, h5⟩,
    cases (h1.src h2).determ h3,
    have A1 := h1.dest h4,
    refine ⟨⟨⟨_, _, ⟨⟩⟩, _⟩, _⟩,
    { rintro _ _ ⟨⟩, exact ⟨⟨⟩, _, A1.writeq h5⟩ },
    { rintro _ _ ⟨_, _, ⟨⟩, B1⟩,
      cases (A1.writeq h5).determ B1,
      refine ⟨_, _, ⟨h2, rfl⟩, _, _, ⟨h3, rfl⟩, _, h4, h5⟩ } },
  iterate 2 {
    rcases ha with ⟨ds, h1, rfl⟩,
    rintro ⟨⟨ea, _, h2, rfl⟩, R⟩,
    rcases R _ _ ⟨h2, rfl⟩ with ⟨⟨⟩, _, h3⟩,
    rcases id h2 with ⟨_, A1, A2⟩,
    rcases id h3 with ⟨_, A3, A4⟩,
    have A5 := (h1.src A1).read A2,
    have A6 := (h1.dest A3).writeq A4,
    refine ⟨⟨⟨_, _, A5, rfl⟩, _⟩, _⟩,
    { rintro _ _ ⟨B1, rfl⟩, cases A5.determ B1,
      refine ⟨⟨_, _, ⟨⟩⟩, _⟩, rintro _ _ ⟨⟩,
      refine ⟨⟨⟩, _, A6⟩ },
    { rintro _ _ ⟨_, _, ⟨B1, rfl⟩, _, _, ⟨⟩, B2⟩,
      cases A5.determ B1, cases A6.determ B2,
      refine ⟨_, _, ⟨h2, rfl⟩, _, A3, A4⟩ } },
  case hla.asm1.xchg : sz a r {
    rcases ha with ⟨rm, h1, rfl⟩,
    rintro ⟨⟨ea, _, h2, rfl⟩, R⟩,
    rcases R _ _ ⟨h2, rfl⟩ with ⟨⟨dst, _, h3, rfl⟩, R⟩,
    rcases R _ _ ⟨h3, rfl⟩ with ⟨⟨vs, _, h4, rfl⟩, R⟩,
    rcases R _ _ ⟨h4, rfl⟩ with ⟨⟨⟨⟩, _, h5⟩, R⟩,
    sorry, },
    -- cases (h1.src h2).determ h3,
    -- have A1 := h1.dest h4,
    -- refine ⟨⟨⟨_, _, ⟨_⟩⟩, _⟩, _⟩,
    -- { rintro _ _ ⟨⟩, exact ⟨⟨⟩, _, A1.writeq h5⟩ },
    -- { rintro _ _ ⟨_, _, ⟨⟩, B1⟩,
    --   cases (A1.writeq h5).determ B1,
    --   refine ⟨_, _, ⟨h2, rfl⟩, _, _, ⟨h3, rfl⟩, _, h4, h5⟩ } },
    -- split,
    -- { rintro ⟨_, _, ⟨⟩, _, _, ⟨h2, rfl⟩, _, _, ⟨h3, rfl⟩, ⟨⟩, _, h4⟩,
    --   exact ⟨_, _, _, _, h1.ea, h2, h3, h4⟩ },
    -- { rintro ⟨_, _, _, _, h1', h2, h3, h4⟩,
    --   cases h1.ea.determ h1',
    --   exact ⟨_, _, ⟨_⟩, _, _, ⟨h2, rfl⟩, _, _, ⟨h3, rfl⟩, ⟨⟩, _, h4⟩ } },
  -- case hla.asm1.cmpxchg : sz a r {
  --   rcases ha with ⟨rm, h1, rfl⟩,
  --   split,
  --   { rintro ⟨_, _, ⟨⟩, _, _, ⟨h2, rfl⟩, _, _, ⟨h3, rfl⟩, h4⟩,
  --     exact ⟨_, _, _, h1.ea, h2, h3, h4⟩ },
  --   { rintro ⟨_, _, _, h1', h2, h3, h4⟩,
  --     cases h1.ea.determ h1',
  --     exact ⟨_, _, ⟨_⟩, _, _, ⟨h2, rfl⟩, _, _, ⟨h3, rfl⟩, h4⟩ } },
  -- case hla.asm1.xadd : sz a r {
  --   rcases ha with ⟨rm, h1, rfl⟩,
  --   split,
  --   { rintro ⟨_, _, ⟨⟩, _, _, ⟨h2, rfl⟩, _, _, ⟨h3, rfl⟩, ⟨⟩, _, h4⟩,
  --     exact ⟨_, _, _, _, h1.ea, h2, h3, h4⟩ },
  --   { rintro ⟨_, _, _, _, h1', h2, h3, h4⟩,
  --     cases h1.ea.determ h1',
  --     exact ⟨_, _, ⟨_⟩, _, _, ⟨h2, rfl⟩, _, _, ⟨h3, rfl⟩, ⟨⟩, _, h4⟩, } },
  -- case hla.asm1.cmov : c sz d s {
  --   rcases ha with ⟨ds, h1, rfl⟩,
  --   change _ ↔ cond _ _ _,
  --   split,
  --   { rintro ⟨_, _, ⟨⟩, h2⟩, dsimp only at h2,
  --     revert h2, cases c.read k.flags,
  --     { rintro ⟨⟩, exact rfl },
  --     { rintro ⟨_, _, ⟨h3, rfl⟩, h4⟩,
  --       exact ⟨_, ⟨_, h1.src, h3⟩, _, h1.dest, h4⟩ } },
  --   { intro h2, refine ⟨_, _, ⟨_⟩, _⟩, dsimp only,
  --     revert h2, cases c.read k.flags,
  --     { rintro ⟨⟩, exact ⟨_, _⟩ },
  --     { rintro ⟨_, ⟨_, hs, h3⟩, _, hd, h4⟩,
  --       cases h1.dest.determ hd,
  --       cases h1.src.determ hs,
  --       exact ⟨_, _, ⟨h3, rfl⟩, h4⟩ } } },
  -- case hla.asm1.setcc : c b a {
  --   rcases ha with ⟨rm, h1, rfl⟩,
  --   split,
  --   { rintro ⟨_, _, ⟨⟩, h2⟩,
  --     exact ⟨_, h1.ea, h2⟩ },
  --   { rintro ⟨_, h1', h2⟩,
  --     cases h1.ea.determ h1',
  --     exact ⟨_, _, ⟨_⟩, h2⟩ } },
  -- iterate 2 {
  --   rcases ha with ⟨rm, h1, rfl⟩,
  --   split,
  --   { exact λ h2, ⟨_, h1, h2⟩ },
  --   { rintro ⟨_, h1', h2⟩,
  --     cases h1.determ h1',
  --     exact h2 } },
  -- case hla.asm1.leave {
  --   cases ha, split,
  --   { rintro ⟨_, _, ⟨_, _, ⟨h2, rfl⟩, h3⟩, h4⟩,
  --     cases EA.readq_reg_64.1 h2,
  --     cases EA.writeq_reg_64.1 h3,
  --     exact h4 },
  --   { rintro h4,
  --     exact ⟨⟨⟩, _, ⟨_, _,
  --       ⟨EA.readq_reg_64.2 rfl, rfl⟩, EA.writeq_reg_64.2 rfl⟩, h4⟩ } },
  -- iterate 3 {
  --   cases ha, split,
  --   { rintro ⟨⟩, constructor },
  --   { rintro ⟨⟩, constructor } },
  -- case hla.asm1.syscall { cases ha, split; rintro ⟨⟨⟩⟩ },

  -- case hla.asm1.unop : op sz a {
  --   rcases ha with ⟨rm, h1, rfl⟩,
  --   split,
  --   { rintro ⟨_, _, ⟨⟩, q, _, ⟨h2, rfl⟩, h3⟩,
  --     exact ⟨_, _, h1.ea, h2, h3⟩ },
  --   { rintro ⟨ea, q, ⟨rm', h1', rfl⟩, h2, h3⟩,
  --     cases (arg.rm_imm_rm.1 h1).determ h1',
  --     exact ⟨_, _, ⟨_⟩, q, _, ⟨h2, rfl⟩, h3⟩ } },
  -- case hla.asm1.binop : op sz d s {
  --   rcases ha with ⟨ds, h1, rfl⟩,
  --   split,
  --   { rintro ⟨⟨ea, d', s'⟩, _, ⟨⟨d, s, h2, h3⟩, rfl⟩, h4⟩,
  --     exact ⟨_, _, _, h1.dest, h2, ⟨_, h1.src, h3⟩, h4⟩ },
  --   { rintro ⟨_, d', s', hd, h3, ⟨s'', hs, _, h4, rfl⟩, h5⟩,
  --     cases h1.dest.determ hd,
  --     cases h1.src.determ hs,
  --     exact ⟨⟨_, _, _⟩, _, ⟨⟨_, _, h3, _, h4, rfl⟩, rfl⟩, h5⟩ } },
  -- case hla.asm1.mul : sz a {
  --   rcases ha with ⟨rm, h1, rfl⟩,
  --   split,
  --   { rintro ⟨q, _, ⟨h2, rfl⟩, _, _, ⟨⟩,
  --       q2, _, ⟨h3, rfl⟩, ⟨⟩, k1, h4, h5⟩,
  --     refine ⟨_, _, _, h2, ⟨_, h1.ea, h3⟩, _, h5⟩,
  --     cases sz, exact h4,
  --     all_goals { rcases h4 with ⟨⟨⟩, k, h1, h2⟩, exact ⟨_, h1, h2⟩ } },
  --   { rintro ⟨q, w, k1, h2, ⟨_, h1', h3⟩, h4, h5⟩,
  --     cases h1.ea.determ h1',
  --     refine ⟨_, _, ⟨h2, rfl⟩, _, _, ⟨_⟩, _, _, ⟨h3, rfl⟩, ⟨⟩, _, _, h5⟩,
  --     cases sz, exact h4,
  --     all_goals { rcases h4 with ⟨_, h1, h2⟩, exact ⟨⟨⟩, _, h1, h2⟩ } } },
  -- case hla.asm1.div : sz a {
  --   rcases ha with ⟨rm, h1, rfl⟩,
  --   split,
  --   { rintro ⟨eax, _, ⟨h2, rfl⟩, edx, _, ⟨h3, rfl⟩, _, _, ⟨⟩, _, _,
  --       ⟨d, _, ⟨h4, rfl⟩⟩, ⟨⟩, _, ⟨⟨h5, h6⟩, rfl⟩, ⟨⟩, _, h7, ⟨⟩, _, h8⟩,
  --     exact ⟨_, _, _, _, _, h2, h3, ⟨_, h1.ea, h4⟩, h5, h6, h7, h8⟩ },
  --   { rintro ⟨_, _, _, _, _, h2, h3, ⟨_, h1', h4⟩, h5, h6, h7, h8⟩,
  --     cases h1.ea.determ h1',
  --     exact ⟨_, _, ⟨h2, rfl⟩, _, _, ⟨h3, rfl⟩, _, _, ⟨_⟩, _, _,
  --       ⟨_, _, _, ⟨h4, rfl⟩⟩, ⟨⟩, _, ⟨⟨h5, h6⟩, rfl⟩, ⟨⟩, _, h7, ⟨⟩, _, h8⟩ } },
  -- case hla.asm1.lea : sz d s {
  --   rcases ha with ⟨ds, h1, rfl⟩,
  --   split,
  --   { rintro ⟨_, _, ⟨⟩, h2⟩,
  --     exact ⟨_, h1.src, _, h1.dest, h2⟩ },
  --   { rintro ⟨_, hs, _, hd, h2⟩,
  --     cases h1.dest.determ hd,
  --     cases h1.src.determ hs,
  --     exact ⟨_, _, ⟨_⟩, h2⟩ } },
  -- iterate 2 {
  --   rcases ha with ⟨ds, h1, rfl⟩,
  --   split,
  --   { rintro ⟨_, _, ⟨h2, rfl⟩, _, _, ⟨⟩, h3⟩,
  --     exact ⟨_, ⟨_, h1.src, h2⟩, _, h1.dest, h3⟩ },
  --   { rintro ⟨_, ⟨_, hs, h2⟩, _, hd, h3⟩,
  --     cases h1.dest.determ hd,
  --     cases h1.src.determ hs,
  --     exact ⟨_, _, ⟨h2, rfl⟩, _, _, ⟨_⟩, h3⟩ } },
  -- case hla.asm1.xchg : sz a r {
  --   rcases ha with ⟨rm, h1, rfl⟩,
  --   split,
  --   { rintro ⟨_, _, ⟨⟩, _, _, ⟨h2, rfl⟩, _, _, ⟨h3, rfl⟩, ⟨⟩, _, h4⟩,
  --     exact ⟨_, _, _, _, h1.ea, h2, h3, h4⟩ },
  --   { rintro ⟨_, _, _, _, h1', h2, h3, h4⟩,
  --     cases h1.ea.determ h1',
  --     exact ⟨_, _, ⟨_⟩, _, _, ⟨h2, rfl⟩, _, _, ⟨h3, rfl⟩, ⟨⟩, _, h4⟩ } },
  -- case hla.asm1.cmpxchg : sz a r {
  --   rcases ha with ⟨rm, h1, rfl⟩,
  --   split,
  --   { rintro ⟨_, _, ⟨⟩, _, _, ⟨h2, rfl⟩, _, _, ⟨h3, rfl⟩, h4⟩,
  --     exact ⟨_, _, _, h1.ea, h2, h3, h4⟩ },
  --   { rintro ⟨_, _, _, h1', h2, h3, h4⟩,
  --     cases h1.ea.determ h1',
  --     exact ⟨_, _, ⟨_⟩, _, _, ⟨h2, rfl⟩, _, _, ⟨h3, rfl⟩, h4⟩ } },
  -- case hla.asm1.xadd : sz a r {
  --   rcases ha with ⟨rm, h1, rfl⟩,
  --   split,
  --   { rintro ⟨_, _, ⟨⟩, _, _, ⟨h2, rfl⟩, _, _, ⟨h3, rfl⟩, ⟨⟩, _, h4⟩,
  --     exact ⟨_, _, _, _, h1.ea, h2, h3, h4⟩ },
  --   { rintro ⟨_, _, _, _, h1', h2, h3, h4⟩,
  --     cases h1.ea.determ h1',
  --     exact ⟨_, _, ⟨_⟩, _, _, ⟨h2, rfl⟩, _, _, ⟨h3, rfl⟩, ⟨⟩, _, h4⟩, } },
  -- case hla.asm1.cmov : c sz d s {
  --   rcases ha with ⟨ds, h1, rfl⟩,
  --   change _ ↔ cond _ _ _,
  --   split,
  --   { rintro ⟨_, _, ⟨⟩, h2⟩, dsimp only at h2,
  --     revert h2, cases c.read k.flags,
  --     { rintro ⟨⟩, exact rfl },
  --     { rintro ⟨_, _, ⟨h3, rfl⟩, h4⟩,
  --       exact ⟨_, ⟨_, h1.src, h3⟩, _, h1.dest, h4⟩ } },
  --   { intro h2, refine ⟨_, _, ⟨_⟩, _⟩, dsimp only,
  --     revert h2, cases c.read k.flags,
  --     { rintro ⟨⟩, exact ⟨_, _⟩ },
  --     { rintro ⟨_, ⟨_, hs, h3⟩, _, hd, h4⟩,
  --       cases h1.dest.determ hd,
  --       cases h1.src.determ hs,
  --       exact ⟨_, _, ⟨h3, rfl⟩, h4⟩ } } },
  -- case hla.asm1.setcc : c b a {
  --   rcases ha with ⟨rm, h1, rfl⟩,
  --   split,
  --   { rintro ⟨_, _, ⟨⟩, h2⟩,
  --     exact ⟨_, h1.ea, h2⟩ },
  --   { rintro ⟨_, h1', h2⟩,
  --     cases h1.ea.determ h1',
  --     exact ⟨_, _, ⟨_⟩, h2⟩ } },
  -- iterate 2 {
  --   rcases ha with ⟨rm, h1, rfl⟩,
  --   split,
  --   { exact λ h2, ⟨_, h1, h2⟩ },
  --   { rintro ⟨_, h1', h2⟩,
  --     cases h1.determ h1',
  --     exact h2 } },
  -- case hla.asm1.leave {
  --   cases ha, split,
  --   { rintro ⟨_, _, ⟨_, _, ⟨h2, rfl⟩, h3⟩, h4⟩,
  --     cases EA.readq_reg_64.1 h2,
  --     cases EA.writeq_reg_64.1 h3,
  --     exact h4 },
  --   { rintro h4,
  --     exact ⟨⟨⟩, _, ⟨_, _,
  --       ⟨EA.readq_reg_64.2 rfl, rfl⟩, EA.writeq_reg_64.2 rfl⟩, h4⟩ } },
  -- iterate 3 {
  --   cases ha, split,
  --   { rintro ⟨⟩, constructor },
  --   { rintro ⟨⟩, constructor } },
  -- case hla.asm1.syscall { cases ha, split; rintro ⟨⟨⟩⟩ },
  repeat {sorry}
end

-- theorem terminator.exec_ok {H labs rip t v}
--   (ha : terminator.pred t H labs rip v) {k k'} :
--   execute a' k k' ↔ a.exec k k' :=

theorem code_pred.cons_ok {a b H k labs}
  (h : (code_pred.cons a b).ok H k labs) : a.ok H k labs := sorry

def hla_ok {α} (F : pstate config α) : Prop :=
∀ {{H : hla}} {{a k k'}}, (F k).P a k' → H.ok k → H.ok k'

theorem hla_ok.pure {α} {a : α} : hla_ok (pure a) :=
by rintro H a k k' ⟨⟩; exact id

theorem hla_ok.return {α} {a : α} : hla_ok (return a) :=
hla_ok.pure

theorem hla_ok.bind {α β} {m : pstate config α} {f : α → pstate config β}
  (H1 : hla_ok m) (H2 : ∀ b, hla_ok (f b)) :
  hla_ok (m >>= f) :=
by rintro H a k k' ⟨a, k1, h1, h2⟩ h; exact H2 _ h2 (H1 h1 h)

theorem hla_ok.map {α β} {m : pstate config α} {f : α → β}
  (H1 : hla_ok m) : hla_ok (f <$> m) :=
by rintro H a k k' ⟨a, h1, h2⟩; exact H1 h2

theorem hla_ok.lift {α} {f : config → α → config → Prop}
  (H : ∀ {{H : hla}} {{a k k'}}, f k a k' → H.ok k → H.ok k') :
  hla_ok (pstate.lift f) := H

theorem hla_ok.get : hla_ok pstate.get :=
by rintro H a k k' ⟨⟩; exact id

theorem hla_ok.assert {α} {p : config → α → Prop} :
  hla_ok (pstate.assert p) :=
by rintro H a k k' ⟨_, rfl⟩; exact id

theorem hla_ok.modify {f : config → config}
  (h : ∀ {{H : hla}} {{k}}, H.ok k → H.ok (f k)) :
  hla_ok (pstate.modify f) :=
by rintro H _ k k' ⟨_, rfl⟩; apply h

theorem hla_ok.any {α} {p : config → α → Prop} :
  hla_ok (@pstate.any _ α) :=
hla_ok.assert

theorem hla_ok.fail {α} {p : config → α → Prop} :
  hla_ok (@pstate.fail _ α) :=
hla_ok.assert

/-
theorem hla_ok_mem_read {H : hla} {k k' : config}
  (h1 : ∀ p q v, k.mem.read' p q v →
    ∃ v', list.length v' = v.length ∧ k'.mem.read' p q v') :
  H.ok k → H.ok k'
| ⟨h2, h3⟩ := begin
  refine ⟨λ b q n m, _, λ q n ll v m, _⟩,
  { rcases h2 b q n m with ⟨v1, rfl, h4⟩,
    exact h1 _ _ _ h4 },
  { rcases h2 b q n m with ⟨v1, rfl, h4⟩,
    have := h3 q n ll v' m,
  }
end

theorem hla_ok_mem_eq {H : hla} {k k' : config}
  (e : k.mem = k'.mem) (h : H.ok k) : H.ok k' :=
_

theorem hla_ok.write_rip {q} : hla_ok (write_rip q) :=
hla_ok.modify $ λ H k, _

theorem hla.ok.step {H : hla} {k k' : config}
  (hk : H.ok k) (h : k.step k') : H.ok k' :=
begin
  cases h with _ _ _ _ _ h,
end

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
-/

end hla