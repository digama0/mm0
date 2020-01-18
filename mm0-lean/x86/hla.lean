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

def arg.imm_rm : arg → imm_rm → Prop
| (arg.reg r) rm := imm_rm.rm (RM.reg r) = rm
| (arg.mem ix b d) rm := imm_rm.rm (RM.mem ix b d) = rm
| (arg.imm q) rm := imm_rm.imm q = rm
| _ _ := false

def arg.rm : arg → RM → Prop
| (arg.reg r) rm := RM.reg r = rm
| (arg.mem ix b d) rm := RM.mem ix b d = rm
| _ _ := false

theorem arg.rm_imm_rm {a rm} :
  arg.rm a rm ↔ arg.imm_rm a (imm_rm.rm rm) :=
by cases a; simp [arg.rm, arg.imm_rm]

def assemble_ds (d s : arg) : dest_src → Prop
| (dest_src.Rm_i rm q) := arg.rm d rm ∧ s = arg.imm q
| (dest_src.Rm_r rm r) := arg.rm d rm ∧ s = arg.reg r
| (dest_src.R_rm r rm) := arg.rm d (RM.reg r) ∧ arg.rm s rm

def code_pred := hla → list qword → qword → list byte → Prop

def asm1.pred' : asm1 → ast → Prop
| (asm1.unop op sz a) v := ∃ rm,
  a.rm rm ∧
  ast.unop op sz rm = v
| (asm1.binop op sz d s) v := ∃ ds,
  assemble_ds d s ds ∧
  ast.binop op sz ds = v
| (asm1.mul sz a) v := ∃ rm,
  a.rm rm ∧
  ast.mul sz rm = v
| (asm1.div sz a) v := ∃ rm,
  a.rm rm ∧
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
  a.rm rm ∧
  ast.xchg sz rm r = v
| (asm1.cmpxchg sz a r) v := ∃ rm,
  a.rm rm ∧
  ast.cmpxchg sz rm r = v
| (asm1.xadd sz a r) v := ∃ rm,
  a.rm rm ∧
  ast.xadd sz rm r = v
| (asm1.cmov c sz d s) v := ∃ ds,
  assemble_ds d s ds ∧
  ast.cmov c sz ds = v
| (asm1.setcc c b a) v := ∃ rm,
  a.rm rm ∧
  ast.setcc c b rm = v
| (asm1.push a) v := ∃ rm,
  a.imm_rm rm ∧
  ast.push rm = v
| (asm1.pop a) v := ∃ rm,
  a.rm rm ∧
  ast.pop rm = v
| asm1.leave v := ast.leave = v
| asm1.cmc v := ast.cmc = v
| asm1.clc v := ast.clc = v
| asm1.stc v := ast.stc = v
| asm1.syscall v := ast.syscall = v

theorem arg.imm_rm.determ {a rm1 rm2} : arg.imm_rm a rm1 → a.imm_rm rm2 → rm1 = rm2 :=
by cases a; rintro ⟨⟩ ⟨⟩; refl

theorem arg.rm.determ {a rm1 rm2} : arg.rm a rm1 → arg.rm a rm2 → rm1 = rm2 :=
by cases a; rintro ⟨⟩ ⟨⟩; refl

def arg.ea (k : config) (a : arg) (ea : EA) : Prop :=
∃ rm, arg.imm_rm a rm ∧ imm_rm.ea k rm = ea

theorem arg.ea.determ {k a ea1 ea2} : arg.ea k a ea1 → a.ea k ea2 → ea1 = ea2 :=
by rintro ⟨_, h1, rfl⟩ ⟨_, h2, rfl⟩; cases h1.determ h2; refl

theorem arg.imm_rm.ea {a rm k} (h : arg.imm_rm a rm) : arg.ea k a (rm.ea k) :=
by cases a; cases h; exact ⟨_, rfl, rfl⟩

theorem arg.rm.ea {a rm k} (h : arg.rm a rm) : arg.ea k a (rm.ea k) :=
(arg.rm_imm_rm.1 h).ea

theorem assemble_ds.src {d s ds k}
  (h : assemble_ds d s ds) : arg.ea k s (ea_src k ds) :=
begin
  cases ds; cases h,
  { subst s, exact ⟨_, rfl, rfl⟩ },
  { subst s, refine ⟨_, rfl, rfl⟩ },
  { exact h_right.ea },
end

theorem assemble_ds.dest {d s ds k}
  (h : assemble_ds d s ds) : arg.ea k d (ea_dest k ds) :=
by cases ds; cases h; exact h_left.ea

def arg.read (k : config) (a : arg) (sz : wsize) (w : bitvec sz.to_nat) : Prop :=
∃ ea, arg.ea k a ea ∧ ea.read k sz w

def arg.readq (k : config) (a : arg) (sz : wsize) (q : qword) : Prop :=
∃ ea, arg.ea k a ea ∧ ea.readq k sz q

def arg.writeq (k : config) (a : arg) (sz : wsize) (q : qword) (k' : config) : Prop :=
∃ ea, arg.ea k a ea ∧ ea.writeq k sz q k'

def asm1.exec (k k' : config) : asm1 → Prop
| (asm1.unop op sz rm) := ∃ ea w,
  arg.ea k rm ea ∧ ea.readq k sz w ∧
  write_unop sz w ea op k k'
| (asm1.binop op sz d s) := ∃ ea d' s',
  arg.ea k d ea ∧ ea.readq k sz d' ∧
  s.readq k sz s' ∧
  write_binop sz ea d' s' op k k'
| (asm1.mul sz r) := ∃ eax src k2,
  (EA.EA_r RAX).readq k sz eax ∧
  r.readq k sz src ∧
  match sz with
  | (wsize.Sz8 _) :=
    (EA.EA_r RAX).writeq k wsize.Sz16 (eax * src) k2
  | _ := ∃ k1,
    let hi := bitvec.of_nat sz.to_nat
      ((eax.to_nat * src.to_nat).shiftl sz.to_nat) in
    (EA.EA_r RAX).writeq k sz (eax * src) k1 ∧
    (EA.EA_r RDX).writeq k1 sz (EXTZ hi) k2
  end ∧
  erase_flags k2 k'
| (asm1.div sz r) := ∃ eax edx d k1 k2,
  (EA.EA_r RAX).readq k sz eax ∧
  (EA.EA_r RDX).readq k sz edx ∧
  let n := edx.to_nat * (2 ^ sz.to_nat) + eax.to_nat in
  r.readq k sz d ∧
  let d := bitvec.to_nat d in
  d ≠ 0 ∧ n / d < 2 ^ sz.to_nat ∧
  (EA.EA_r RAX).writeq k sz (bitvec.of_nat _ (n / d)) k1 ∧
  (EA.EA_r RDX).writeq k1 sz (bitvec.of_nat _ (n % d)) k2 ∧
  erase_flags k2 k'
| (asm1.lea sz d s) := ∃ sea,
  arg.ea k s sea ∧
  d.writeq k sz sea.addr k'
| (asm1.movsx sz1 d s sz2) := ∃ w,
  s.read k sz1 w ∧
  d.writeq k sz2 (EXTZ (EXTS w : bitvec sz2.to_nat)) k'
| (asm1.movzx sz1 d s sz2) := ∃ w,
  s.read k sz1 w ∧
  d.writeq k sz2 (EXTZ w) k'
| (asm1.xchg sz r n) := ∃ dst val_src val_dst k1,
  let src := EA.EA_r n in
  r.ea k dst ∧
  src.readq k sz val_src ∧
  dst.readq k sz val_dst ∧
  src.writeq k sz val_dst k1 ∧
  dst.writeq k1 sz val_src k'
| (asm1.cmpxchg sz r n) := ∃ dst val_dst val_acc,
  let src := EA.EA_r n, acc := EA.EA_r RAX in
  r.ea k dst ∧
  dst.readq k sz val_dst ∧
  acc.readq k sz val_acc ∧
  (do
    write_binop sz src val_acc val_dst binop.cmp,
    if val_acc = val_dst then
      src.read' sz >>= dst.write' sz
    else acc.write' sz val_dst) k k'
| (asm1.xadd sz r n) := ∃ dst val_src val_dst k1,
  let src := EA.EA_r n in
  r.ea k dst ∧
  src.readq k sz val_src ∧
  dst.readq k sz val_dst ∧
  src.writeq k sz val_dst k1 ∧
  write_binop sz dst val_src val_dst binop.add k1 k'
| (asm1.cmov c sz d s) :=
  cond (c.read k.flags)
    (∃ w, s.readq k sz w ∧ d.writeq k sz w k')
    (k = k')
| (asm1.setcc c b r) :=
  r.writeq k (wsize.Sz8 b) (EXTZ $ bitvec.singleton $ c.read k.flags) k'
| (asm1.push i) := ∃ i',
  arg.imm_rm i i' ∧ push i' k k'
| (asm1.pop r) := ∃ r',
  arg.rm r r' ∧ pop r' k k'
| asm1.leave :=
  pop (RM.reg RBP) (k.set_reg RSP (k.regs RBP)) k'
| asm1.clc := k' = {flags := {CF := ff, ..k.flags}, ..k}
| asm1.cmc := k' = {flags := {CF := bnot k.flags.CF, ..k.flags}, ..k}
| asm1.stc := k' = {flags := {CF := tt, ..k.flags}, ..k}
| asm1.syscall := false

def noIO_rel (P : config → config → Prop) : kcfg → kcfg → Prop
| ⟨i, o, k⟩ ⟨i', o', k'⟩ := i = i' ∧ o = o' ∧ P k k'

def asm1.kexec : kcfg → kcfg → asm1 → Prop
| ⟨i, o, k⟩ ⟨i', o', k'⟩ asm1.syscall := ∃ k1 k2 ret,
  config.isIO k k1 ∧
  exec_io i o k1 (k1.regs RAX) i' o' k2 ret →
  k' = k2.set_reg RAX ret
| ⟨i, o, k⟩ ⟨i', o', k'⟩ a := i = i' ∧ o = o' ∧ a.exec k k'

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
| (bblock.cons a b) k k' := ∃ k1, a.kexec k k1 ∧ b.kexec k1 k'
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

theorem asm1.exec_ok {a a'} (ha : asm1.pred' a a') {k k'} :
  execute a' k k' ↔ a.exec k k' :=
begin
  change (execute a' k).P () k' ↔ _,
  cases a,
  case hla.asm1.unop : op sz a {
    rcases ha with ⟨rm, h1, rfl⟩,
    split,
    { rintro ⟨_, _, ⟨⟩, q, _, ⟨h2, rfl⟩, h3⟩,
      exact ⟨_, _, h1.ea, h2, h3⟩ },
    { rintro ⟨ea, q, ⟨rm', h1', rfl⟩, h2, h3⟩,
      cases (arg.rm_imm_rm.1 h1).determ h1',
      exact ⟨_, _, ⟨_⟩, q, _, ⟨h2, rfl⟩, h3⟩ } },
  case hla.asm1.binop : op sz d s {
    rcases ha with ⟨ds, h1, rfl⟩,
    split,
    { rintro ⟨⟨ea, d', s'⟩, _, ⟨⟨d, s, h2, h3⟩, rfl⟩, h4⟩,
      exact ⟨_, _, _, h1.dest, h2, ⟨_, h1.src, h3⟩, h4⟩ },
    { rintro ⟨_, d', s', hd, h3, ⟨s'', hs, _, h4, rfl⟩, h5⟩,
      cases h1.dest.determ hd,
      cases h1.src.determ hs,
      exact ⟨⟨_, _, _⟩, _, ⟨⟨_, _, h3, _, h4, rfl⟩, rfl⟩, h5⟩ } },
  case hla.asm1.mul : sz a {
    rcases ha with ⟨rm, h1, rfl⟩,
    split,
    { rintro ⟨q, _, ⟨h2, rfl⟩, _, _, ⟨⟩,
        q2, _, ⟨h3, rfl⟩, ⟨⟩, k1, h4, h5⟩,
      refine ⟨_, _, _, h2, ⟨_, h1.ea, h3⟩, _, h5⟩,
      cases sz, exact h4,
      all_goals { rcases h4 with ⟨⟨⟩, k, h1, h2⟩, exact ⟨_, h1, h2⟩ } },
    { rintro ⟨q, w, k1, h2, ⟨_, h1', h3⟩, h4, h5⟩,
      cases h1.ea.determ h1',
      refine ⟨_, _, ⟨h2, rfl⟩, _, _, ⟨_⟩, _, _, ⟨h3, rfl⟩, ⟨⟩, _, _, h5⟩,
      cases sz, exact h4,
      all_goals { rcases h4 with ⟨_, h1, h2⟩, exact ⟨⟨⟩, _, h1, h2⟩ } } },
  case hla.asm1.div : sz a {
    rcases ha with ⟨rm, h1, rfl⟩,
    split,
    { rintro ⟨eax, _, ⟨h2, rfl⟩, edx, _, ⟨h3, rfl⟩, _, _, ⟨⟩, _, _,
        ⟨d, _, ⟨h4, rfl⟩⟩, ⟨⟩, _, ⟨⟨h5, h6⟩, rfl⟩, ⟨⟩, _, h7, ⟨⟩, _, h8⟩,
      exact ⟨_, _, _, _, _, h2, h3, ⟨_, h1.ea, h4⟩, h5, h6, h7, h8⟩ },
    { rintro ⟨_, _, _, _, _, h2, h3, ⟨_, h1', h4⟩, h5, h6, h7, h8⟩,
      cases h1.ea.determ h1',
      exact ⟨_, _, ⟨h2, rfl⟩, _, _, ⟨h3, rfl⟩, _, _, ⟨_⟩, _, _,
        ⟨_, _, _, ⟨h4, rfl⟩⟩, ⟨⟩, _, ⟨⟨h5, h6⟩, rfl⟩, ⟨⟩, _, h7, ⟨⟩, _, h8⟩ } },
  case hla.asm1.lea : sz d s {
    rcases ha with ⟨ds, h1, rfl⟩,
    split,
    { rintro ⟨_, _, ⟨⟩, h2⟩,
      exact ⟨_, h1.src, _, h1.dest, h2⟩ },
    { rintro ⟨_, hs, _, hd, h2⟩,
      cases h1.dest.determ hd,
      cases h1.src.determ hs,
      exact ⟨_, _, ⟨_⟩, h2⟩ } },
  iterate 2 {
    rcases ha with ⟨ds, h1, rfl⟩,
    split,
    { rintro ⟨_, _, ⟨h2, rfl⟩, _, _, ⟨⟩, h3⟩,
      exact ⟨_, ⟨_, h1.src, h2⟩, _, h1.dest, h3⟩ },
    { rintro ⟨_, ⟨_, hs, h2⟩, _, hd, h3⟩,
      cases h1.dest.determ hd,
      cases h1.src.determ hs,
      exact ⟨_, _, ⟨h2, rfl⟩, _, _, ⟨_⟩, h3⟩ } },
  case hla.asm1.xchg : sz a r {
    rcases ha with ⟨rm, h1, rfl⟩,
    split,
    { rintro ⟨_, _, ⟨⟩, _, _, ⟨h2, rfl⟩, _, _, ⟨h3, rfl⟩, ⟨⟩, _, h4⟩,
      exact ⟨_, _, _, _, h1.ea, h2, h3, h4⟩ },
    { rintro ⟨_, _, _, _, h1', h2, h3, h4⟩,
      cases h1.ea.determ h1',
      exact ⟨_, _, ⟨_⟩, _, _, ⟨h2, rfl⟩, _, _, ⟨h3, rfl⟩, ⟨⟩, _, h4⟩ } },
  case hla.asm1.cmpxchg : sz a r {
    rcases ha with ⟨rm, h1, rfl⟩,
    split,
    { rintro ⟨_, _, ⟨⟩, _, _, ⟨h2, rfl⟩, _, _, ⟨h3, rfl⟩, h4⟩,
      exact ⟨_, _, _, h1.ea, h2, h3, h4⟩ },
    { rintro ⟨_, _, _, h1', h2, h3, h4⟩,
      cases h1.ea.determ h1',
      exact ⟨_, _, ⟨_⟩, _, _, ⟨h2, rfl⟩, _, _, ⟨h3, rfl⟩, h4⟩ } },
  case hla.asm1.xadd : sz a r {
    rcases ha with ⟨rm, h1, rfl⟩,
    split,
    { rintro ⟨_, _, ⟨⟩, _, _, ⟨h2, rfl⟩, _, _, ⟨h3, rfl⟩, ⟨⟩, _, h4⟩,
      exact ⟨_, _, _, _, h1.ea, h2, h3, h4⟩ },
    { rintro ⟨_, _, _, _, h1', h2, h3, h4⟩,
      cases h1.ea.determ h1',
      exact ⟨_, _, ⟨_⟩, _, _, ⟨h2, rfl⟩, _, _, ⟨h3, rfl⟩, ⟨⟩, _, h4⟩, } },
  case hla.asm1.cmov : c sz d s {
    rcases ha with ⟨ds, h1, rfl⟩,
    change _ ↔ cond _ _ _,
    split,
    { rintro ⟨_, _, ⟨⟩, h2⟩, dsimp only at h2,
      revert h2, cases c.read k.flags,
      { rintro ⟨⟩, exact rfl },
      { rintro ⟨_, _, ⟨h3, rfl⟩, h4⟩,
        exact ⟨_, ⟨_, h1.src, h3⟩, _, h1.dest, h4⟩ } },
    { intro h2, refine ⟨_, _, ⟨_⟩, _⟩, dsimp only,
      revert h2, cases c.read k.flags,
      { rintro ⟨⟩, exact ⟨_, _⟩ },
      { rintro ⟨_, ⟨_, hs, h3⟩, _, hd, h4⟩,
        cases h1.dest.determ hd,
        cases h1.src.determ hs,
        exact ⟨_, _, ⟨h3, rfl⟩, h4⟩ } } },
  case hla.asm1.setcc : c b a {
    rcases ha with ⟨rm, h1, rfl⟩,
    split,
    { rintro ⟨_, _, ⟨⟩, h2⟩,
      exact ⟨_, h1.ea, h2⟩ },
    { rintro ⟨_, h1', h2⟩,
      cases h1.ea.determ h1',
      exact ⟨_, _, ⟨_⟩, h2⟩ } },
  iterate 2 {
    rcases ha with ⟨rm, h1, rfl⟩,
    split,
    { exact λ h2, ⟨_, h1, h2⟩ },
    { rintro ⟨_, h1', h2⟩,
      cases h1.determ h1',
      exact h2 } },
  case hla.asm1.leave {
    cases ha, split,
    { rintro ⟨_, _, ⟨_, _, ⟨h2, rfl⟩, h3⟩, h4⟩,
      cases EA.readq_reg_64.1 h2,
      cases EA.writeq_reg_64.1 h3,
      exact h4 },
    { rintro h4,
      exact ⟨⟨⟩, _, ⟨_, _,
        ⟨EA.readq_reg_64.2 rfl, rfl⟩, EA.writeq_reg_64.2 rfl⟩, h4⟩ } },
  iterate 3 {
    cases ha, split,
    { rintro ⟨⟩, constructor },
    { rintro ⟨⟩, constructor } },
  case hla.asm1.syscall { cases ha, split; rintro ⟨⟨⟩⟩ },
end

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