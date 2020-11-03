import x86.lemmas data.set.lattice data.list.basic data.list.alist

namespace x86

inductive flag_place | CFP | ZFP | SFP | OFP

def flag_place.read (f : flags) : flag_place → bool
| flag_place.CFP := f.CF
| flag_place.ZFP := f.ZF
| flag_place.SFP := f.SF
| flag_place.OFP := f.OF

def flag_place.write (f : flags) (b : bool) : flag_place → flags
| flag_place.CFP := {CF := b, ..f}
| flag_place.ZFP := {ZF := b, ..f}
| flag_place.SFP := {SF := b, ..f}
| flag_place.OFP := {OF := b, ..f}

inductive place
| flag : flag_place → place
| reg : regnum → place
| rip : place
| mem : qword → place

inductive place.read (k : config) : place → ∀ {n}, bitvec n → Prop
| flag {f} : place.read (place.flag f) (bitvec.singleton (f.read k.flags))
| reg {r} : place.read (place.reg r) (k.regs r)
| rip : place.read place.rip k.rip
| mem {a b} : k.mem.read1 perm.R a b → place.read (place.mem a) b

inductive place.write (k : config) : place → ∀ {n}, bitvec n → config → Prop
| flag {f b} : place.write (place.flag f) (bitvec.singleton b) {flags := f.write k.flags b, ..k}
| reg {r n q} : place.write (place.reg r) q (k.write_reg r n q)
| rip {q} : place.write place.rip q {rip := q, ..k}
| mem {a b m'} : k.mem.write1 a b m' → place.write (place.mem a) b {mem := m', ..k}

inductive heaplet
| flag : flag_place → bool → heaplet
| reg : regnum → qword → heaplet
| rip : qword → heaplet
| mem : qword → perm → byte → heaplet

def heaplet.place : heaplet → place
| (heaplet.flag fp b) := place.flag fp
| (heaplet.reg r q)   := place.reg r
| (heaplet.rip q)     := place.rip
| (heaplet.mem a p v) := place.mem a

def heaplet.value : heaplet → Σ n, bitvec n
| (heaplet.flag fp b) := ⟨_, bitvec.singleton b⟩
| (heaplet.reg r q)   := ⟨_, q⟩
| (heaplet.rip q)     := ⟨_, q⟩
| (heaplet.mem a p v) := ⟨_, v⟩

def heaplet.read (k : config) : heaplet → Prop
| (heaplet.flag fp b) := fp.read k.flags = b
| (heaplet.reg r q)   := k.regs r = q
| (heaplet.rip q)     := k.rip = q
| (heaplet.mem a p v) := k.mem.read1 p a v

def split {α} (H h₁ h₂ : set α) : Prop :=
H = h₁ ∪ h₂ ∧ disjoint h₁ h₂

theorem sProp.split_comm {α} {h1 h2 h : set α} :
  split h h1 h2 ↔ split h h2 h1 := sorry

theorem sProp.split_assoc {α} {h1 h2 h3 h : set α} :
  (∃ h23, split h23 h2 h3 ∧ split h h1 h23) ↔
  (∃ h12, split h12 h1 h2 ∧ split h h12 h3) := sorry

@[reducible] def heap := set heaplet
def sProp := heap → Prop

def config.heap (k : config) : heap := {h | h.read k}

def sProp.sep (P Q : sProp) : sProp :=
λ S, ∃ S₁ S₂, split S S₁ S₂ ∧ P S₁ ∧ Q S₂

def sProp.sepish (P Q : sProp) : sProp :=
λ S, ∃ S₁ S₂, S = S₁ ∪ S₂ ∧ P S₁ ∧ Q S₂

instance : has_mul sProp := ⟨sProp.sep⟩
theorem sProp.sep_comm (P Q : sProp) : P * Q = Q * P := sorry
theorem sProp.sep_assoc (P Q R : sProp) : P * Q * R = P * (Q * R) := sorry

def sProp.wand (P Q : sProp) : sProp :=
λ S₂, ∀ S₁ S, split S S₁ S₂ → P S₁ → Q S

theorem sProp.sep_wand (P Q R : sProp) :
  (P * Q).wand R = P.wand (Q.wand R) :=
begin
  funext h, apply propext, split,
  { rintro H h' S s p a b c d,
    obtain ⟨e,f,g⟩ := sProp.split_assoc.1 ⟨_, s, c⟩,
    exact H _ _ g ⟨_, _, sProp.split_comm.1 f, p, d⟩, },
  { rintro H h' S s ⟨a,b,c,d,e⟩,
    obtain ⟨x,f,g⟩ := sProp.split_assoc.2 ⟨_, sProp.split_comm.1 c, s⟩,
    refine H _ _ f d _ _ g e }
end

def heap.sn (H : heap) : sProp := eq H

def heaplet.sn (h : heaplet) : sProp := heap.sn {h}

def emp : sProp := heap.sn ∅

def lift (p : Prop) : sProp := λ _, p

instance lattice.complete_lattice.sProp : complete_lattice sProp :=
pi.complete_lattice

theorem sProp.wand_mp (P Q : sProp) : P * P.wand Q ≤ Q :=
λ h ⟨a,b,c,d,H⟩, H _ _ c d

def sProp.with (p : sProp) (q : Prop) : sProp := p ⊓ lift q

def liftE (p : Prop) : sProp := sProp.with emp p

def sProp.ex {α} (p : α → sProp) : sProp := λ S, ∃ a, p a S

def sProp.al {α} (p : α → sProp) : sProp := λ S, ∀ a, p a S

constant heap.sat : heap → config → Prop
constant config.ok : config → Prop

def s_weak (P Q : sProp) : Prop := ∀ h, P h → ∃ h', Q h' ∧ h' ⊆ h
axiom s_weak.sat {P Q} (H : s_weak P Q) :
  ∀ k, (∃ h, P h ∧ h.sat k) → (∃ h, Q h ∧ h.sat k)

theorem s_sep.weak₁ {P Q} : s_weak (P * Q) P :=
by rintro k ⟨h, h1, ⟨rfl, h2⟩, h3, h4⟩;
   exact ⟨_, h3, λ _, or.inl⟩
theorem s_sep.weak₂ {P Q} : s_weak (P * Q) Q :=
by rw sProp.sep_comm; exact s_sep.weak₁

theorem el_s_sep_sn {x y z : heap} : (x.sn * y.sn) z ↔ split z x y := sorry
theorem s_sep_sn {x y z : heap} : x.sn * y.sn = z.sn ↔ split z x y := sorry

theorem s_sep.mono_right {P Q : sProp} (R) (H : P ≤ Q) : R * P ≤ R * Q :=
λ a ⟨b,c,d,e,f⟩, ⟨b,c,d,e, H _ f⟩
theorem s_sep.mono_left {P Q : sProp} (R) (H : P ≤ Q) : P * R ≤ Q * R :=
λ a ⟨b,c,d,e,f⟩, ⟨b,c,d, H _ e, f⟩

theorem s_sep.weak_right {P Q} (R) (H : s_weak P Q) : s_weak (R * P) (R * Q) :=
by rintro x ⟨a,b,⟨rfl,c⟩,d,e⟩; obtain ⟨f,g,h⟩ := H _ e;
  exact ⟨_, ⟨_, _, ⟨rfl,c.mono_right h⟩, d, g⟩,
    set.union_subset_union_right _ h⟩
theorem s_sep.weak_left {P Q} (R) : s_weak P Q → s_weak (P * R) (Q * R) :=
by rw [sProp.sep_comm P, sProp.sep_comm Q]; exact s_sep.weak_right _

def s_ok (P : sProp) : Prop :=
∀ k h, P h → heap.sat h k → k.ok

theorem s_ok_sep {R P} : s_ok (R * P) ↔ ∀ fr, R fr → s_ok (fr.sn * P) := sorry

def hoare' (P Q : sProp) : Prop :=
∀ fr:heap, s_ok (fr.sn * Q) → s_ok (fr.sn * P)

theorem s_weak.hoare {P Q} (H : s_weak P Q) : hoare' P Q :=
by rintro fr H' k h hp b;
  obtain ⟨c,d,e⟩ := (s_sep.weak_right _ H).sat k ⟨_, hp, b⟩;
  exact H' _ _ d e

theorem hoare'.frame_ok {P Q R} :
  hoare' P Q → s_ok (R * Q) → s_ok (R * P) := sorry
theorem hoare'.ok {P Q} : hoare' P Q → s_ok Q → s_ok P := sorry
theorem hoare_frame {P Q} (R) : hoare' P Q → hoare' (R * P) (R * Q) := sorry

theorem unframe (R P Q : sProp) (A)
  (hA : ∀ h, P h → heaplet.place '' h ∩ A = ∅)
  (H : ∀ h:heap, heaplet.place '' h = A →
    hoare' (h.sn * P) (h.sn * Q)) : hoare' P Q :=
begin
  rintro fr hQ k p ⟨_, a, hp, ⟨⟩, hP⟩ pk,
  have := hA _ hP,
  obtain ⟨x:heap, y, z, w, u, hx1, hx2, hx3, hx4, hx5⟩ :
    ∃ x y z w u:heap,
    heaplet.place '' x = A ∧
    split y w p ∧
    split x z w ∧
    split fr z u ∧ y.sat k,
  { sorry },
  have : s_ok (u.sn * (x.sn * Q)),
  { refine (s_weak.hoare _).ok hQ,
    rw ← sProp.sep_assoc,
    apply s_sep.weak_left,
    rw [← s_sep_sn.2 hx4, sProp.sep_comm],
    apply s_sep.weak_left,
    rw [← s_sep_sn.2 hx3],
    exact s_sep.weak₁ },
  have := H _ hx1 u this,
  rw [← sProp.sep_assoc, ← s_sep_sn.2 hx3,
    ← sProp.sep_assoc, sProp.sep_comm u.sn,
    s_sep_sn.2 hx4, sProp.sep_comm fr.sn, sProp.sep_assoc] at this,
  refine this k _ ⟨_, _, hx2, ⟨_⟩, _, _, hp, ⟨_⟩, hP⟩ hx5,
end

theorem sep_le_sep {P₁ P₂ Q₁ Q₂ : sProp}
  (H₁ : P₁ ≤ Q₁) (H₂ : P₂ ≤ Q₂) : P₁ * P₂ ≤ Q₁ * Q₂ :=
λ S ⟨S₁, S₂, h₁, h₂, h₃⟩, ⟨S₁, S₂, h₁, H₁ _ h₂, H₂ _ h₃⟩

def place.clob (p : place) : sProp :=
sProp.ex $ λ h:heaplet, h.sn.with (h.place = p)

def sProp.flags (f : flags) : sProp :=
sProp.al $ λ p, (heaplet.flag p $ p.read f).sn

inductive block
| reg : regnum → wsize → block
| mem : qword → qword → block
| const : list byte → block

def block.size : block → qword
| (block.reg _ sz) := (sz.to_nat / 8 : ℕ)
| (block.mem _ sz) := sz
| (block.const l) := l.length

inductive block.places : block → set place
| reg {r sz} : block.places (block.reg r sz) (place.reg r)
| mem {a b sz : qword} :
  (bitvec.sub b a).to_nat ≤ sz.to_nat →
  block.places (block.mem a sz) (place.mem b)

def block.disj (b1 b2 : block) := disjoint b1.places b2.places

def sProp.mem_block (p : perm) : qword → list byte → sProp
| a [] := emp
| a (b :: v) :=
  sProp.ex (λ q, (heaplet.mem a q b).sn.with (p ≤ q)) *
  sProp.mem_block (a + 1) v

theorem sProp.mem_block.mono {p₁ p₂} (h : p₁ ≤ p₂) :
  ∀ {a v}, sProp.mem_block p₂ a v ≤ sProp.mem_block p₁ a v
| a [] := le_refl _
| a (b :: v) := sep_le_sep
  (λ S ⟨q, h₁, h₂⟩, ⟨q, h₁, le_trans h h₂⟩)
  sProp.mem_block.mono

def block.read : block → list byte → sProp
| (block.reg r sz) v := sProp.ex $ λ q,
  (heaplet.reg r q).sn.with $ read_full_imm sz q v
| (block.mem a sz) v := (sProp.mem_block perm.R a v).with $ v.length = sz.to_nat
| (block.const l) v := liftE $ v = l

def block.readW : block → list byte → sProp
| (block.reg r sz) v := sProp.ex $ λ q,
  (heaplet.reg r q).sn.with $ read_full_imm sz q v
| (block.mem a sz) v := (sProp.mem_block (perm.R + perm.W) a v).with $ v.length = sz.to_nat
| (block.const l) v := lift false

theorem block.read.size : ∀ {b v k},
  block.read b v k → v.length = b.size.to_nat := sorry

theorem block.readW_le_read : ∀ {b v},
  block.readW b v ≤ block.read b v
| (block.reg r sz) v := le_refl _
| (block.mem a sz) v := λ s ⟨h₁, h₂⟩,
  ⟨sProp.mem_block.mono perm.le_add_left _ h₁, h₂⟩
| (block.const l) v := by rintro _ ⟨⟩

def hoare (P : kcfg → Prop) (Q : kcfg → Prop) :=
∀ {{k}}, P k → hoare_p Q k

def sHoareIO (P : sProp) (Q : list byte → list byte → sProp) :=
∀ i₁ o₁ R, hoare
  (λ ⟨i, o, k⟩, (P * R) k.heap ∧ i = i₁ ∧ o = o₁)
  (λ ⟨i₂, o₂, k₂⟩, ∃ i' o', i₁ = i' ++ i₂ ∧ o₂ = o₁ ++ o' ∧ (Q i' o' * R) k₂.heap)

def noIO (Q : sProp) (i o : list byte) : sProp := Q.with (i = [] ∧ o = [])
def sHoare (P Q : sProp) := sHoareIO P (noIO Q)
def sHoareW (C P Q : sProp) := sHoare (P * C) (Q * C)

def locals_ctx := alist (λ _ : ℕ, block)

def locals_ctx.get (Γ : locals_ctx) (n : ℕ) : option block := Γ.lookup n

def labels_ctx := qword × list qword

def labels_ctx.cons (q : qword) (L : labels_ctx) : labels_ctx :=
⟨L.1, q :: L.2⟩

structure asm_ctx :=
(L : list qword)
(Γ : alist (λ _ : ℕ, block))
(exit : qword)
(die : ∃ l, sHoare ((heaplet.rip exit).sn ⊓
  sProp.mem_block (perm.R + perm.X) exit l) ⊥)

def asm_ctx.read (A : asm_ctx) (n : ℕ) : option block := A.Γ.lookup n

def asm_ctx.push_local (A : asm_ctx) (i : ℕ) (b : block) : asm_ctx :=
⟨A.1, A.2.insert i b, A.3, A.4⟩

def asm_ctx.push_label (A : asm_ctx) (q : qword) : asm_ctx :=
⟨q :: A.1, A.2, A.3, A.4⟩

inductive exit_kind
| straight
| label (n : ℕ)

def exit_kind.result (A : asm_ctx) (pos : qword) : exit_kind → sProp
| exit_kind.straight := (heaplet.rip pos).sn
| (exit_kind.label n) := sProp.ex $ λ h, (heaplet.rip (A.1.nth_le n h)).sn

def stmt : Type :=
asm_ctx → set place →
∀ rip : qword, list byte → Prop

def stmt.hoareIO (A) (P : sProp) (C : stmt)
  (Q : exit_kind → list byte → list byte → sProp) : Prop :=
∀ D rip l, C A D rip l →
  sHoareIO (P * (heaplet.rip rip).sn *
      sProp.mem_block (perm.R + perm.X) rip l)
    (λ i o, sProp.ex $ λ e,
      Q e i o * e.result A (rip + l.length) *
      sProp.mem_block (perm.R + perm.X) rip l)

def stmt.hoare (A P C) (Q : exit_kind → sProp) : Prop :=
stmt.hoareIO A P C (λ e, noIO (Q e))

def hstmt (P Q : sProp) : stmt :=
λ L Γ rip v, sHoareW (sProp.mem_block (perm.R + perm.X) rip v)
  (P * (heaplet.rip rip).sn)
  (Q * (heaplet.rip (rip + v.length)).sn)

def hstmtW (C P Q : sProp) : stmt := hstmt (P * C) (Q * C)

instance complete_lattice.stmt : complete_lattice stmt :=
pi.complete_lattice

def stmt.all {α} (s : α → stmt) : stmt :=
λ A D rip v, ∀ a, s a A D rip v

def stmt.ex {α} (s : α → stmt) : stmt :=
λ A D rip v, ∃ a, s a A D rip v

def stmt.with (p : Prop) (s : stmt) : stmt :=
stmt.ex $ λ h : p, s

def stmt.or (s₁ s₂ : stmt) : stmt :=
λ A D rip v, s₁ A D rip v ∨ s₂ A D rip v

def expr (α : Type) := block → stmt

instance complete_lattice.expr {α} : complete_lattice (expr α) :=
pi.complete_lattice

def expr.hoareIO {α} (A) (P : sProp) (E : expr α)
  (Q : block → list byte → list byte → sProp) : Prop :=
∀ b, (E b).hoareIO A P $
  λ e i o, (Q b i o).with (e = exit_kind.straight)

def expr.hoare {α} (A) (P : sProp) (E : expr α) (Q : block → sProp) : Prop :=
expr.hoareIO A P E (λ ret i o, noIO (Q ret) i o)

class value (α : Type*) :=
(size : ℕ)
(eval : α → list byte → Prop)
(eval_eq : ∀ {{a l}}, eval a l → l.length = size)

def value.evalB {α} [value α] (x : α) (b : block) : sProp :=
sProp.ex $ λ l, (block.read b l).with $ value.eval x l

def value.read_sized {α} [value α] (a : qword) (x : α) (b : block) : sProp :=
(value.evalB x b).with (b = block.mem a (value.size α))

class type (α : Type*) :=
(size : ℕ)
(read : α → block → sProp)
(read_eq : ∀ {{a b s}}, read a b s → b.size.to_nat = size)

instance (α) [value α] : type α :=
⟨value.size α,
  λ a b, sProp.ex $ λ v,
    (block.read b v).with (value.eval a v),
  λ a b s ⟨v, h₁, h₂⟩, by rw [← h₁.size, @value.eval_eq α _ a v h₂]⟩

def bits.value {n} (m : ℕ) : value (bitvec n) :=
⟨m, bits_to_byte m, λ a v h, h.1⟩

instance unit.value : value unit :=
⟨0, λ _ v, v = [], by rintro _ _ ⟨⟩; refl⟩

instance byte.value : value byte :=
⟨1, λ b v, v = [b], by rintro _ _ ⟨⟩; refl⟩

instance word.value : value word := bits.value 4
instance qword.value : value qword := bits.value 8

class box (α) [type α] := (deref : α)

instance box.type (α) [type α] : type (box α) :=
⟨8, λ x b, sProp.ex $ λ a, sProp.ex $ λ v,
  (block.read b v).with (qword.to_list_byte a v) *
  type.read x.deref (block.mem a (type.size α)),
  λ x b s ⟨a, v, _, _, _, ⟨h₁, h₂, _⟩, _⟩,
    by rw [← h₁.size, h₂]⟩

def ret (α) (b : block) : expr α :=
λ bl A D a v, bl = b ∧ v = []

def const (α) (l : list byte) : expr α := ret α (block.const l)

def name (α : Type) := ℕ

def var {α} (i : name α) : expr α :=
λ bl A D a v, bl ∈ A.read i ∧ v = []

def hexpr {α} (P : sProp) (Q : block → sProp) : expr α :=
λ ret, hstmt P (Q ret)

def hexprW {α} (C P : sProp) (Q : block → sProp) : expr α :=
λ ret, hstmtW C P (Q ret)

def expr.all {α β} (e : α → expr β) : expr β :=
λ ret, stmt.all $ λ a, e a ret

def expr.ex {α β} (e : α → expr β) : expr β :=
λ ret, stmt.ex $ λ a, e a ret

def expr.with {α} (p : Prop) (s : expr α) : expr α :=
expr.ex $ λ h : p, s

def const' {α} [type α] (a : α) : expr α := hexpr ⊤ $ type.read a

inductive stmt.seq (s₁ s₂ : stmt) : stmt
| mk {A D rip v₁ v₂} :
  s₁ A D rip v₁ →
  s₂ A D (rip + v₁.length) v₂ →
  stmt.seq A D rip (v₁ ++ v₂)

inductive expr.bindS {α} (e₁ : expr α) (s₂ : block → stmt) : stmt
| mk {b A D rip v₁ v₂} :
  e₁ b A D rip v₁ →
  s₂ b A D (rip + v₁.length) v₂ →
  expr.bindS A D rip (v₁ ++ v₂)

def expr.bind {α β} (e₁ : expr α) (e₂ : block → expr β) : expr β :=
λ b₂, expr.bindS e₁ $ λ b₁, e₂ b₁ b₂

def block.mov (dst src : block) : stmt :=
λ A D rip v, dst.size = src.size ∧ ∀ val P,
sProp.ex (block.readW dst) * P ≤ block.read src val →
hstmtW P (sProp.ex (block.readW dst)) (block.readW dst val) A D rip v

def expr.set {α} (e₁ e₂ : expr α) : stmt :=
expr.bindS e₁ $ λ dst, expr.bindS e₂ $ λ src, block.mov dst src

inductive label | fail | label (n : ℕ)

inductive label.loc (A : asm_ctx) : label → qword → Prop
| fail : label.loc label.fail A.exit
| label (n h) : label.loc (label.label n) (A.L.nth_le n h)

def stmt.jump_cc (p : flags → bool) (l : label) : stmt :=
λ A D rip v, ∀ tgt, l.loc A tgt →
sHoareW (sProp.mem_block (perm.R + perm.X) rip v)
  (sProp.ex sProp.flags * (heaplet.rip rip).sn)
  (sProp.ex $ λ f, sProp.flags f *
    (heaplet.rip (cond (p f) tgt (rip + v.length))).sn)

def stmt.jump : label → stmt := stmt.jump_cc (λ _, tt)

def boolexpr := (flags → bool) → stmt

def boolexpr.hoare (A) (P : sProp) (E : boolexpr) (Q : bool → sProp) : Prop :=
∃ p, stmt.hoare A (sProp.ex sProp.flags * P) (E p)
  (λ e, sProp.ex $ λ f, sProp.flags f *
    (Q (p f)).with (e = exit_kind.straight))

def boolexpr.not (c : boolexpr) : boolexpr :=
λ p, c (bnot ∘ p)

def boolexpr.jump_if (c : boolexpr) (l : label) : stmt :=
stmt.ex $ λ p, (c p).seq $ stmt.jump_cc p l

def stmt.nop : stmt := λ A D rip v, v = []

def if_stmt (c : boolexpr) (s₁ s₂ : stmt) : stmt :=
stmt.ex $ λ p, stmt.seq (c p) $ λ A D rip v,
∃ v₁ v₂ v₃, v = v₁ ++ v₂ ++ v₃ ∧
let q₁ := rip + v₁.length, q₂ := q₁ + v₂.length in
stmt.jump_cc (bnot ∘ p) (label.label 0) (A.push_label q₁) D rip v₁ ∧
s₁.seq (stmt.jump (label.label 0)) (A.push_label q₂) D q₁ v₂ ∧
s₂.seq (stmt.jump (label.label 0)) (A.push_label q₂) D q₂ v₃

def loop (s : stmt) : stmt :=
λ A D rip, s (A.push_label rip) D rip

def block_stmt (s : stmt) : stmt :=
λ A D rip v, s (A.push_label (rip + v.length)) D rip v

def while (c : boolexpr) (s : stmt) : stmt :=
block_stmt $ loop $
  (c.not.jump_if (label.label 1)).seq $
  s.seq $
  stmt.jump (label.label 0)

def decl_block {α} (b : block) (s : name α → stmt) : stmt :=
λ A D rip v, ∃ i, s i (A.push_local i b) D rip v

def decl {α} (sz : qword) (s : name α → stmt) : stmt :=
stmt.ex $ λ b, stmt.with (block.size b = sz) $ decl_block b s

def init {α} (e : expr α) (s : name α → stmt) : stmt :=
e.bindS $ λ b, decl_block b s

/-
def binop_expr {α β γ} [type α] [type β] [type γ]
  (f : α → β → γ) (e₁ : expr α) (e₂ : expr β) : expr γ :=
e₁.bind $ λ b₁, e₂.bind $ λ b₂ b, stmt.all $ λ x, stmt.all $ λ y,
hstmt (type.read' x b₁ ⊓ type.read' y b₂) (type.write (f x y) b)

def asn_binop {α β} [type α] [type β] (f : α → β → α) (e₁ : expr α) (e₂ : expr β) : stmt :=
e₁.bindS $ λ b₁, (ret α b₁).set (binop_expr f (ret α b₁) e₂)

def unop_expr {α β} [type α] [type β]
  (f : α → β) (e : expr α) : expr β :=
e.bind $ λ b₁ b, stmt.ex $ λ x,
hstmt (type.read' x b₁) (type.write (f x) b)

def asn_unop {α} [type α] (f : α → α) (e : expr α) : stmt :=
e.bindS $ λ b, (ret α b).set (unop_expr f (ret α b))

def for {α} (start : expr α) (test : name α → boolexpr) (incr body : name α → stmt) : stmt :=
init start $ λ i, while (test i) $ (body i).seq (incr i)

def incr {α} [type α] [has_add α] [has_one α] : expr α → stmt :=
asn_unop (+ 1)

def bool_binop {α β} [type α] [type β]
  (f : α → β → bool) (e₁ : expr α) (e₂ : expr β) : boolexpr :=
λ p, e₁.bindS $ λ b₁, e₂.bindS $ λ b₂, stmt.ex $ λ x, stmt.ex $ λ y,
hstmt (type.read' x b₁ ⊓ type.read' y b₂)
  (mProp.final mProp.id (λ k, p k.flags = f x y))

def ltq (e₁ e₂ : expr qword) : boolexpr :=
bool_binop (λ a b : qword, a.to_nat < b.to_nat) e₁ e₂

def for_seq (sz : qword) (max : expr qword) (body : name qword → stmt) : stmt :=
for (const' (0 : qword)) (λ i, ltq (const' 0) max) (λ i, incr (var i)) body

----------------------------------------
-- Assembly
----------------------------------------

theorem hoare.mono {P Q : kcfg → set place → Prop}
  (H : ∀ {{k S}}, P k S → Q k S) : hoare P Q :=
λ k S p, hoare_p.zero (H p)

theorem hoare.step {P P' Q : kcfg → set place → Prop}
  (h₁ : ∀ {{k S}}, P k S → ∃ k', k.step k')
  (h₂ : ∀ {{k S}}, P k S → ∀ {{k'}}, k.step k' → P' k' S)
  (h₃ : hoare P' Q) : hoare P Q :=
λ k S p, hoare_p.step (h₁ p) (λ k' s, h₃ (h₂ p s))

theorem hoare.mono_l {P P' Q : kcfg → set place → Prop}
  (H : ∀ {{k S}}, P k S → P' k S) : hoare P' Q → hoare P Q :=
λ H' k S h, H' (H h)

theorem hoare_p.mono_l {P P' : kcfg → set place → Prop}
  (H : ∀ {{k S}}, P k S → P' k S) {k S} : hoare_p P k S → hoare_p P' k S :=
begin
  intro h, induction h,
  exact hoare_p.zero (H h_a),
  exact hoare_p.step h_a (λ k', h_ih _),
  exact hoare_p.exit _ _ _ h_a (λ e, H (h_a_1 e)),
end

theorem hoare.mono_r {P Q Q' : kcfg → set place → Prop}
  (H : ∀ {{k S}}, Q k S → Q' k S) : hoare P Q → hoare P Q' :=
λ H' k S h, hoare_p.mono_l H (H' h)

theorem sHoareIO.mono {P : sProp} {Q : list byte → list byte → sProp}
  (H : ∀ {{k S}}, P k S → Q [] [] k S) : sHoareIO P Q :=
λ i o, hoare.mono $ by rintro k S ⟨h, rfl, rfl⟩; exact
  ⟨[], [], rfl, (list.append_nil _).symm, H h⟩

theorem sHoareIO.mono_l {P P' : sProp} {Q : list byte → list byte → sProp}
  (H : ∀ {{k S}}, P k S → P' k S) : sHoareIO P' Q → sHoareIO P Q :=
λ h i o, hoare.mono_l (by exact λ k S ⟨h₁, h₂⟩, ⟨H h₁, h₂⟩) (@h i o)

theorem sHoareIO.mono_r {P : sProp} {Q Q' : list byte → list byte → sProp}
  (H : ∀ {{i o k S}}, Q i o k S → Q' i o k S) : sHoareIO P Q → sHoareIO P Q' :=
λ h i o, hoare.mono_r (by exact λ k S ⟨i', o', h₁, h₂, h₃⟩,
  ⟨i', o', h₁, h₂, H h₃⟩) (@h i o)

theorem sHoareIO.step {P P' : sProp} {Q : list byte → list byte → sProp}
  (h₁ : ∀ ⦃k i o S⦄, P k S → ∃ k', kcfg.step ⟨i, o, k⟩ k')
  (h₂ : ∀ {{k₁ i₁ o₁ k₂ i₂ o₂ S}}, P k₁ S →
    kcfg.step ⟨i₁, o₁, k₁⟩ ⟨i₂, o₂, k₂⟩ → P' k₂ S ∧ i₂ = i₁ ∧ o₂ = o₁)
  (h₃ : sHoareIO P' Q) : sHoareIO P Q :=
λ i o, hoare.step (λ ⟨i', o', k⟩ S h, h₁ h.1)
  (by rintro ⟨i₁, o₁, k₁⟩ S ⟨h, rfl, rfl⟩ ⟨i₂, o₂, k₂⟩ h'; exact
    @h₂ k₁ i₁ o₁ k₂ i₂ o₂ S h h')
  (@h₃ i o)

theorem sHoareIO.asm (P : sProp) (Q : list byte → list byte → sProp) :
  sHoareIO P Q :=
λ i o, sorry

theorem sHoare.mono {P Q : sProp} (H : ∀ {{k S}}, P k S → Q k S) : sHoare P Q :=
sHoareIO.mono $ λ k S h, ⟨H h, rfl, rfl⟩

theorem sHoare.mono_l {P P' Q : sProp}
  (H : ∀ {{k S}}, P k S → P' k S) : sHoare P' Q → sHoare P Q :=
sHoareIO.mono_l H

theorem sHoare.mono_r {P Q Q' : sProp}
  (H : ∀ {{k S}}, Q k S → Q' k S) : sHoare P Q → sHoare P Q' :=
sHoareIO.mono_r $ λ i o k S ⟨h₁, h₂⟩, ⟨H h₁, h₂⟩

theorem config.isIO_terminal {k} :
  (∃ k', config.step k k') → ¬ ∃ k', k.isIO k' := sorry

theorem sHoare.step {P P' Q : sProp}
  (h₁ : ∀ ⦃k S⦄, P k S → ∃ k', config.step k k')
  (h₂ : ∀ ⦃k S⦄, P k S → ∀ k', config.step k k' → P' k' S) :
  sHoare P' Q → sHoare P Q :=
sHoareIO.step
  (λ k i o S h, let ⟨k', h'⟩ := h₁ h in ⟨_, kcfg.step.noio h'⟩)
  (λ k₁ i₁ o₁ k₂ i₂ o₂ S h h', begin
    cases h', exact ⟨h₂ h _ h'_a, rfl, rfl⟩,
    cases config.isIO_terminal (h₁ h) ⟨_, h'_a⟩
  end)

def stmt.asm {n} (s : stmt n) := Π L Γ rip, ∃ v, s L Γ rip v

theorem hstmt.step {n} {P P' Q : sProp}
  (h₁ : ∀ (L : labels_ctx) (Γ : locals_ctx n) rip,
    ∃ l, ∀ v k S,
    (P * sProp.sn place.rip rip *
        sProp.mem_block (perm.R + perm.X) rip (l ++ v)) k S →
    ∃ a k', decode a l ∧
      (write_rip (k.rip + bitvec.of_nat 64 l.length) k).P () k' ∧
      (execute a k').P () k ∧
      ∀ H, P k H → P' k' H)
  (h₂ : (@hstmt n P' Q).asm)
  : (@hstmt n P Q).asm :=
λ L Γ rip, let ⟨l, H⟩ := h₁ L Γ rip, ⟨v, H₂⟩ := h₂ L Γ rip in
⟨l ++ v, begin
  refine sHoare.step (λ k S h, _) (λ k S h k', _) (sHoare.mono_r _ H₂),
  { rcases H v k S h with ⟨a, k', h₃, h₄, h₅, h₆⟩,
    have : mem.readX (k.mem) (k.rip) l, sorry,
    exact ⟨k, this, h₃, (), k', h₄, h₅⟩ },
  { rintro ⟨l, a, _, m, d, h⟩,
    sorry },
  sorry,
end⟩

theorem hstmt.asm {n} (P : sProp) (Q : sProp) : (@hstmt n P Q).asm :=
sorry
-/

end x86