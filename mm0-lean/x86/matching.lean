import x86.lemmas data.set.lattice data.list.basic data.pfun data.list.alist

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

def place.stable (k k' : config) : place → Prop
| (place.flag f) := f.read k.flags = f.read k'.flags
| (place.reg r) := k.regs r = k'.regs r
| place.rip := k.rip = k'.rip
| (place.mem a) :=
  roption.mk (k.mem.valid a) (λ h, (k.mem.mem a h, k.mem.perm a h)) =
  roption.mk (k'.mem.valid a) (λ h, (k'.mem.mem a h, k'.mem.perm a h))

theorem place.stable.refl (k p) : place.stable k k p :=
by cases p; exact rfl

theorem place.stable.trans {k₁ k₂ k₃ p}
  (h₁ : place.stable k₁ k₂ p) (h₂ : place.stable k₂ k₃ p) : place.stable k₁ k₃ p :=
by cases p; exact eq.trans h₁ h₂

theorem mem.read1.stable {k k' a} (s : place.stable k k' (place.mem a))
  {p b} : mem.read1 p k.mem a b → mem.read1 p k'.mem a b :=
@@eq.subst (λ o : roption (byte × perm),
  ∃ (h : o.1), b = (o.2 h).1 ∧ p ≤ (o.2 h).2) s

theorem place.read.stable {k k'} : ∀ {p}, place.stable k k' p →
  ∀ {n v}, @place.read k p n v → place.read k' p v :=
begin
  rintro p s n v h, induction h,
  { rw show _=_, from s, constructor },
  { rw show _=_, from s, constructor },
  { rw show _=_, from s, constructor },
  { exact place.read.mem (mem.read1.stable s h_a_1) }
end

def stability (k k' : config) : set place := {p | place.stable k k' p}

def split {α} (H h₁ h₂ : set α) : Prop :=
H = h₁ ∪ h₂ ∧ disjoint h₁ h₂

def sProp := config → Prop

def sProp.stable (P : sProp) (D : set place) : Prop :=
∀ k k', D ⊆ stability k k' → P k → P k'

def sProp.reserve (S : set place) : sProp :=
λ k, ∀ p ∈ S, ∃ n v, @place.read k p n v

theorem sProp.reserve.stable {S D : set place} (h : S ⊆ D) :
  (sProp.reserve S).stable D :=
λ k k' h' H p hp, let ⟨n, v, hp'⟩ := H p hp in
  ⟨n, v, place.read.stable (h' (h hp)) hp'⟩

def mProp := config → config → Prop

def mProp.exterior (P : mProp) : set place :=
{p | ∀ k k', P k k' → place.stable k k' p}

def mProp.dom (P : mProp) : set place := (P.exterior)ᶜ

def stable_at (D : set place) : mProp := λ k k', D ⊆ stability k k'

theorem stable_at.refl {D k} : stable_at D k k :=
λ x _, place.stable.refl _ _

theorem stable_at.trans {D k₁ k₂ k₃}
  (h₁ : stable_at D k₁ k₂) (h₂ : stable_at D k₂ k₃) : stable_at D k₁ k₃ :=
λ x h, place.stable.trans (h₁ h) (h₂ h)

def mProp.initial (Q : mProp) (P : sProp) : mProp := λ k k', Q k k' ∧ P k
def mProp.final (Q : mProp) (P : sProp) : mProp := λ k k', Q k k' ∧ P k'

def mProp.apply (Q : mProp) (P : sProp) : sProp :=
λ k', ∃ k, P k ∧ Q k k'

def mProp.id : mProp := eq

def mProp.comp (P Q : mProp) : mProp :=
λ k₁ k₃, ∃ k₂, P k₁ k₂ ∧ Q k₂ k₃

def mProp.imp (P Q : mProp) : mProp :=
λ k₂ k₃, ∀ k₁, P k₁ k₂ → Q k₁ k₃

def slift (p : Prop) : sProp := λ _, p
def mlift (p : Prop) : mProp := λ _ _, p

instance lattice.complete_lattice.sProp : complete_lattice sProp :=
pi.complete_lattice

instance lattice.complete_lattice.mProp : complete_lattice mProp :=
pi.complete_lattice

def sProp.with (p : sProp) (q : Prop) : sProp := p ⊓ slift q
def mProp.with (p : mProp) (q : Prop) : mProp := p ⊓ mlift q

def sProp.ex {α} (p : α → sProp) : sProp := λ k, ∃ a, p a k
def mProp.ex {α} (p : α → mProp) : mProp := λ k k', ∃ a, p a k k'

def sProp.all {α} (p : α → sProp) : sProp := λ k, ∀ a, p a k
def mProp.all {α} (p : α → mProp) : mProp := λ k k', ∀ a, p a k k'

def sProp.sn (p : place) {n} (v : bitvec n) : sProp :=
λ k, p.read k v
def mProp.write (p : place) {n} (v' : bitvec n) : mProp :=
λ k k', p.write k v' k'
def mProp.sn (p : place) {n} (v v' : bitvec n) : mProp :=
(mProp.write p v').initial (sProp.sn p v)
def mProp.clob (p : place) {n} (v : bitvec n) : mProp :=
mProp.ex $ λ v', mProp.sn p v v'

def sProp.flags (f : flags) : sProp :=
sProp.all $ λ p : flag_place,
sProp.sn (place.flag p) (bitvec.singleton $ p.read f)

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

def sProp.mem_block (p : perm) (a : qword) (v : list byte) : sProp :=
λ k, k.mem.read' p a v

def block.read : block → list byte → sProp
| (block.reg r sz) v :=
  (sProp.reserve (block.reg r sz).places) ⊓ λ k,
    read_full_imm sz (k.regs r) v
| (block.mem a sz) v :=
  (sProp.reserve (block.mem a sz).places) ⊓ λ k,
    k.mem.read a v ∧ v.length = sz.to_nat
| (block.const l) v := slift $ v = l

def block.writable : block → sProp
| (block.reg r sz) := sProp.reserve (block.reg r sz).places
| (block.mem a sz) :=
  (sProp.reserve (block.mem a sz).places) ⊓ λ k,
    ∃ v, k.mem.read' perm.W a v ∧ v.length = sz.to_nat
| (block.const _) := slift false

def block.write : block → list byte → mProp
| (block.reg r sz) l k k' := ∃ v,
  @bits_to_byte (sz.to_nat * 8) sz.to_nat v l ∧
  mProp.write (place.reg r) v k k'
| (block.mem a sz) l k k' :=
  ∃ m', k.mem.write a l m' ∧ k' = {mem := m', ..k}
| (block.const _) _ _ _ := false

theorem block.read.size : ∀ {b v k},
  block.read b v k → v.length = b.size.to_nat := sorry

theorem block.write.size : ∀ {b v k k'},
  block.write b v k k' → v.length = b.size.to_nat := sorry

theorem block.read_write : ∀ {b v k k'},
  block.write b v k k' → block.read b v k' := sorry

theorem block.read.stable {l v k k'}
  (h₁ : block.read l v k) (ss : places l ⊆ stability k k') :
  block.read l v k' := sorry

def hoare (P : kcfg → Prop) (Q : kcfg → kcfg → Prop) :=
∀ {{k}}, P k → hoare_p (Q k) k

def mHoareIO (P : sProp) (Q : list byte → list byte → mProp) :=
hoare (λ k, P k.k)
  (λ k k', ∃ i' o', k.input = i' ++ k'.input ∧ k'.output = k.output ++ o' ∧
    (Q i' o') k.k k'.k)

def noIO (Q : mProp) (i o : list byte) : mProp := Q.with (i = [] ∧ o = [])
def mHoare (P : sProp) (Q : mProp) := mHoareIO P (noIO Q)

def locals_ctx := alist (λ _ : ℕ, block)

def locals_ctx.get (Γ : locals_ctx) (n : ℕ) : option block := Γ.lookup n

def labels_ctx := qword × list qword

def labels_ctx.cons (q : qword) (L : labels_ctx) : labels_ctx :=
⟨L.1, q :: L.2⟩

structure asm_ctx :=
(L : list qword)
(Γ : alist (λ _ : ℕ, block))
(exit : qword)
(die : ∃ l, mHoare (sProp.sn place.rip exit ⊓
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
| exit_kind.straight := sProp.sn place.rip pos
| (exit_kind.label n) := sProp.ex $ λ h, sProp.sn place.rip (A.1.nth_le n h)

def stmt : Type :=
asm_ctx → set place →
∀ rip : qword, list byte → Prop

def stmt.hoareIO (A) (P : sProp) (C : stmt)
  (Q : exit_kind → list byte → list byte → mProp) : Prop :=
∀ D rip l, C A D rip l →
  mHoareIO
    (P ⊓ sProp.sn place.rip rip ⊓
      sProp.mem_block (perm.R + perm.X) rip l)
    (λ i o, stable_at D ⊓
      mProp.ex (λ e, (Q e i o).final (e.result A (rip + l.length))))

def stmt.hoare (A) (P : sProp) (C : stmt) (Q : exit_kind → mProp) : Prop :=
stmt.hoareIO A P C (λ e i o, noIO (Q e) i o)

def hstmt (P : sProp) (Q : mProp) : stmt :=
λ A D rip v,
  mHoare (sProp.sn place.rip rip ⊓ sProp.mem_block (perm.R + perm.X) rip v)
    ((Q ⊓ stable_at D).final (sProp.sn place.rip (rip + v.length)))

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

def stmt.stabilize (S : set place) (s : stmt) : stmt :=
λ A D, s A (D ∪ S)

def expr (α : Type) := block → stmt

instance complete_lattice.expr {α} : complete_lattice (expr α) :=
pi.complete_lattice

def expr.hoareIO {α} (A) (P : sProp) (E : expr α)
  (Q : block → list byte → list byte → mProp) : Prop :=
∀ b, (E b).hoareIO A P $
  λ e i o, (Q b i o).with (e = exit_kind.straight)

def expr.hoare {α} (A) (P : sProp) (E : expr α) (Q : block → mProp) : Prop :=
expr.hoareIO A P E (λ ret i o, noIO (Q ret) i o)

def expr.stabilize {α} (S : set place) (s : expr α) : expr α :=
λ b, (s b).stabilize S

class value (α : Type*) :=
(size : ℕ)
(eval : α → list byte → Prop)
(eval_eq : ∀ {{a l}}, eval a l → l.length = size)

def value.evalB {α} [value α] (x : α) (b : block) : sProp :=
λ k, ∃ l, block.read b l k ∧ value.eval x l

def value.read_sized {α} [value α] (a : qword) (x : α) (b : block) : sProp :=
value.evalB x b ⊓ slift (b = block.mem a (value.size α))

class type (α : Type*) :=
(size : ℕ)
(read : α → block → set place → sProp)
(write : α → block → mProp)
(read_eq : ∀ {{a l s k}}, read a l s k → l.size.to_nat = size)
(write_eq : ∀ {{a l k k'}}, write a l k k' → l.size.to_nat = size)
(read_write : ∀ {{a l k k'}}, write a l k k' → ∃ s, read a l s k')
(read_stable : ∀ {{a l s k k'}},
  read a l s k → s ⊆ stability k k' → read a l s k')

def type.read' {α} [type α] (a : α) (b : block) : sProp :=
sProp.ex $ type.read a b

instance (α) [value α] : type α :=
⟨value.size α,
  λ a b s, sProp.ex $ λ v,
    block.read b v ⊓ slift (value.eval a v ∧ s = b.places),
  λ a b, mProp.ex $ λ v,
    block.write b v ⊓ mlift (value.eval a v),
  λ a b s k ⟨v, h₁, h₂, _⟩, by rw [← h₁.size, @value.eval_eq α _ a v h₂],
  λ a b k k' ⟨v, h₁, h₂⟩, by rw [← h₁.size, @value.eval_eq α _ a v h₂],
  λ a v k k' ⟨s, h₁, h₂⟩, ⟨_, _, block.read_write h₁, h₂, rfl⟩,
  λ a l s k k' ⟨v, h₁, h₂, e⟩ ss, ⟨v, h₁.stable (e ▸ ss), h₂, e⟩⟩

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
⟨8, λ x b s k, ∃ a l s',
    block.read b l k ∧
    qword.to_list_byte a l ∧
    type.read x.deref (block.mem a (type.size α)) s' k ∧
    s = b.places ∪ s',
  λ x b k k', ∃ a l s',
    block.write b l k k' ∧
    qword.to_list_byte a l ∧
    type.read x.deref (block.mem a (type.size α)) s' k',
  λ x b s k ⟨a, l, s', h₁, h₂, _⟩,
    by rw [← h₁.size, h₂.1],
  λ x b k k' ⟨a, l, s', h₁, h₂, _⟩,
    by rw [← h₁.size, h₂.1],
  λ x b k k' ⟨a, l, s', h₁, h₂, h₃⟩,
    ⟨_, _, _, _, block.read_write h₁, h₂, h₃, rfl⟩,
  λ x b s k k' ⟨a, l, s', h₁, h₂, h₃, e⟩ ss,
    let ⟨ss₁, ss₂⟩ := set.union_subset_iff.1 (by rwa e at ss) in
    ⟨a, l, s', h₁.stable ss₁, h₂, type.read_stable h₃ ss₂, e⟩⟩

def ret (α) (b : block) : expr α :=
λ bl A D a v, bl = b ∧ v = []

def const (α) (l : list byte) : expr α := ret α (block.const l)

def name (α : Type) := ℕ

def var {α} (i : name α) : expr α :=
λ bl A D a v, bl ∈ A.read i ∧ v = []

def hexpr {α} (P : sProp) (Q : block → mProp) : expr α :=
λ ret, hstmt P (Q ret)

def expr.all {α β} (e : α → expr β) : expr β :=
λ ret, stmt.all $ λ a, e a ret

def expr.ex {α β} (e : α → expr β) : expr β :=
λ ret, stmt.ex $ λ a, e a ret

def expr.with {α} (p : Prop) (s : expr α) : expr α :=
expr.ex $ λ h : p, s

def const' {α} [type α] (a : α) : expr α :=
hexpr ⊤ $ λ b, mProp.final mProp.id (type.read' a b)

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
stmt.with (dst.size = src.size) $
stmt.all $ λ val, hstmt (block.read src val) (block.write dst val)

def expr.set {α} (e₁ e₂ : expr α) : stmt :=
expr.bindS e₁ $ λ dst, expr.bindS e₂ $ λ src, block.mov dst src

inductive label | fail | label (n : ℕ)

inductive label.loc (A : asm_ctx) : label → qword → Prop
| fail : label.loc label.fail A.exit
| label (n h) : label.loc (label.label n) (A.L.nth_le n h)

def stmt.jump_cc (p : flags → bool) (l : label) : stmt :=
λ A D rip v, ∀ tgt, l.loc A tgt →
mHoare (sProp.sn place.rip rip ⊓ sProp.mem_block (perm.R + perm.X) rip v)
  (λ k k', stable_at D k k' ∧
    mProp.write place.rip (cond (p k.flags) tgt (rip + v.length)) k k')

def stmt.jump : label → stmt := stmt.jump_cc (λ _, tt)

def boolexpr := (flags → bool) → stmt

def boolexpr.hoare (A) (P : sProp) (E : boolexpr) (Q : bool → mProp) : Prop :=
∃ p, stmt.hoare A P (E p)
  (λ e k k', e = exit_kind.straight ∧ Q (p k'.flags) k k')

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
-- Program logic
----------------------------------------

theorem mProp.comp_imp {P Q} : mProp.comp P (mProp.imp P Q) ≤ Q :=
λ k₁ k₃ ⟨k₂, h₁, h₂⟩, h₂ _ h₁

theorem mProp.comp_ex_imp {α P Q} :
  mProp.comp (@mProp.ex α P) (mProp.all $ λ a, mProp.imp (P a) Q) ≤ Q :=
λ k₁ k₃ ⟨k₂, ⟨a, h₁⟩, h₂⟩, h₂ a _ h₁

theorem mProp.ex_apply {α Q P} :
  (@mProp.ex α Q).apply P = sProp.ex (λ a, (Q a).apply P) :=
funext $ λ k, propext
⟨λ ⟨k', h₁, a, h₂⟩, ⟨a, k', h₁, h₂⟩,
 λ ⟨a, k', h₁, h₂⟩, ⟨k', h₁, a, h₂⟩⟩

theorem mProp.ex_comp {α Q Q'} :
  (@mProp.ex α Q).comp Q' = mProp.ex (λ a, (Q a).comp Q') :=
funext $ λ k, funext $ λ k', propext
⟨λ ⟨k'', ⟨a, h₁⟩, h₂⟩, ⟨a, k'', h₁, h₂⟩,
 λ ⟨a, k'', h₁, h₂⟩, ⟨k'', ⟨a, h₁⟩, h₂⟩⟩

theorem mem.read'_left {m p a v₁ v₂} (ss : v₁ <+: v₂) :
  mem.read' m p a v₂ → mem.read' m p a v₁ :=
begin
  intro h, induction h generalizing v₁,
  { cases list.eq_nil_of_prefix_nil ss, constructor },
  { cases v₁, constructor,
    rcases ss with ⟨_, ⟨⟩⟩,
    exact mem.read'.cons h_a (h_ih ⟨_, rfl⟩) }
end

theorem mem.read'_right {m p a v₁ v₂} :
  mem.read' m p a (v₁ ++ v₂) → mem.read' m p (a + v₁.length) v₂ :=
begin
  generalize e : v₁ ++ v₂ = v,
  intro h, induction h generalizing v₁ v₂,
  { cases list.eq_nil_of_suffix_nil ⟨_, e⟩, constructor },
  { cases v₁; cases e,
    { simp, exact mem.read'.cons h_a h_a_1 },
    { simp [-add_comm], rw [← add_assoc, add_right_comm],
      exact h_ih rfl } }
end

theorem hoare.zero {P : kcfg → Prop} {Q : kcfg → kcfg → Prop}
  (H : ∀ {{k}}, P k → Q k k) : hoare P Q :=
λ k p, hoare_p.zero (H p)

theorem hoare.step {P P' : kcfg → Prop} {Q Q' : kcfg → kcfg → Prop}
  (h₁ : ∀ {{k}}, P k → ∃ k', k.step k')
  (h₂ : ∀ {{k}}, P k → ∀ {{k'}}, k.step k' → P' k' ∧ ∀ {{k''}}, Q' k' k'' → Q k k'')
  (h₃ : hoare P' Q') : hoare P Q :=
λ k p, hoare_p.step (h₁ p) (λ k' s, hoare_p.mono (h₂ p s).2 (h₃ (h₂ p s).1))

theorem hoare.mono_l {P P' : kcfg → Prop} {Q : kcfg → kcfg → Prop}
  (H : ∀ {{k}}, P k → P' k) : hoare P' Q → hoare P Q :=
λ H' k h, H' (H h)

theorem hoare.mono_r {P : kcfg → Prop} {Q Q' : kcfg → kcfg → Prop}
  (H : ∀ {{k k'}}, P k → Q k k' → Q' k k') : hoare P Q → hoare P Q' :=
λ H' k h, hoare_p.mono (λ k' h', H h (by exact h')) (H' h)

theorem hoare.comp {P : kcfg → Prop} {Q Q' : kcfg → kcfg → Prop}
  (H₁ : hoare P Q)
  (H₂ : hoare (λ k', ∃ k, Q k k' ∧ P k) Q') :
  hoare P (rel.comp Q Q') :=
λ k p, begin
  refine (hoare.mono_r _ H₁ p).bind _,
  exact (λ k k', Q k k' ∧ P k),
  rintro k' ⟨h₁, h₂⟩,
  refine (H₂ ⟨_, h₁, h₂⟩).mono (λ k₂ h, ⟨_, h₁, h⟩),
  exact λ k k' h₁ h₂, ⟨h₂, h₁⟩
end

theorem mHoareIO.zero {P : sProp} {Q : list byte → list byte → mProp}
  (H : ∀ {{k}}, P k → Q [] [] k k) : mHoareIO P Q :=
hoare.zero $ λ k h, ⟨[], [], rfl, (list.append_nil _).symm, H h⟩

theorem mHoareIO.mono_l {P P' : sProp} {Q : list byte → list byte → mProp}
  (H : P ≤ P') : mHoareIO P' Q → mHoareIO P Q :=
λ h, hoare.mono_l (λ k h, H _ h) h

theorem mHoareIO.mono_r {P : sProp} {Q Q' : list byte → list byte → mProp}
  (H : ∀ {{i o}}, Q i o ≤ Q' i o) : mHoareIO P Q → mHoareIO P Q' :=
λ h, hoare.mono_r (by exact λ k k' _ ⟨i', o', h₁, h₂, h₃⟩,
  ⟨i', o', h₁, h₂, H _ _ h₃⟩) h

theorem mHoareIO.step {P P' : sProp} {Q Q' : list byte → list byte → mProp}
  (H₁ : ∀ ⦃k i o⦄, P k → ∃ k', kcfg.step ⟨i, o, k⟩ k')
  (H₂ : ∀ {{k₁ k₂ i o i₁ o₁}}, P k₁ →
    kcfg.step ⟨i₁ ++ i, o, k₁⟩ ⟨i, o ++ o₁, k₂⟩ → P' k₂ ∧
      ∀ {{i₂ o₂ k₃}}, Q' i₂ o₂ k₂ k₃ → Q (i₁ ++ i₂) (o₁ ++ o₂) k₁ k₃)
  (H₃ : mHoareIO P' Q') : mHoareIO P Q :=
begin
  refine hoare.step (λ ⟨i', o', k⟩ h, H₁ h) _ H₃,
  rintro ⟨i₁, o₁, k₁⟩ h ⟨i₂, o₂, k₂⟩ h',
  rcases kcfg.step.io_part h' with ⟨⟨i, rfl⟩, ⟨o, rfl⟩⟩,
  rcases H₂ h h' with ⟨h₁, h₄⟩,
  refine ⟨h₁, _⟩,
  rintro k₃ ⟨i', o', e₁, e₂, h₅⟩,
  exact ⟨_, _,
    (congr_arg ((++) i) e₁).trans (list.append_assoc _ _ _).symm,
    e₂.trans (list.append_assoc _ _ _),
    h₄ h₅⟩
end

theorem mHoareIO.comp {P : sProp} {Q Q' : list byte → list byte → mProp}
  (H₁ : mHoareIO P Q)
  (H₂ : mHoareIO (sProp.ex $ λ i, sProp.ex $ λ o, (Q i o).apply P) Q') :
  mHoareIO P (λ i o,
    mProp.ex $ λ i₁, mProp.ex $ λ i₂,
    mProp.ex $ λ o₁, mProp.ex $ λ o₂,
    ((Q i₁ o₁).comp (Q' i₂ o₂)).with (i = i₁ ++ i₂ ∧ o = o₁ ++ o₂)) :=
λ k p, begin
  refine (H₁ p).bind _,
  rintro k₁ ⟨i₁, o₁, e₁, e₂, h₁⟩,
  refine (H₂ ⟨_, _, _, p, h₁⟩).mono _,
  rintro k₂ ⟨i₂, o₂, e₃, e₄, h₂⟩,
  refine ⟨_, _, _, _, _, _, _, _, ⟨_, h₁, h₂⟩, rfl, rfl⟩,
  rw [e₁, list.append_assoc, e₃],
  rw [e₄, ← list.append_assoc, e₂],
end

theorem mHoareIO.ex_l {α} {P : α → sProp} {Q} :
  mHoareIO (sProp.ex P) Q ↔ ∀ a, mHoareIO (P a) Q :=
⟨λ H a k h, H ⟨a, h⟩, λ H k ⟨a, h⟩, H a h⟩

theorem mHoare.zero {P : sProp} {Q : mProp}
  (H : ∀ {{k}}, P k → Q k k) : mHoare P Q :=
mHoareIO.zero $ λ k h, ⟨H h, rfl, rfl⟩

theorem mHoare.mono_l {P P' : sProp} {Q : mProp}
  (H : P ≤ P') : mHoare P' Q → mHoare P Q :=
mHoareIO.mono_l H

theorem mHoare.mono_r {P : sProp} {Q Q' : mProp}
  (H : Q ≤ Q') : mHoare P Q → mHoare P Q' :=
mHoareIO.mono_r $ λ k k' i o ⟨h₁, h₂, h₃⟩, ⟨H _ _ h₁, h₂, h₃⟩

theorem mHoare.step {P P' : sProp} {Q Q' : mProp}
  (H₁ : ∀ ⦃k⦄, P k → ∃ k', config.step k k')
  (H₂ : ∀ {{k₁ k₂}}, P k₁ → config.step k₁ k₂ →
    P' k₂ ∧ ∀ {{k₃}}, Q' k₂ k₃ → Q k₁ k₃) :
  mHoare P' Q' → mHoare P Q :=
mHoareIO.step
  (λ k i o h, let ⟨k', h'⟩ := H₁ h in ⟨⟨i, o, k'⟩, kcfg.step.noio h'⟩)
  (λ k₁ k₂ i o i₁ o₁ h h', begin
    generalize_hyp ei : i₁ ++ i = i' at h',
    generalize_hyp eo : o ++ o₁ = o' at h',
    cases h',
    { cases (@list.append_left_inj _ _ [] i).1 ei,
      cases (@list.append_right_inj _ _ [] o).1 (by simpa using eo),
      exact ⟨(H₂ h h'_a).1,
        λ i₂ o₂ k₃ h'', ⟨(H₂ h h'_a).2 h''.1, h''.2⟩⟩ },
    { cases H₁ h with k₂ h',
      cases config.step_noIO h' h'_a }
  end)

theorem mHoare.comp {P : sProp} {Q Q' : mProp}
  (H₁ : mHoare P Q)
  (H₂ : mHoare (Q.apply P) Q') :
  mHoare P (Q.comp Q') :=
(H₁.comp (H₂.mono_l
  (λ k₂ ⟨_, _, k₁, h₁, h₂, rfl, rfl⟩, ⟨_, h₁, h₂⟩))).mono_r $
by rintro _ _ k₁ k₃ ⟨i₁, o₁, i₂, o₂,
    ⟨k₂, ⟨h₁, rfl, rfl⟩, ⟨h₂, rfl, rfl⟩⟩, rfl, rfl⟩;
  exact ⟨⟨_, h₁, h₂⟩, rfl, rfl⟩

theorem mHoare.ex_l {α} {P : α → sProp} {Q} :
  mHoare (sProp.ex P) Q ↔ ∀ a, mHoare (P a) Q :=
⟨λ H a k h, H ⟨a, h⟩, λ H k ⟨a, h⟩, H a h⟩

theorem stmt.hoareIO.mono_s {A P Q s₁ s₂}
  (h : s₂ ≤ s₁) : stmt.hoareIO A P s₁ Q → stmt.hoareIO A P s₂ Q :=
λ H D rip l h', H _ _ _ (h _ _ _ _ h')

theorem stmt.hoareIO.mono_l {A P₁ P₂ s Q}
  (h : P₂ ≤ P₁) : stmt.hoareIO A P₁ s Q → stmt.hoareIO A P₂ s Q :=
λ H D rip l h', (H _ _ _ h').mono_l
  (λ k ⟨⟨h₁, h₂⟩, h₃⟩, ⟨⟨h _ h₁, h₂⟩, h₃⟩)

theorem stmt.hoareIO.mono_r {A P s}
  {Q₁ Q₂ : exit_kind → list byte → list byte → mProp}
  (h : ∀ {{e i o}}, Q₁ e i o ≤ Q₂ e i o) :
  stmt.hoareIO A P s Q₁ → stmt.hoareIO A P s Q₂ :=
λ H D rip l h', (H _ _ _ h').mono_r
  (λ i o k k', and.imp_right $
    Exists.imp $ λ e, and.imp_left $ λ h₁, h _ _ h₁)

theorem stmt.hoareIO.ex_l {α A s} {P : α → sProp} {Q} :
  stmt.hoareIO A (sProp.ex P) s Q ↔ ∀ a, stmt.hoareIO A (P a) s Q :=
⟨λ H a, H.mono_l $ λ k h, ⟨a, h⟩,
 λ H S rip k h k ⟨⟨⟨a, h₁⟩, h₂⟩, h₃⟩,
  H a _ _ _ h ⟨⟨h₁, h₂⟩, h₃⟩⟩

theorem stmt.hoare_iff {A P s Q} :
  stmt.hoare A P s Q ↔
  ∀ {{D rip l}}, s A D rip l →
    mHoare
      (P ⊓ sProp.sn place.rip rip ⊓
        sProp.mem_block (perm.R + perm.X) rip l)
      (mProp.ex (λ e, stable_at D ⊓
        (Q e).final (e.result A (rip + l.length)))) :=
forall_congr $ λ D, forall_congr $ λ rip, forall_congr $ λ l,
forall_congr $ λ h, iff_of_eq begin
  congr, funext i o k k', exact propext
    ⟨λ ⟨h₁, e, ⟨h₂, ei, eo⟩, h₃⟩, ⟨⟨e, h₁, h₂, h₃⟩, ei, eo⟩,
     λ ⟨⟨e, h₁, h₂, h₃⟩, ei, eo⟩, ⟨h₁, e, ⟨h₂, ei, eo⟩, h₃⟩⟩,
end

theorem stmt.hoare.mono_s {A P Q s₁ s₂}
  (h : s₂ ≤ s₁) : stmt.hoare A P s₁ Q → stmt.hoare A P s₂ Q :=
λ H D rip l h', H _ _ _ (h _ _ _ _ h')

theorem stmt.hoare.mono_l {A P₁ P₂ s Q}
  (h : P₂ ≤ P₁) : stmt.hoare A P₁ s Q → stmt.hoare A P₂ s Q :=
λ H D rip l h', (H _ _ _ h').mono_l
  (λ k ⟨⟨h₁, h₂⟩, h₃⟩, ⟨⟨h _ h₁, h₂⟩, h₃⟩)

theorem stmt.hoare.mono_r {A P s} {Q₁ Q₂ : exit_kind → mProp}
  (h : ∀ {{e}}, Q₁ e ≤ Q₂ e) :
  stmt.hoare A P s Q₁ → stmt.hoare A P s Q₂ :=
stmt.hoareIO.mono_r $ λ e i o k k' ⟨h₁, h₂⟩, ⟨h _ _ h₁, h₂⟩

theorem stmt.hoare.zero {A P} {s : stmt} {p : Prop}
  (H : ∀ {{D rip l}}, s A D rip l → p ∧ l = []) :
  s.hoare A P (λ e, (mlift p).with (e = exit_kind.straight)) :=
stmt.hoare_iff.2 $ λ D rip l h', begin
  rcases H h' with ⟨h, rfl⟩, apply mHoare.zero,
  rintro k ⟨⟨h₁, h₂⟩, h₃⟩,
  refine ⟨_, stable_at.refl, ⟨h, rfl⟩, _⟩,
  simpa using h₂
end

theorem stmt.hoare.ex_l {α A s} {P : α → sProp} {Q} :
  stmt.hoare A (sProp.ex P) s Q ↔ ∀ a, stmt.hoare A (P a) s Q :=
⟨λ H a, H.mono_l $ λ k h, ⟨a, h⟩,
 λ H S rip k h k ⟨⟨⟨a, h₁⟩, h₂⟩, h₃⟩,
  H a _ _ _ h ⟨⟨h₁, h₂⟩, h₃⟩⟩

theorem expr.hoare_iff {α A P E Q} :
  @expr.hoare α A P E Q ↔
  ∀ {{b}}, (E b).hoare A P $
    λ e, (Q b).with (e = exit_kind.straight) :=
forall_congr $ λ b, iff_of_eq begin
  congr, funext e i o k k', exact propext
    ⟨λ ⟨⟨h, ei, eo⟩, ee⟩, ⟨⟨h, ee⟩, ei, eo⟩,
     λ ⟨⟨h, ee⟩, ei, eo⟩,  ⟨⟨h, ei, eo⟩, ee⟩⟩
end

theorem expr.hoare.zero {α A P} {e : expr α} {p : block → Prop}
  (H : ∀ {{b D rip l}}, e b A D rip l → p b ∧ l = []) :
  e.hoare A P (λ b, mlift (p b)) :=
expr.hoare_iff.2 $ λ b, stmt.hoare.zero (@H b)

theorem expr.hoareIO.mono_e {α A P Q} {e₁ e₂ : expr α}
  (h : e₂ ≤ e₁) : expr.hoareIO A P e₁ Q → expr.hoareIO A P e₂ Q :=
λ H b, (H b).mono_s (@h b)

theorem expr.hoareIO.mono_l {α A P₁ P₂ s Q}
  (h : P₂ ≤ P₁) : @expr.hoareIO α A P₁ s Q → expr.hoareIO A P₂ s Q :=
λ H b, (H b).mono_l h

theorem expr.hoareIO.mono_r {α A P s}
  {Q₁ Q₂ : block → list byte → list byte → mProp}
  (h : ∀ {{b i o}}, Q₁ b i o ≤ Q₂ b i o) :
  @expr.hoareIO α A P s Q₁ → expr.hoareIO A P s Q₂ :=
λ H b, (H b).mono_r $ λ e i o, inf_le_inf (@h _ _ _) (le_refl _)

theorem expr.hoareIO.ex_l {α β A} {e : expr β} {P : α → sProp} {Q} :
  expr.hoareIO A (sProp.ex P) e Q ↔ ∀ a, expr.hoareIO A (P a) e Q :=
iff.trans (forall_congr $ λ b, stmt.hoareIO.ex_l) forall_swap

theorem expr.to_hoare {α A P} {e : expr α} {Q : block → mProp}
  (H : ∀ b, stmt.hoare A P (e b) (λ e, (Q b).with (e = exit_kind.straight))) :
  expr.hoare A P e Q :=
begin
  refine λ b, stmt.hoareIO.mono_r _ (H b),
  rintro e _ _ k k' ⟨⟨h, e'⟩, rfl, rfl⟩, exact ⟨⟨h, rfl, rfl⟩, e'⟩
end

theorem expr.hoare.ex_l {α β A} {e : expr β} {P : α → sProp} {Q} :
  expr.hoare A (sProp.ex P) e Q ↔ ∀ a, expr.hoare A (P a) e Q :=
expr.hoareIO.ex_l

theorem var.hoare {α} (i : name α) {A} (P : sProp) :
  (var i).hoare A P (λ b, mlift (b ∈ A.read i)) :=
expr.hoare.zero $ λ _ _ _ _, id

theorem ret.hoare {α b A} (P : sProp) :
  (ret α b).hoare A P (λ b', mlift (b' = b)) :=
expr.hoare.zero $ λ _ _ _ _, id

theorem hstmt.hoare {A} (P : sProp) (Q : mProp) :
  (hstmt P Q).hoare A P (λ e, Q.with (e = exit_kind.straight)) :=
stmt.hoare_iff.2 $ λ D rip l h',
(mHoare.mono_l
  (by exact λ _, and.imp_left and.right) h').mono_r $
by rintro k k' ⟨⟨h₁, h₂⟩, h₃⟩; exact ⟨_, h₂, ⟨h₁, rfl⟩, h₃⟩

theorem hexpr.hoare {α A} (P : sProp) (Q : block → mProp) :
  (@hexpr α P Q).hoare A P Q :=
expr.to_hoare $ λ b, hstmt.hoare _ _

def comp_exit (Q₁ Q₂ : exit_kind → mProp) (e : exit_kind) : mProp :=
mProp.ex $ λ e₁, exit_kind.cases_on e₁ ((Q₁ e₁).comp (Q₂ e)) $ λ _, (Q₁ e₁).with (e₁ = e)

/-
theorem stmt.seq.hoare {A s₁ s₂}
  {P₁ P₂ : sProp} {Q₁ Q₂ : exit_kind → mProp}
  (H₁ : stmt.hoare A P₁ s₁ Q₁)
  (H₂ : stmt.hoare A P₂ s₂ Q₂)
  (H : (Q₁ exit_kind.straight).apply P₁ ≤ P₂) :
  (stmt.seq s₁ s₂).hoare A P₁ (comp_exit Q₁ Q₂) :=
stmt.hoare_iff.2 begin
  rintro D rip l ⟨_, _, _, v₁, v₂, h₁, h₂⟩,
  change v₁.append v₂ with v₁ ++ v₂ at a ⊢,
  have := stmt.hoare_iff.1 H₁ h₁,
  refine (((stmt.hoare_iff.1 H₁ h₁).mono_l _).comp _).mono_r mProp.comp_ex_imp,
  { refine inf_le_inf (le_refl _) _,
    exact λ k, mem.read'_left ⟨_, rfl⟩ },
  rw [mProp.ex_apply, mHoare.ex_l], rintro (_|⟨n⟩),
  { refine ((stmt.hoare_iff.1 H₂ h₂).mono_l _).mono_r _,
    { rintro k₂ k₃ ⟨e₂, s₂, q₂, r₂⟩ e₁ k₁ ⟨s₁, q₁, r₁⟩,
      rw [list.length_append, ← bitvec.add_nat_assoc],
      refine ⟨e₂, s₁.trans s₂, ⟨exit_kind.straight, _, _, q₂⟩, r₂⟩,
      sorry },
    { } },
  { exact ⟨⟨exit_kind.label n, q₁, _⟩, r₂⟩ },

  have:= (((stmt.hoare_iff.1 H₁ h₁).mono_l _).comp
          ((stmt.hoare_iff.1 H₂ h₂).mono_l _)).mono_r _,
  { rintro k₁ k₃ ⟨k₂, ⟨s₁, e₁, q₁, r₁⟩, ⟨s₂, e₂, q₂, r₂⟩⟩,
    cases e₁,
    { refine ⟨s₁.trans s₂, e₂, ⟨exit_kind.straight, _, q₁, q₂⟩, _⟩,
      rwa [list.length_append, ← bitvec.add_nat_assoc] },
    { refine ⟨s₁.trans s₂, _, ⟨exit_kind.label e₁, _, rfl⟩, _⟩,

    } },
end
-/

----------------------------------------
-- Assembly
----------------------------------------

-- theorem var.asm {α} {i : name α} {A D rip bl}
--   (h : bl ∈ locals_ctx.get Γ i) : var i bl A D rip [] :=
-- ⟨h, rfl⟩

theorem ret.asm {α A D rip bl} : ret α bl bl A D rip [] :=
⟨rfl, rfl⟩

def stmt.asm (s : stmt) (D : set place) := Π A rip, ∃ v, s A D rip v


end x86