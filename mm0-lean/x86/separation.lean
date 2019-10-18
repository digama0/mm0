import x86.x86 data.set.lattice data.list.basic

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

def split (H h₁ h₂ : set place) : Prop :=
H = h₁ ∪ h₂ ∧ disjoint h₁ h₂

def sProp := config → set place → Prop

def sProp.sep (P Q : sProp) : sProp :=
λ k H, ∃ H₁ H₂, split H H₁ H₂ ∧ P k H₁ ∧ Q k H₂

instance : has_mul sProp := ⟨sProp.sep⟩

def sProp.wand (P Q : sProp) : sProp :=
λ k H₂, ∀ H₁ H, split H H₁ H₂ → P k H₁ → Q k H

def sProp.mk (H : config → set place) : sProp := λ k, eq (H k)

def sProp.reserve (S : set place) : sProp :=
sProp.mk $ λ k, {p | p ∈ S ∧ ∃ n v, @place.read k p n v}

def emp : sProp := sProp.mk $ λ _, ∅

def lift' (p : config → Prop) : sProp := λ k _, p k

def lift (p : Prop) : sProp := λ _ _, p

def sProp.and (P Q : sProp) : sProp := λ k H, P k H ∧ Q k H

def sProp.or (P Q : sProp) : sProp := λ k H, P k H ∨ Q k H

def sProp.with' (p : sProp) (q : config → Prop) : sProp := p.and (lift' q)
def sProp.with (p : sProp) (q : Prop) : sProp := p.and (lift q)
def liftE (p : Prop) : sProp := sProp.with emp p

def sProp.sn (p : place) {n} (v : bitvec n) : sProp :=
sProp.mk $ λ k, {p' | p = p' ∧ p.read k v}

def sProp.ex {α} (p : α → sProp) : sProp := λ k H, ∃ a, p a k H

def sProp.al {α} (p : α → sProp) : sProp := λ k H, ∀ a, p a k H

def sProp.flags (f : flags) : sProp :=
sProp.al $ λ p : flag_place,
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
(sProp.reserve (block.mem a v.length).places).with' $ λ k, k.mem.read' p a v

def sProp.block : block → list byte → sProp
| (block.reg r sz) v :=
  (sProp.reserve (block.reg r sz).places).with' $ λ k,
    read_full_imm sz (k.regs r) v
| (block.mem a sz) v :=
  (sProp.reserve (block.mem a sz).places).with' $ λ k,
    k.mem.read a v ∧ v.length = sz.to_nat
| (block.const l) v := liftE $ v = l

def sProp.block_writable : block → sProp
| (block.reg r sz) := sProp.reserve (block.reg r sz).places
| (block.mem a sz) :=
  (sProp.reserve (block.mem a sz).places).with' $ λ k,
    ∃ v, k.mem.read' perm.W a v ∧ v.length = sz.to_nat
| (block.const _) := lift false

def locals_ctx (n : ℕ) := {Γ : list (ℕ × block) //
  Γ.pairwise (λ i j, i.1 ≠ j.1 ∧ i.2.disj j.2) ∧
  ∀ i : ℕ × block, i ∈ Γ → i.1 < n}

instance {n} : has_mem (ℕ × block) (locals_ctx n) := ⟨λ a Γ, a ∈ Γ.1⟩

def locals_ctx.cons {n} (Γ : locals_ctx n) (b : block)
  (h : ∀ i : ℕ × block, i ∈ Γ → b.disj i.2) : locals_ctx (n+1) :=
⟨(n, b) :: Γ.1,
  list.pairwise_cons.2 ⟨λ i h', ⟨ne_of_gt $ Γ.2.2 _ h', h _ h'⟩, Γ.2.1⟩,
  by rintro i (rfl|h'); [
    apply nat.lt_succ_self,
    exact nat.lt_succ_of_lt (Γ.2.2 _ h')]⟩

def locals_ctx.shrink {m n} (Γ : locals_ctx m) : locals_ctx n :=
⟨Γ.1.filter (λ i, i.1 < n),
  list.pairwise_of_sublist (list.filter_sublist _) Γ.2.1,
  λ i h, (list.mem_filter.1 h).2⟩

def labels_ctx := qword × list qword

def labels_ctx.cons (q : qword) (L : labels_ctx) : labels_ctx :=
⟨L.1, q :: L.2⟩

inductive hoare_p (Q : kcfg → set place → Prop) : kcfg → set place → Prop
| zero {{k H}} : Q k H → hoare_p k H
| step {{k H}} : (∃ k', kcfg.step k k') →
  (∀ k', k.step k' → hoare_p k' H) → hoare_p k H
| exit (k : kcfg) (H ret) :
  k.k.exit ret → (ret = 0 → Q k H) → hoare_p k H

def hoare (P Q : kcfg → set place → Prop) :=
∀ {{k H}}, P k H → hoare_p Q k H

def sHoareIO (P : sProp) (Q : list byte → list byte → sProp) :=
∀ {{i o}}, hoare (λ k H, P k.k H ∧ k.input = i ∧ k.output = o)
  (λ k H, ∃ i' o', i = i' ++ k.input ∧ o = k.output ++ o' ∧
    (Q i' o') k.k H)

def noIO (Q : sProp) (i o : list byte) : sProp := Q.with (i = [] ∧ o = [])
def sHoare (P Q : sProp) := sHoareIO P (noIO Q)

inductive exit_kind
| straight
| label (n : ℕ)

def exit_kind.result (L : labels_ctx) (pos : qword) : exit_kind → sProp
| exit_kind.straight := sProp.sn place.rip pos
| (exit_kind.label n) := sProp.ex $ λ h, sProp.sn place.rip (L.2.nth_le n h)

def stmt (n) : Type :=
labels_ctx → locals_ctx n →
∀ rip : qword, list byte → Prop

def stmt.hoareIO (P : sProp) {n} (C : stmt n)
  (Q : exit_kind → list byte → list byte → sProp) : Prop :=
∀ L Γ rip l, C L Γ rip l →
  sHoareIO (P * sProp.sn place.rip rip *
      sProp.mem_block (perm.R + perm.X) rip l)
    (λ i o,
      ((sProp.sn place.rip L.1).or $
        sProp.ex $ λ e, Q e i o * e.result L (rip + l.length)) *
      sProp.mem_block (perm.R + perm.X) rip l)

def stmt.hoare (P : sProp) {n} (C : stmt n) (Q : exit_kind → sProp) : Prop :=
stmt.hoareIO P C (λ e, noIO (Q e))

def hstmt {n} (P : sProp) (Q : sProp) : stmt n :=
λ L Γ rip v,
  sHoare (P * sProp.sn place.rip rip * sProp.mem_block (perm.R + perm.X) rip v)
    (Q * sProp.sn place.rip (rip + v.length) * sProp.mem_block (perm.R + perm.X) rip v)

def stmt.all {α n} (s : α → stmt n) : stmt n :=
λ L Γ rip v, ∀ a, s a L Γ rip v

def stmt.ex {α n} (s : α → stmt n) : stmt n :=
λ L Γ rip v, ∃ a, s a L Γ rip v

def stmt.with {n} (p : Prop) (s : stmt n) : stmt n :=
stmt.ex $ λ h : p, s

def stmt.or {n} (s₁ s₂ : stmt n) : stmt n :=
λ L Γ rip v, s₁ L Γ rip v ∨ s₂ L Γ rip v

def stmt.lift {m n} (s : stmt n) : stmt m := λ L Γ, s L Γ.shrink

def expr (n) := block → stmt n

def expr.hoareIO (P : sProp) {n} (E : expr n)
  (Q : list byte → list byte → list byte → sProp) : Prop :=
∀ b, (E b).hoareIO (P * sProp.reserve b.places) $
  λ e i o, exit_kind.cases_on e
    (sProp.ex $ λ l, Q l i o * sProp.block b l)
    (λ n, lift false)

def expr.hoare (P : sProp) {n} (E : expr n) (Q : list byte → sProp) : Prop :=
expr.hoareIO P E (λ ret, noIO (Q ret))

def expr.lift {m n} (e : expr n) : expr m := λ b, stmt.lift (e b)

class value (α : Type*) :=
(size : ℕ)
(eval : α → list byte → Prop)
(eq_size : ∀ {v a}, eval a v → v.length = size)

class type (α : Type*) :=
(size : ℕ)
(eval : α → list byte → sProp)
(eq_size : ∀ {a v k H}, eval a v k H → v.length = size)

def type.evalB {α} [type α] (a : α) (b : block) : sProp :=
sProp.ex $ λ v, sProp.block b v * type.eval a v

instance (α) [value α] : type α :=
⟨value.size α, λ a v, lift $ value.eval a v, λ a v k H, value.eq_size⟩

def expr.hoareT (P : sProp) {n} (E : expr n) {α} [type α] (Q : α → sProp) : Prop :=
expr.hoare P E (λ v, sProp.ex $ λ a, Q a * type.eval a v)

theorem bits_to_byte_length {n m w v} : @bits_to_byte n m w v → v.length = m :=
by rintro ⟨bs⟩; exact bs.2

def bits.value {n} (m : ℕ) : value (bitvec n) :=
⟨m, bits_to_byte m, λ v a h, bits_to_byte_length h⟩

instance unit.value : value unit :=
⟨0, λ _ v, v = [], by rintro v _ ⟨⟩; refl⟩

instance byte.value : value byte :=
⟨1, λ b v, v = [b], by rintro v k ⟨⟩; refl⟩

instance word.value : value word := bits.value 4
instance qword.value : value qword := bits.value 8

class box (α) [type α] := (deref : α)

instance box.type (α) [type α] : type (box α) :=
⟨8, λ x v, sProp.ex $ λ a, (sProp.ex $ λ l,
    sProp.mem_block perm.R a l *
    type.eval x.deref l).with (value.eval a v),
  λ P v k H ⟨_, _, h⟩, bits_to_byte_length h⟩

def const {n} (l : list byte) : expr n :=
λ bl L Γ a v, bl = block.const l ∧ v = []

def var {n} (i : ℕ) : expr n :=
λ bl L Γ a v, (i, bl) ∈ Γ.1 ∧ v = []

def hexpr {n} (P : sProp) (Q : block → sProp) : expr n :=
λ ret, hstmt P (Q ret)

def expr.all {α n} (e : α → expr n) : expr n :=
λ ret, stmt.all $ λ a, e a ret

def expr.ex {α n} (e : α → expr n) : expr n :=
λ ret, stmt.ex $ λ a, e a ret

def expr.with {n} (p : Prop) (s : expr n) : expr n :=
expr.ex $ λ h : p, s

def const' {n} (sz : wsize) (i : ℕ) : expr n :=
expr.ex $ λ q, expr.ex $ λ l,
expr.with (read_full_imm sz q l ∧ q.to_nat = i) $
const l

inductive stmt.seq {n} (s₁ : stmt n) (s₂ : stmt n) : stmt n
| mk {L Γ rip v₁ v₂} :
  s₁ L Γ rip v₁ →
  s₂ L Γ (rip + v₁.length) v₂ →
  stmt.seq L Γ rip (v₁ ++ v₂)

inductive expr.bindS {n} (e₁ : expr n) (s₂ : block → stmt n) : stmt n
| mk {b L Γ rip v₁ v₂} :
  e₁ b L Γ rip v₁ →
  s₂ b L Γ (rip + v₁.length) v₂ →
  expr.bindS L Γ rip (v₁ ++ v₂)

def expr.bind {n} (e₁ : expr n) (e₂ : block → expr n) : expr n :=
λ b₂, expr.bindS e₁ $ λ b₁, e₂ b₁ b₂

def expr.bindST {n α} [type α] (e₁ : expr n) (s₂ : α → stmt n) : stmt n :=
expr.bindS e₁ $ λ b, stmt.all $ λ a : α,
λ L Γ rip v, sHoare (type.evalB a b)
  ((type.evalB a b).with (s₂ a L Γ rip v))

def expr.bindT {n α} [type α] (e₁ : expr n) (e₂ : α → expr n) : expr n :=
λ b₂, expr.bindST e₁ $ λ a, e₂ a b₂

def block.mov {n} (dst src : block) : stmt n :=
stmt.with (dst.size = src.size) $
stmt.all $ λ val, hstmt
  (sProp.block_writable dst * sProp.block src val)
  (sProp.block dst val * sProp.block src val)

def expr.set {n} (e₁ e₂ : expr n) : stmt n :=
expr.bindS e₁ $ λ dst, expr.bindS e₂ $ λ src, block.mov dst src

inductive label | fail | label (n : ℕ)

inductive label.loc (L : labels_ctx) : label → qword → Prop
| fail : label.loc label.fail L.1
| label (n h) : label.loc (label.label n) (L.2.nth_le n h)

def stmt.jump_cc {n} (p : flags → bool) (l : label) : stmt n :=
λ L Γ rip v, ∀ tgt, l.loc L tgt → ∀ f,
sHoare (sProp.flags f * sProp.sn place.rip rip * sProp.mem_block (perm.R + perm.X) rip v)
  (sProp.sn place.rip (cond (p f) tgt (rip + v.length)) * sProp.mem_block (perm.R + perm.X) rip v)

def stmt.jump {n} : label → stmt n := stmt.jump_cc (λ _, tt)

def boolexpr (n) := (flags → bool) × stmt n

def boolexpr.hoare (P : sProp) {n} (E : boolexpr n) (Q : bool → sProp) : Prop :=
stmt.hoare (P * sProp.reserve (set.range place.flag))
  E.2
  (λ e, exit_kind.cases_on e
    (sProp.ex $ λ f, Q (E.1 f) * sProp.flags f)
    (λ n, lift false))

def boolexpr.not {n} (c : boolexpr n) : boolexpr n :=
⟨λ f, bnot $ c.1 f, c.2⟩

def boolexpr.jump_if {n} (c : boolexpr n) (l : label) : stmt n :=
stmt.seq c.2 $ stmt.jump_cc c.1 l

def stmt.nop {n} : stmt n := λ L Γ rip v, v = []

def if_stmt {n} (c : boolexpr n) (s₁ s₂ : stmt n) : stmt n :=
stmt.seq c.not.2 $ λ L Γ rip v,
∃ v₁ v₂ v₃, v = v₁ ++ v₂ ++ v₃ ∧
let q₁ := rip + v₁.length, q₂ := q₁ + v₂.length in
stmt.jump_cc c.not.1 (label.label 0) (L.cons q₁) Γ rip v₁ ∧
s₁.seq (stmt.jump (label.label 0)) (L.cons q₂) Γ q₁ v₂ ∧
s₂.seq (stmt.jump (label.label 0)) (L.cons q₂) Γ q₂ v₃

def loop {n} (s : stmt n) : stmt n :=
λ L Γ rip, s (L.cons rip) Γ rip

def block_stmt {n} (s : stmt n) : stmt n :=
λ L Γ rip v, s (L.cons (rip + v.length)) Γ rip v

def while {n} (c : boolexpr n) (s : stmt n) : stmt n :=
block_stmt $ loop $
  (c.not.jump_if (label.label 1)).seq $
  s.seq $
  stmt.jump (label.label 0)

def decl_block {n} (b : block) (s : stmt (n + 1)) : stmt n :=
λ L Γ rip v, ∀ h, s L (Γ.cons b h) rip v

def decl {n} (sz : qword) (s : stmt (n + 1)) : stmt n :=
λ L Γ rip v, ∀ b h, block.size b = sz → s L (Γ.cons b h) rip v

def init_rvo {n} (sz : qword) (e : expr n) (s : stmt (n + 1)) : stmt n :=
e.bindS $ λ b, stmt.with (b.size = sz) $
λ L Γ rip v, ∃ h, s L (Γ.cons b h) rip v

def init_assign {n} (sz : qword) (e : expr n) (s : stmt (n + 1)) : stmt n :=
e.bindS $ λ b, stmt.with (b.size = sz) $
decl sz $ ((var n).set e.lift).seq s

def init {n} (sz : qword) (e : expr n) (s : stmt (n + 1)) : stmt n :=
(init_rvo sz e s).or (init_assign sz e s)

def for {n} (sz : qword) (start : expr n)
  (test : boolexpr (n+1)) (incr body : stmt (n+1)) : stmt n :=
init sz start $ while test $ body.seq incr

def binop_expr {n α β γ} [type α] [type β]
  (f : α → β → γ) (mk : γ → list byte → Prop)
  (e₁ e₂ : expr n) : expr n :=
e₁.bindT $ λ a : α, e₂.bindT $ λ b : β, 
sorry

def incr {n} (i) : stmt n :=
(var i).set $ binop_expr (+) qword.to_list_byte (var i) (const [1])

def bool_binop {n α β} [type α] [type β]
  (f : α → β → bool) (e₁ e₂ : expr n) : boolexpr n :=
⟨sorry, e₁.bindST $ λ a : α, e₂.bindST $ λ b : β,
  sorry⟩

def lt {n} (e₁ e₂ : expr n) : boolexpr n :=
bool_binop (λ a b : qword, a.to_nat < b.to_nat) e₁ e₂

def for_seq {n} (sz : qword) (max : expr n) (body : stmt (n+1)) : stmt n :=
for sz (const' wsize.Sz64 0) (lt (const' wsize.Sz64 0) max.lift) (incr n) body

----------------------------------------
-- Determinism
----------------------------------------

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

end x86