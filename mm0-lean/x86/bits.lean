-- import data.bitvec
import data.vector order.basic

@[reducible] def bitvec (n : ℕ) := vector bool n

namespace bitvec
open vector nat

-- Create a zero bitvector
@[reducible] protected def zero (n : ℕ) : bitvec n := repeat ff n

-- Create a bitvector with the constant one.
@[reducible] protected def one : Π (n : ℕ), bitvec n
| 0        := nil
| (succ n) := tt :: repeat ff n

-- bitvec specific version of vector.append
def append {m n} : bitvec m → bitvec n → bitvec (m + n) := vector.append

def singleton (b : bool) : bitvec 1 := vector.cons b vector.nil

protected def cong {a b : ℕ} (h : a = b) : bitvec a → bitvec b
| ⟨x, p⟩ := ⟨x, h ▸ p⟩

section bitwise
  variable {n : ℕ}

  def not : bitvec n → bitvec n := map bnot
  def and : bitvec n → bitvec n → bitvec n := map₂ band
  def or  : bitvec n → bitvec n → bitvec n := map₂ bor
  def xor : bitvec n → bitvec n → bitvec n := map₂ bxor

  def from_bits_fill (fill : bool) : list bool → ∀ {n}, bitvec n
  | [] n := repeat fill n
  | (a :: l) 0 := vector.nil
  | (a :: l) (n+1) := vector.cons a (from_bits_fill l)

  def fill_shr (x : bitvec n) (i : ℕ) (fill : bool) : bitvec n :=
  from_bits_fill fill (list.repeat ff i ++ x.1)

  -- unsigned shift right
  def ushr (x : bitvec n) (i : ℕ) : bitvec n :=
  fill_shr x i ff

end bitwise

protected def of_nat : Π (n : ℕ), nat → bitvec n
| 0        x := nil
| (succ n) x := let ⟨b, y⟩ := bodd_div2 x in b :: of_nat n y

def bits_to_nat (v : list bool) : nat := v.foldr nat.bit 0

def to_nat {n} (v : bitvec n) : ℕ := bits_to_nat v.1

def sign : ∀ {n} (v : bitvec n), bool
| 0     _ := ff
| (n+1) v := v.nth ⟨n, lt_succ_self _⟩

def to_int {n} (v : bitvec n) : ℤ :=
cond (sign v) (to_nat v - (2^n : ℕ) : ℤ) (to_nat v)

section arith
  variable {n : ℕ}

  protected def neg {n} (v : bitvec n) : bitvec n :=
  bitvec.of_nat _ (2^n - to_nat v)

  protected def add (x y : bitvec n) : bitvec n :=
  bitvec.of_nat _ (to_nat x + to_nat y)

  protected def sub (x y : bitvec n) : bitvec n := x.add y.neg

  instance : has_zero (bitvec n) := ⟨bitvec.zero n⟩
  instance : has_one (bitvec n)  := ⟨bitvec.one n⟩
  instance : has_add (bitvec n)  := ⟨bitvec.add⟩
  instance : has_sub (bitvec n)  := ⟨bitvec.sub⟩
  instance : has_neg (bitvec n)  := ⟨bitvec.neg⟩

  protected def mul (x y : bitvec n) : bitvec n :=
  bitvec.of_nat _ (to_nat x * to_nat y)

  instance : has_mul (bitvec n)  := ⟨bitvec.mul⟩

  def shl (x : bitvec n) (i : ℕ) : bitvec n :=
  bitvec.of_nat _ (nat.shiftl (to_nat x) i)
  -- bitvec.cong (by simp) $ (repeat ff (min n i)).append (drop i x)
end arith

end bitvec

@[reducible] def byte := bitvec 8

def byte.to_nat : byte → ℕ := bitvec.to_nat

@[reducible] def short := bitvec 16

@[reducible] def word := bitvec 32

@[reducible] def qword := bitvec 64

def of_bits : list bool → nat
| [] := 0
| (b :: l) := nat.bit b (of_bits l)

inductive split_bits : ℕ → list (Σ n, bitvec n) → Prop
| nil : split_bits 0 []
| zero {b l} : split_bits b l → split_bits b (⟨0, vector.nil⟩ :: l)
| succ {b n l bs} :
  split_bits (nat.div2 b) (⟨n, bs⟩ :: l) →
  split_bits b (⟨n + 1, vector.cons (nat.bodd b) bs⟩ :: l)

def from_list_byte : list byte → ℕ
| [] := 0
| (b :: l) := b.to_nat + 0x100 * from_list_byte l

def bits_to_byte {n} (m) (w : bitvec n) (l : list byte) : Prop :=
l.length = m ∧ split_bits w.to_nat (l.map (λ b, ⟨8, b⟩))

def short.to_list_byte : short → list byte → Prop := bits_to_byte 2

def word.to_list_byte : word → list byte → Prop := bits_to_byte 4

def qword.to_list_byte : qword → list byte → Prop := bits_to_byte 8

def EXTS_aux : list bool → bool → ∀ {m}, bitvec m
| []     b m     := vector.repeat b _
| (a::l) _ 0     := vector.nil
| (a::l) _ (m+1) := vector.cons a (EXTS_aux l a)

def EXTS {m n} (v : bitvec n) : bitvec m := EXTS_aux v.1 ff

def EXTZ_aux : list bool → ∀ {m}, bitvec m
| []     m     := vector.repeat ff _
| (a::l) 0     := vector.nil
| (a::l) (m+1) := vector.cons a (EXTZ_aux l)

def EXTZ {m n} (v : bitvec n) : bitvec m := EXTZ_aux v.1

def bitvec.update0_aux : list bool → ∀ {n}, bitvec n → bitvec n
| []     n     v := v
| (a::l) 0     v := v
| (a::l) (n+1) v := vector.cons a (bitvec.update0_aux l v.tail)

def bitvec.update_aux : ℕ → list bool → ∀ {n}, bitvec n → bitvec n
| 0     l n     v := bitvec.update0_aux l v
| (m+1) l 0     v := v
| (m+1) l (n+1) v := vector.cons v.head (bitvec.update_aux m l v.tail)

def bitvec.update {m n} (v1 : bitvec n) (index : ℕ) (v2 : bitvec m) : bitvec n :=
bitvec.update_aux index v2.1 v1

class byte_encoder (α : Type*) := (f : α → list byte → Prop)

def encodes {α : Type*} [E : byte_encoder α] : α → list byte → Prop := E.f

def encodes_with {α : Type*} [byte_encoder α]
  (a : α) (l1 l2 : list byte) : Prop :=
∃ l, encodes a l ∧ l2 = l ++ l1

def encodes_start {α : Type*} [byte_encoder α]
  (a : α) (l : list byte) : Prop :=
∃ l', encodes_with a l' l

inductive encodes_list {α} [byte_encoder α] : list α → list byte → Prop
| nil : encodes_list [] []
| cons {a as l ls} : encodes a l → encodes_list (a :: as) (l ++ ls)

inductive encodes_list_start {α} [byte_encoder α] : list α → list byte → Prop
| nil {l} : encodes_list_start [] l
| cons {a as l ls} : encodes a l → encodes_list_start (a :: as) (l ++ ls)

instance : byte_encoder unit := ⟨λ _ l, l = []⟩
instance : byte_encoder byte := ⟨λ b l, l = [b]⟩
instance : byte_encoder short := ⟨short.to_list_byte⟩
instance : byte_encoder word := ⟨word.to_list_byte⟩
instance : byte_encoder qword := ⟨qword.to_list_byte⟩
instance : byte_encoder (list byte) := ⟨eq⟩
instance {n} : byte_encoder (vector byte n) := ⟨λ x l, x.1 = l⟩

instance {α β} [byte_encoder α] [byte_encoder β] : byte_encoder (α × β) :=
⟨λ ⟨a, b⟩ l, ∃ l1 l2, encodes a l1 ∧ encodes a l2 ∧ l = l1 ++ l2⟩

def string.to_cstr (s : string) : list byte :=
s.to_list.map (λ c, bitvec.of_nat _ c.1) ++ [0]

structure pstate_result (σ α : Type*) :=
(safe : Prop)
(P : α → σ → Prop)
(good : safe → ∃ a s, P a s)

def pstate (σ α : Type*) := σ → pstate_result σ α

instance (σ) : has_coe_to_fun (pstate_result σ unit) := ⟨_, λ r, r.P ()⟩

inductive pstate_pure_P {σ α : Type*} (a : α) (s : σ) : α → σ → Prop
| mk : pstate_pure_P a s

inductive pstate_map_P {σ α β} (f : α → β) (x : pstate_result σ α) : β → σ → Prop
| mk (a s') : x.P a s' → pstate_map_P (f a) s'

def pstate_bind_safe {σ α β} (x : pstate σ α) (f : α → pstate σ β) (s : σ) : Prop :=
(x s).safe ∧ ∀ a s', (x s).P a s' → (f a s').safe

def pstate_bind_P {σ α β} (x : pstate σ α) (f : α → pstate σ β) (s : σ) (b : β) (s' : σ) : Prop :=
∃ a s1, (x s).P a s1 ∧ (f a s1).P b s'

instance {σ} : monad (pstate σ) :=
{ pure := λ α a s, ⟨true, pstate_pure_P a s, λ _, ⟨_, _, ⟨a, s⟩⟩⟩,
  map := λ α β f x s, ⟨(x s).1, pstate_map_P f (x s), λ h,
    let ⟨a, s', h⟩ := (x s).good h in ⟨_, _, ⟨_, _, _, h⟩⟩⟩,
  bind := λ α β x f s, ⟨pstate_bind_safe x f s, pstate_bind_P x f s,
    λ ⟨h₁, h₂⟩, let ⟨a, s1, hx⟩ := (x s).good h₁,
      ⟨b, s2, hf⟩ := (f a s1).good (h₂ a s1 hx) in
      ⟨b, s2, ⟨_, _, hx, hf⟩⟩⟩ }

def pstate.lift {σ α} (f : σ → α → σ → Prop) : pstate σ α := λ s, ⟨_, f s, id⟩

inductive pstate.get' {σ} (s : σ) : σ → σ → Prop
| mk : pstate.get' s s
def pstate.get {σ} : pstate σ σ := pstate.lift pstate.get'

def pstate.put {σ} (s : σ) : pstate σ unit := pstate.lift $ λ _ _, eq s

def pstate.assert {σ α} (p : σ → α → Prop) : pstate σ α :=
pstate.lift $ λ s a s', p s a ∧ s = s'

def pstate.modify {σ} (f : σ → σ) : pstate σ unit :=
pstate.lift $ λ s _ s', s' = f s

def pstate.any {σ α} : pstate σ α := pstate.assert $ λ _ _, true

def pstate.fail {σ α} : pstate σ α := pstate.assert $ λ _ _, false

def pstate_result.le {σ α} (s1 s2 : pstate_result σ α) : Prop :=
s2.safe → s1.safe ∧ ∀ a s, s1.P a s → s2.P a s

instance {σ α} : has_le (pstate_result σ α) := ⟨pstate_result.le⟩
instance {σ α} : preorder (pstate_result σ α) :=
{ le := pstate_result.le,
  le_refl := λ a h, ⟨h, λ _ _, id⟩,
  le_trans := λ a b c h1 h2 h,
    let ⟨h21, h22⟩ := h2 h, ⟨h11, h12⟩ := h1 h21 in
    ⟨h11, λ _ _ s, h22 _ _ (h12 _ _ s)⟩ }

instance {σ α} : preorder (pstate σ α) := pi.preorder

theorem pstate.bind_le {σ α β} {m m' : pstate σ α} {f f' : α → pstate σ β}
  (h1 : m ≤ m') (h2 : ∀ a, f a ≤ f' a) :
  m >>= f ≤ m' >>= f' :=
λ _ ⟨h3, h4⟩, begin
  cases h1 _ h3 with h5 h6,
  refine ⟨⟨h5, λ a s' h, (h2 a s' $ h4 _ _ $ h6 _ _ h).1⟩, _⟩,
  rintro a s' ⟨a', s'', h, h8⟩,
  exact ⟨_, _, h6 _ _ h, (h2 _ _ $ h4 _ _ $ h6 _ _ h).2 _ _ h8⟩
end

theorem pstate.map_le {σ α β} {m m' : pstate σ α} {f f' : α → pstate σ β}
  (h1 : m ≤ m') : f <$> m ≤ f <$> m' :=
λ _ h, ⟨(h1 _ h).1, by rintro b s ⟨a', _, h4⟩; exact
  ⟨_, _, _, (h1 _ h).2 _ _ h4⟩⟩

theorem pstate.lift_le {σ α} {f f' : σ → α → σ → Prop}
  (H : ∀ s, (∃ a s', f' s a s') →
    (∃ a s', f s a s') ∧ ∀ a s', f s a s' → f' s a s') :
  pstate.lift f ≤ pstate.lift f' :=
λ _, H _

theorem pstate.assert_le {σ α} {f f' : σ → α → Prop}
  (H : ∀ s, (∃ a, f' s a) →
    (∃ a, f s a) ∧ ∀ a, f s a → f' s a) : pstate.assert f ≤ pstate.assert f' :=
begin
  apply pstate.lift_le,
  rintro s ⟨a, _, h, e⟩,
  rcases H s ⟨_, h⟩ with ⟨⟨a', h'⟩, h2'⟩,
  exact ⟨⟨_, _, h', e⟩, λ a' s' ⟨h1, h2⟩, ⟨h2' _ h1, h2⟩⟩,
end

theorem pstate.assert_le_any {σ α} {f : σ → α → Prop}
  (H : ∀ s, ∃ a, f s a) : pstate.assert f ≤ pstate.any :=
begin
  rintro s ⟨a, _, _, rfl⟩,
  cases H s,
  refine ⟨⟨_, _, h, rfl⟩, λ a s' ⟨_, e⟩, ⟨⟨⟩, e⟩⟩,
end

theorem pstate.not_safe_top {σ α} {S' S : pstate σ α}
  (H : ∀ a, ¬ (S a).safe) : S' ≤ S :=
λ s h, (H _ h).elim
