import x86.x86 data.list.basic data.zmod.basic

namespace bitvec

theorem of_nat_zero (n) : bitvec.of_nat n 0 = 0 :=
by induction n; [refl, exact congr_arg (vector.cons ff) n_ih]

theorem of_nat_one (n) : bitvec.of_nat n 1 = 1 :=
by cases n; [refl, exact congr_arg (vector.cons tt) (of_nat_zero _)]

theorem from_bits_fill_eq : ∀ {n b l} (e : list.length l = n),
  from_bits_fill b l = ⟨l, e⟩
| 0     b []       e := rfl
| (n+1) b (a :: l) e :=
  by rw [from_bits_fill, from_bits_fill_eq (nat.succ_inj e)]; refl

theorem bits_to_nat_zero (n) : bits_to_nat (list.repeat ff n) = 0 :=
by simp [bits_to_nat]; induction n; simp *

@[simp] theorem bits_to_nat_cons (a l) :
  bits_to_nat (a :: l) = nat.bit a (bits_to_nat l) := rfl

@[simp] theorem to_nat_nil : to_nat vector.nil = 0 := rfl

@[simp] theorem to_nat_zero (n) : to_nat (0 : bitvec n) = 0 :=
bits_to_nat_zero _

@[simp] theorem to_nat_cons (b) {n} (v : bitvec n) :
  to_nat (b :: v) = nat.bit b (to_nat v) :=
by cases v; refl

@[simp] theorem of_nat_succ (n i : ℕ) :
  bitvec.of_nat n.succ i = i.bodd :: bitvec.of_nat n i.div2 :=
by rw [bitvec.of_nat, nat.bodd_div2_eq, bitvec.of_nat]

@[simp] theorem of_nat_bit (n : ℕ) (b i) :
  bitvec.of_nat n.succ (nat.bit b i) = b :: bitvec.of_nat n i :=
by rw [of_nat_succ, nat.div2_bit, nat.bodd_bit]

theorem of_nat_bits_to_nat {n} (l : list bool) :
  bitvec.of_nat n (bits_to_nat l) = from_bits_fill ff l :=
begin
  rw bits_to_nat,
  induction l generalizing n, exact of_nat_zero _,
  cases n, refl,
  simp [*, bits_to_nat, from_bits_fill,
    bitvec.of_nat, nat.bodd_bit, nat.div2_bit]
end

theorem of_nat_bits_to_nat_eq {n} (l : list bool) (e : l.length = n) :
  bitvec.of_nat n (bits_to_nat l) = ⟨l, e⟩ :=
begin
  induction n generalizing l; cases l; injection e, refl,
  simp [bits_to_nat, nat.div2_bit, nat.bodd_bit],
  exact congr_arg (vector.cons l_hd) (n_ih _ h_1)
end

@[simp] theorem of_nat_to_nat : ∀ {n} (v : bitvec n),
  bitvec.of_nat n (to_nat v) = v
| n ⟨l, e⟩ := of_nat_bits_to_nat_eq l e

theorem to_nat_of_nat_aux (m n b) :
  nat.bit b (n % 2 ^ m) = nat.bit b n % 2 ^ nat.succ m :=
begin
  have := nat.mod_add_div (n.bit b) (2^m * 2),
  conv at this { to_rhs, rw [nat.bit_val, ← nat.mod_add_div n (2^m),
    mul_add, add_right_comm, ← nat.bit_val, mul_left_comm,
    ← mul_assoc] },
  rw [nat.pow_succ],
  refine add_right_cancel (this.symm.trans _), congr' 2,
  rw [mul_comm, ← nat.div_div_eq_div_mul, ← nat.div2_val, nat.div2_bit]
end

theorem to_nat_of_nat (m n) : to_nat (bitvec.of_nat m n) = n % 2 ^ m :=
begin
  induction m generalizing n,
  { simp [bitvec.of_nat, to_nat], refl },
  simp [bitvec.of_nat, m_ih],
  conv { to_rhs, rw ← nat.bit_decomp n },
  apply to_nat_of_nat_aux
end

theorem to_nat_lt_pow2 {n} (v : bitvec n) : to_nat v < 2 ^ n :=
begin
  rw [← of_nat_to_nat v, to_nat_of_nat],
  exact nat.mod_lt _ (nat.pow_pos dec_trivial _),
end

def pow2 (n : ℕ) : ℕ+ := ⟨2^n, nat.pow_pos dec_trivial _⟩

def to_zmod {n} (v : bitvec n) : zmod (pow2 n) := bitvec.to_nat v
def of_zmod {n} (i : zmod (pow2 n)) : bitvec n := bitvec.of_nat _ i.1

theorem to_zmod_of_zmod {n} (i : zmod (pow2 n)) : to_zmod (of_zmod i) = i :=
((zmod.eq_iff_modeq_nat' _).2
  (by convert nat.modeq.mod_modeq _ _; apply to_nat_of_nat)).trans (zmod.cast_val _)

theorem of_zmod_to_zmod {n} (v : bitvec n) : of_zmod (to_zmod v) = v :=
by unfold of_zmod to_zmod; convert of_nat_to_nat v; exact
zmod.val_cast_of_lt (to_nat_lt_pow2 _)

theorem of_nat_eq_iff_modeq {m n₁ n₂} :
  bitvec.of_nat m n₁ = bitvec.of_nat m n₂ ↔ n₁ ≡ n₂ [MOD 2 ^ m] :=
begin
  dunfold nat.modeq, split; intro h,
  { rw [← to_nat_of_nat, h, to_nat_of_nat] },
  { rw [← of_nat_to_nat (bitvec.of_nat m n₁),
      to_nat_of_nat, h, ← to_nat_of_nat, of_nat_to_nat] },
end

theorem of_nat_eq_of_zmod (m n) :
  bitvec.of_nat m n = bitvec.of_zmod n :=
eq.symm $ of_nat_eq_iff_modeq.2 $
by convert nat.modeq.mod_modeq _ _; apply zmod.val_cast_nat

theorem to_zmod_zero (n) : to_zmod (0 : bitvec n) = 0 :=
by rw [to_zmod, to_nat_zero]; refl

theorem of_zmod_zero (n) : (of_zmod 0 : bitvec n) = 0 :=
by rw [← to_zmod_zero, of_zmod_to_zmod]

theorem of_zmod_one (n) : (of_zmod 1 : bitvec n) = 1 :=
begin
  cases n, {refl},
  change bitvec.of_nat _ (1 % 2 ^ _) = _,
  rw [nat.mod_eq_of_lt, of_nat_one],
  exact @nat.pow_lt_pow_of_lt_right _ dec_trivial 0 _ (nat.succ_pos _)
end

theorem to_zmod_one (n) : to_zmod (1 : bitvec n) = 1 :=
by rw [← of_zmod_one, to_zmod_of_zmod]

theorem to_zmod_add {n} (a b : bitvec n) : to_zmod (a + b) = to_zmod a + to_zmod b :=
show to_zmod (bitvec.of_nat _ _) = _,
by rw [of_nat_eq_of_zmod, to_zmod_of_zmod, to_zmod, to_zmod, nat.cast_add]

theorem to_zmod_mul {n} (a b : bitvec n) : to_zmod (a * b) = to_zmod a * to_zmod b :=
show to_zmod (bitvec.of_nat _ _) = _,
by rw [of_nat_eq_of_zmod, to_zmod_of_zmod, to_zmod, to_zmod, nat.cast_mul]

theorem to_zmod_neg {n} (a : bitvec n) : to_zmod (-a) = -to_zmod a :=
show to_zmod (bitvec.of_nat _ _) = _,
begin
  rw [of_nat_eq_of_zmod, to_zmod_of_zmod, eq_neg_iff_add_eq_zero, to_zmod,
    ← nat.cast_add, nat.sub_add_cancel (le_of_lt (to_nat_lt_pow2 _))],
  exact zmod.cast_self_eq_zero,
end

theorem of_zmod_add {n} (a b : zmod (pow2 n)) : of_zmod (a + b) = of_zmod a + of_zmod b :=
by conv_lhs {rw [← to_zmod_of_zmod a, ← to_zmod_of_zmod b]};
   rw [← to_zmod_add, of_zmod_to_zmod]

theorem of_zmod_mul {n} (a b : zmod (pow2 n)) : of_zmod (a * b) = of_zmod a * of_zmod b :=
by conv_lhs {rw [← to_zmod_of_zmod a, ← to_zmod_of_zmod b]};
   rw [← to_zmod_mul, of_zmod_to_zmod]

theorem of_zmod_neg {n} (a : zmod (pow2 n)) : of_zmod (-a) = -of_zmod a :=
by conv_lhs {rw [← to_zmod_of_zmod a]}; rw [← to_zmod_neg, of_zmod_to_zmod]

instance (n : ℕ) : add_comm_semigroup (bitvec n) :=
{ add_assoc := λ a b c, by rw [← of_zmod_to_zmod a, ← of_zmod_to_zmod b, ← of_zmod_to_zmod c,
    ← of_zmod_add, ← of_zmod_add, add_assoc, of_zmod_add, of_zmod_add],
  add_comm := λ a b, by rw [← of_zmod_to_zmod a, ← of_zmod_to_zmod b,
    ← of_zmod_add, add_comm, of_zmod_add],
  ..bitvec.has_add }

instance (n : ℕ) : comm_semigroup (bitvec n) :=
{ mul_assoc := λ a b c, by rw [← of_zmod_to_zmod a, ← of_zmod_to_zmod b, ← of_zmod_to_zmod c,
    ← of_zmod_mul, ← of_zmod_mul, mul_assoc, of_zmod_mul, of_zmod_mul],
  mul_comm := λ a b, by rw [← of_zmod_to_zmod a, ← of_zmod_to_zmod b,
    ← of_zmod_mul, mul_comm, of_zmod_mul],
  ..bitvec.has_mul }

instance (n : ℕ) : comm_ring (bitvec n) :=
{ zero_add := λ a, by rw [← of_zmod_to_zmod a, ← of_zmod_zero, ← of_zmod_add, zero_add],
  add_zero := λ a, by rw [← of_zmod_to_zmod a, ← of_zmod_zero, ← of_zmod_add, add_zero],
  add_left_neg := λ a, by rw [← of_zmod_to_zmod a,
    ← of_zmod_neg, ← of_zmod_add, add_left_neg, ← of_zmod_zero],
  one_mul := λ a, by rw [← of_zmod_to_zmod a, ← of_zmod_one, ← of_zmod_mul, one_mul],
  mul_one := λ a, by rw [← of_zmod_to_zmod a, ← of_zmod_one, ← of_zmod_mul, mul_one],
  left_distrib := λ a b c, by rw [← of_zmod_to_zmod a, ← of_zmod_to_zmod b, ← of_zmod_to_zmod c,
    ← of_zmod_add, ← of_zmod_mul, left_distrib, of_zmod_add, of_zmod_mul, of_zmod_mul]; refl,
  right_distrib := λ a b c, by rw [← of_zmod_to_zmod a, ← of_zmod_to_zmod b, ← of_zmod_to_zmod c,
    ← of_zmod_add, ← of_zmod_mul, right_distrib, of_zmod_add, of_zmod_mul, of_zmod_mul]; refl,
  ..bitvec.has_zero,
  ..bitvec.has_one,
  ..bitvec.has_neg,
  ..bitvec.add_comm_semigroup n,
  ..bitvec.comm_semigroup n }

theorem to_nat_nth {n} (i j) :
  (bitvec.of_nat n i).nth j = i.test_bit j.1 :=
begin
  generalize e : bitvec.of_nat n i = v, cases v with l e',
  cases j with j h,
  rw [vector.nth], dsimp only,
  induction n generalizing i l j, cases h,
  cases l; injection e',
  simp [bitvec.of_nat] at e,
  generalize_hyp e₂ : bitvec.of_nat n_n i.div2 = v at e, cases v with l e₂',
  injection e, cases h_2,
  cases j; simp, refl,
  rw [← nat.bit_decomp i, nat.test_bit_succ],
  exact n_ih _ _ _ _ e₂ (nat.lt_of_succ_lt_succ h)
end

theorem of_nat_from_bits_fill (n m i) (h : n ≤ m) :
  bitvec.of_nat n i = from_bits_fill ff (bitvec.of_nat m i).1 :=
begin
  generalize e : bitvec.of_nat m i = v, cases v with l h, simp,
  induction n generalizing m i l e, exact (vector.eq_nil _).trans (vector.eq_nil _).symm,
  rw [of_nat_succ],
  cases m, cases h,
  rw [of_nat_succ] at e,
  generalize e' : bitvec.of_nat m i.div2 = v, cases v with l' h',
  rw e' at e, injection e, subst l,
  rw [n_ih _ _ (nat.le_of_succ_le_succ h) _ _ e', from_bits_fill],
end

theorem of_nat_bit0_aux {n} (j : bitvec (nat.succ n)) :
  bit0 j = ff :: from_bits_fill ff (j.val) :=
begin
  change bitvec.of_nat n.succ (bit0 (to_nat j)) = _,
  rw [of_nat_succ,
    nat.bodd_bit0, nat.div2_bit0, to_nat, of_nat_bits_to_nat]
end

theorem of_nat_bit0 (n i) : bitvec.of_nat n (bit0 i) = bit0 (bitvec.of_nat n i) :=
begin
  induction n generalizing i, refl,
  rw [of_nat_succ,
    nat.bodd_bit0, nat.div2_bit0],
  rw [of_nat_from_bits_fill _ _ _ (nat.le_succ _)],
  generalize : bitvec.of_nat n_n.succ i = j,
  rw of_nat_bit0_aux,
end

theorem of_nat_bit1 (n i) : bitvec.of_nat n (bit1 i) = bit1 (bitvec.of_nat n i) :=
begin
  induction n generalizing i, refl,
  rw [of_nat_succ,
    nat.bodd_bit1, nat.div2_bit1],
  rw [of_nat_from_bits_fill _ _ _ (nat.le_succ _)],
  generalize : bitvec.of_nat n_n.succ i = j,
  change _ = bitvec.of_nat _ (to_nat (bit0 j) + bit0 (@to_nat n_n 0) + 1),
  rw [to_nat_zero],
  change _ = bitvec.of_nat _ (to_nat (bit0 j) + 1),
  rw [of_nat_bit0_aux, to_nat_cons],
  change _ = bitvec.of_nat _ (nat.bit tt _),
  rw [of_nat_bit, of_nat_to_nat],
end

theorem add_nat_assoc {n} (v : bitvec n) (a b : ℕ) :
  v + a + b = v + (a + b : ℕ) :=
by rw [nat.cast_add, add_assoc]

theorem of_nat_add {n} (a b : ℕ) : bitvec.of_nat n (a + b) = bitvec.of_nat n a + bitvec.of_nat n b :=
by simp [of_nat_eq_of_zmod, of_zmod_add]

theorem of_nat_succ' {n} (a : ℕ) : bitvec.of_nat n a.succ = bitvec.of_nat n a + 1 :=
(of_nat_add a 1).trans $ by simp [of_nat_one]

theorem of_nat_mul {n} (a b : ℕ) : bitvec.of_nat n (a * b) = bitvec.of_nat n a * bitvec.of_nat n b :=
by simp [of_nat_eq_of_zmod, of_zmod_mul]

theorem coe_eq_of_nat {n} (a : ℕ) :
  (a : bitvec n) = bitvec.of_nat n a :=
begin
  induction a, exact (bitvec.of_nat_zero _).symm,
  rw [of_nat_succ', ← a_ih], refl,
end

theorem coe_to_nat {n} (v : bitvec n) : (to_nat v : bitvec n) = v :=
by rw [coe_eq_of_nat, of_nat_to_nat]

theorem bits_to_nat_inj : ∀ {l₁ l₂},
  bits_to_nat l₁ = bits_to_nat l₂ → l₁.length = l₂.length → l₁ = l₂
| [] [] _ _ := rfl
| (a :: l₁) (b :: l₂) e e' := begin
  rw [bits_to_nat_cons, bits_to_nat_cons] at e,
  rw [← nat.bodd_bit a (bits_to_nat l₁), e, nat.bodd_bit,
    @bits_to_nat_inj l₁ l₂ _ (nat.succ_inj e')],
  rw [← nat.div2_bit a (bits_to_nat l₁), e, nat.div2_bit]
end

theorem to_nat_inj {n v₁ v₂}
  (h : @bitvec.to_nat n v₁ = bitvec.to_nat v₂) : v₁ = v₂ :=
subtype.eq $ bits_to_nat_inj h (v₁.2.trans v₂.2.symm)

theorem coe_shl {n} (a b) : (nat.shiftl a b : bitvec n) = bitvec.shl a b :=
begin
  rw [shl, coe_eq_of_nat, nat.shiftl_eq_mul_pow, nat.shiftl_eq_mul_pow],
  refine of_nat_eq_iff_modeq.2 (nat.modeq.modeq_mul_right _ _),
  rw [← of_nat_eq_iff_modeq, of_nat_to_nat, coe_eq_of_nat],
end

theorem sign_iff_neg {n v} : @bitvec.sign n v ↔ bitvec.to_int v < 0 :=
begin
  unfold bitvec.to_int, cases sign v; simp,
  apply sub_lt_zero.2, norm_cast,
  exact to_nat_lt_pow2 _
end

theorem to_int_inj {n v₁ v₂}
  (h : @bitvec.to_int n v₁ = bitvec.to_int v₂) : v₁ = v₂ :=
begin
  have : sign v₁ = sign v₂,
  { apply bool.coe_bool_iff.1,
    rw [sign_iff_neg, sign_iff_neg, h] },
  revert h,
  unfold bitvec.to_int,
  rw this, cases sign v₂; simp; exact to_nat_inj
end

theorem pow2_eq_zero {n} : (2 ^ n : bitvec n) = 0 :=
begin
  suffices : ((2 ^ n : ℕ) : bitvec n) = 0, {exact_mod_cast this},
  have := to_nat_of_nat n (2^n),
  apply to_nat_inj,
  rw [coe_eq_of_nat, to_nat_of_nat, nat.mod_self, to_nat_zero],
end

theorem coe_to_int {n} (v : bitvec n) : (to_int v : bitvec n) = v :=
by unfold to_int; cases sign v; simp [coe_to_nat, pow2_eq_zero]

@[class] def reify {n} (v : bitvec n) (l : out_param (list bool)) : Prop :=
from_bits_fill ff l = v

theorem reify.mk {n} (v) {l} [h : @reify n v l] :
  from_bits_fill ff l = v := h

theorem reify_eq {n v l l'} [@reify n v l] (h : l' = v.1) :
  l' = (@from_bits_fill ff l n).1 := by rwa reify.mk v
theorem reify_eq' {n v l l'} [@reify n v l] (h : l' = v) :
  l' = @from_bits_fill ff l n := by rwa reify.mk v

theorem reify_eq₂ {n v₁ l₁ v₂ l₂}
  [@reify n v₁ l₁] [@reify n v₂ l₂] (h : v₁ = v₂) :
  @from_bits_fill ff l₁ n = from_bits_fill ff l₂ :=
by rwa [reify.mk v₁, reify.mk v₂]

theorem reify_iff {n v l} : @reify n v l ↔ bitvec.of_nat n (bits_to_nat l) = v :=
iff_of_eq $ congr_arg (= v) (of_nat_bits_to_nat _).symm

instance reify_0 {n} : @reify n 0 [] := rfl

instance reify_1 {n} : @reify n 1 [tt] :=
by cases n; exact rfl

instance reify_bit0 {n} (v l) [h : @reify n v l] :
  reify (bit0 v) (ff :: l) :=
reify_iff.2 $
by have := of_nat_bit0 n (bits_to_nat l);
   rwa [reify_iff.1 h] at this

instance reify_bit1 {n} (v l) [h : @reify n v l] :
  reify (bit1 v) (tt :: l) :=
reify_iff.2 $
by have := of_nat_bit1 n (bits_to_nat l);
   rwa [reify_iff.1 h] at this

end bitvec

namespace x86

def split_bits_spec : list (Σ n, bitvec n) → list bool → Prop
| [] l := list.all l bnot
| (⟨n, v⟩ :: s) l := let ⟨l₁, l₂⟩ := l.split_at n in
  (@bitvec.from_bits_fill ff l₁ n).1 = v.1 ∧ split_bits_spec s l₂

theorem split_bits_ok {l s} : split_bits (bitvec.bits_to_nat l) s → split_bits_spec s l :=
begin
  generalize e₁ : bitvec.bits_to_nat l = n,
  induction s generalizing l n, rintro ⟨⟩,
  { induction l, constructor,
    cases l_hd,
    { exact bool.band_intro rfl (l_ih (not_imp_not.1 (nat.bit_ne_zero _) e₁)) },
    { cases nat.bit1_ne_zero _ e₁ } },
  { rcases s_hd with ⟨i, l', e₂⟩,
    unfold split_bits_spec,
    generalize e₃ : l.split_at i = p, cases p with l₁ l₂,
    dsimp [split_bits_spec],
    induction i with i generalizing l' l₁ l₂ e₂ l n; cases l'; injection e₂,
    { cases h_2, cases e₃, exact ⟨rfl, s_ih _ e₁ h_2_a⟩ },
    { generalize_hyp e₄ : (⟨l'_hd :: l'_tl, e₂⟩ : bitvec _) = f at h_2,
      cases h_2, cases h_2_bs with _ pr, injection e₄, cases h_3,
      generalize e₅ : l.tail.split_at i = p, cases p with l₁' l₂',
      have : bitvec.bits_to_nat l.tail = nat.div2 n,
      { subst e₁, cases l, refl, exact (nat.div2_bit _ _).symm },
      rcases i_ih _ _ _ h_1 _ this e₅ h_2_a with ⟨e₆, h'⟩,
      replace e₆ : bitvec.from_bits_fill ff l₁' = ⟨l'_tl, pr⟩ := subtype.eq e₆,
      cases l,
      { cases e₃,
        have : (l₁', l₂') = ([], []), {cases i; cases e₅; refl}, cases this,
        simp [bitvec.from_bits_fill, h', vector.repeat] at e₆ ⊢,
        cases e₁, exact ⟨rfl, e₆⟩ },
      { rw [list.split_at, show l_tl.split_at i = (l₁', l₂'), from e₅] at e₃,
        cases e₃, rw [bitvec.from_bits_fill, ← e₁, e₆],
        refine ⟨_, h'⟩, simp [vector.cons], exact (nat.bodd_bit _ _).symm } } }
end

theorem split_bits.determ_l {n₁ n₂ l} (h₁ : split_bits n₁ l) (h₂ : split_bits n₂ l) : n₁ = n₂ :=
begin
  induction l generalizing n₁ n₂, {cases h₁, cases h₂, refl},
  rcases l_hd with ⟨_, l', rfl⟩,
  induction l' generalizing n₁ n₂,
  { cases h₁, cases h₂, exact l_ih h₁_a h₂_a },
  { have : ∀ {n l'},
      split_bits n l' →
      l' = ⟨_, l'_hd :: l'_tl, rfl⟩ :: l_tl →
      l'_hd = nat.bodd n ∧
      split_bits (nat.div2 n) (⟨_, l'_tl, rfl⟩ :: l_tl),
    { intros, cases a; try {cases a_1},
      rcases a_bs with ⟨l₂, rfl⟩,
      injection a_1, cases h_2,
      cases congr_arg (λ v : Σ n, bitvec n, v.2.1) h_1,
      exact ⟨rfl, a_a⟩ },
    rcases this h₁ rfl with ⟨rfl, h₁'⟩,
    rcases this h₂ rfl with ⟨e, h₂'⟩,
    rw [← nat.bit_decomp n₁, e, l'_ih h₁' h₂', nat.bit_decomp] }
end

theorem split_bits.determ {n l₁ l₂} (h₁ : split_bits n l₁) (h₂ : split_bits n l₂)
  (h : l₁.map sigma.fst = l₂.map sigma.fst) : l₁ = l₂ :=
begin
  induction l₁ generalizing n l₂; cases l₂; injection h, refl,
  cases l₁_hd with i v₁, cases l₂_hd with _ v₂, cases h_1,
  clear h h_1, induction i with i generalizing v₁ v₂ n,
  { cases h₁, cases h₂, rw l₁_ih h₁_a h₂_a h_2 },
  { cases h₁, cases h₂, cases i_ih _ _ h₁_a h₂_a, refl }
end

theorem bits_to_byte.determ_l {n m w1 w2 l} :
  @bits_to_byte n m w1 l → @bits_to_byte n m w2 l → w1 = w2
| ⟨e₁, h₁⟩ ⟨_, h₂⟩ := bitvec.to_nat_inj $ split_bits.determ_l h₁ h₂

theorem bits_to_byte.determ_l_aux {n m w1 w2 l l'} :
  @bits_to_byte n m w1 l → @bits_to_byte n m w2 (l ++ l') → (w1, l') = (w2, [])
| ⟨e₁, h₁⟩ ⟨e₂, h₂⟩ := begin
  simp, suffices, refine ⟨_, this⟩, swap,
  { apply list.length_eq_zero.1,
    apply @eq_of_add_eq_add_left _ _ l.length,
    rw [add_zero, ← list.length_append, e₁, e₂] },
  clear bits_to_byte.determ_l_aux, subst this,
  rw list.append_nil at h₂,
  exact bitvec.to_nat_inj (split_bits.determ_l h₁ h₂)
end

theorem bits_to_byte.determ {n m w l1 l2} :
  @bits_to_byte n m w l1 → @bits_to_byte n m w l2 → l1 = l2
| ⟨e₁, h₁⟩ ⟨e₂, h₂⟩ := list.injective_map_iff.2
  (by rintro x y ⟨⟩; refl)
  (split_bits.determ h₁ h₂
    (by rw [list.map_map, list.map_map, (_ : _∘_ = _),
      list.map_const _ 8, e₁, list.map_const, e₂]; refl))

theorem read_prefixes.determ {r₁ r₂ l} : read_prefixes r₁ l → read_prefixes r₂ l → r₁ = r₂ :=
begin
  intros h₁ h₂, cases h₁; cases h₂; congr,
  cases split_bits.determ h₁_a h₂_a rfl, refl,
end

@[elab_as_eliminator] theorem byte_split {C : byte → Sort*}
   : ∀ b : byte, (∀ b0 b1 b2 b3 b4 b5 b6 b7,
    C ⟨[b0, b1, b2, b3, b4, b5, b6, b7], rfl⟩) → C b
| ⟨[b0, b1, b2, b3, b4, b5, b6, b7], rfl⟩ H := H _ _ _ _ _ _ _ _

def binop.from_bits : ∀ (b0 b1 b2 b3 : bool), binop
| ff ff ff ff := binop.add
| tt ff ff ff := binop.or
| ff tt ff ff := binop.adc
| tt tt ff ff := binop.sbb
| ff ff tt ff := binop.and
| tt ff tt ff := binop.sub
| ff tt tt ff := binop.xor
| tt tt tt ff := binop.cmp
| ff ff ff tt := binop.rol
| tt ff ff tt := binop.ror
| ff tt ff tt := binop.rcl
| tt tt ff tt := binop.rcr
| ff ff tt tt := binop.shl
| tt ff tt tt := binop.shr
| ff tt tt tt := binop.tst
| tt tt tt tt := binop.sar

theorem binop.bits_eq {b0 b1 b2 b3 e op} :
  binop.bits op ⟨[b0, b1, b2, b3], e⟩ → op = binop.from_bits b0 b1 b2 b3 :=
begin
  generalize e' : (⟨[b0, b1, b2, b3], e⟩ : bitvec 4) = v,
  intro h, induction h;
  { cases bitvec.reify_eq (congr_arg subtype.val e'), refl }
end

theorem binop.bits.determ : ∀ {op1 op2 v},
  binop.bits op1 v → binop.bits op2 v → op1 = op2
| op1 op2 ⟨[b0, b1, b2, b3], _⟩ h1 h2 :=
  (binop.bits_eq h1).trans (binop.bits_eq h2).symm

def basic_cond.from_bits : ∀ (b0 b1 b2 : bool), option basic_cond
| ff ff ff := some basic_cond.o
| tt ff ff := some basic_cond.b
| ff tt ff := some basic_cond.e
| tt tt ff := some basic_cond.na
| ff ff tt := some basic_cond.s
| tt ff tt := none
| ff tt tt := some basic_cond.l
| tt tt tt := some basic_cond.ng

theorem basic_cond.bits_eq {b0 b1 b2 e c} :
  basic_cond.bits c ⟨[b0, b1, b2], e⟩ → basic_cond.from_bits b0 b1 b2 = some c :=
begin
  generalize e' : (⟨[b0, b1, b2], e⟩ : bitvec 3) = v,
  intro h, induction h;
  { cases bitvec.reify_eq (congr_arg subtype.val e'), refl }
end

def cond_code.from_bits (b0 b1 b2 b3 : bool) : option cond_code :=
option.map (cond_code.mk b3) (basic_cond.from_bits b0 b1 b2)

theorem cond_code.bits_eq {b0 b1 b2 b3 e c} :
  cond_code.bits c ⟨[b0, b1, b2, b3], e⟩ → cond_code.from_bits b0 b1 b2 b3 = some c :=
begin
  rintro ⟨⟩,
  rcases split_bits_ok a_a with ⟨h₁, ⟨⟩, _⟩,
  cases subtype.eq h₁,
  rw [cond_code.from_bits, basic_cond.bits_eq a_a_1], refl
end

theorem cond_code.bits.determ : ∀ {c1 c2 v},
  cond_code.bits c1 v → cond_code.bits c2 v → c1 = c2
| c1 c2 ⟨[b0, b1, b2, b3], _⟩ h1 h2 := option.some_inj.1 $
  (cond_code.bits_eq h1).symm.trans (cond_code.bits_eq h2)

theorem read_displacement_ne_3 {mod disp l} :
  read_displacement mod disp l → mod ≠ 3 :=
by rintro ⟨⟩ ⟨⟩

theorem read_displacement.determ_aux {mod disp1 disp2 l l'}
  (h₁ : read_displacement mod disp1 l)
  (h₂ : read_displacement mod disp2 (l ++ l')) : (disp1, l') = (disp2, []) :=
begin
  cases h₁; cases h₂; try {refl},
  cases bits_to_byte.determ_l_aux h₁_a h₂_a, refl
end

theorem read_displacement.determ {mod disp1 disp2 l}
  (h₁ : read_displacement mod disp1 l)
  (h₂ : read_displacement mod disp2 l) : disp1 = disp2 :=
by cases read_displacement.determ_aux h₁
  (by rw list.append_nil; exact h₂); refl

theorem read_sib_displacement_ne_3 {mod bbase w Base l} :
  read_sib_displacement mod bbase w Base l → mod ≠ 3 :=
by rw [read_sib_displacement]; split_ifs; [
  {rcases h with ⟨_, rfl⟩; rintro _ ⟨⟩},
  exact λ h, read_displacement_ne_3 h.1]

theorem read_sib_displacement.determ_aux {mod bbase w1 w2 Base1 Base2 l l'}
  (h₁ : read_sib_displacement mod bbase w1 Base1 l)
  (h₂ : read_sib_displacement mod bbase w2 Base2 (l ++ l')) : (w1, Base1, l') = (w2, Base2, []) :=
begin
  rw read_sib_displacement at h₁ h₂, split_ifs at h₁ h₂,
  { rcases h₁ with ⟨b, rfl, rfl, rfl⟩,
    rcases h₂ with ⟨_, rfl, rfl, ⟨⟩⟩, refl },
  { rcases h₁ with ⟨h1, rfl⟩,
    rcases h₂ with ⟨h2, rfl⟩,
    cases read_displacement.determ_aux h1 h2, refl },
end

theorem read_sib_displacement.determ {mod bbase w1 w2 Base1 Base2 l}
  (h₁ : read_sib_displacement mod bbase w1 Base1 l)
  (h₂ : read_sib_displacement mod bbase w2 Base2 l) : (w1, Base1) = (w2, Base2) :=
by cases read_sib_displacement.determ_aux h₁
  (by rw list.append_nil; exact h₂); refl

theorem read_SIB_ne_3 {rex mod rm l} :
  read_SIB rex mod rm l → mod ≠ 3 :=
by rintro ⟨⟩; exact read_sib_displacement_ne_3 a_a_1

theorem read_SIB.determ_aux {rex mod rm1 rm2 l l'}
  (h₁ : read_SIB rex mod rm1 l)
  (h₂ : read_SIB rex mod rm2 (l ++ l')) : (rm1, l') = (rm2, []) :=
begin
  cases h₁, cases h₂,
  cases split_bits.determ h₁_a h₂_a rfl,
  cases read_sib_displacement.determ_aux h₁_a_1 h₂_a_1, refl
end

theorem read_SIB.determ {rex mod rm1 rm2 l}
  (h₁ : read_SIB rex mod rm1 l)
  (h₂ : read_SIB rex mod rm2 l) : rm1 = rm2 :=
by cases read_SIB.determ_aux h₁
  (by rw list.append_nil; exact h₂); refl

theorem read_ModRM_nil {rex reg r} : ¬ read_ModRM rex reg r [] :=
by rintro ⟨⟩

def read_ModRM' (rex : REX) (r : RM)
  (rm : bitvec 3) (mod : bitvec 2) (l : list byte) : Prop :=
if mod = 3 then
  r = RM.reg (rex_reg rex.B rm) ∧
  l = []
else if rm = 4 then
  read_SIB rex mod r l
else if rm = 5 ∧ mod = 0 then ∃ i : word,
  i.to_list_byte l ∧
  r = RM.mem none base.rip (EXTS i)
else ∃ disp,
  read_displacement mod disp l ∧
  r = RM.mem none (base.reg (rex_reg rex.B rm)) disp

theorem read_ModRM_ModRM' {rex : REX} {reg : regnum} {r : RM}
  {rm reg_opc : bitvec 3} {mod : bitvec 2} {b : byte} {l : list byte}
  (h₁ : split_bits b.to_nat [⟨3, rm⟩, ⟨3, reg_opc⟩, ⟨2, mod⟩])
  (h₂ : read_ModRM rex reg r (b :: l)) :
  reg = rex_reg rex.R reg_opc ∧ read_ModRM' rex r rm mod l :=
begin
  generalize_hyp e : list.cons b l = l' at h₂,
  induction h₂; cases e;
    cases split_bits.determ h₁ h₂_a rfl;
    refine ⟨rfl, _⟩,
  { rw [read_ModRM', if_neg, if_neg, if_pos],
    exact ⟨_, h₂_a_1, rfl⟩,
    all_goals {exact dec_trivial} },
  { rw [read_ModRM', if_pos],
    exact ⟨rfl, rfl⟩, exact dec_trivial },
  { rw [read_ModRM', if_neg (read_SIB_ne_3 h₂_a_1), if_pos],
    exact h₂_a_1, refl },
  { rw [read_ModRM', if_neg (read_displacement_ne_3 h₂_a_3),
      if_neg h₂_a_1, if_neg h₂_a_2],
    exact ⟨_, h₂_a_3, rfl⟩ },
end

theorem read_ModRM_split {rex reg r b l}
  (h : read_ModRM rex reg r (b :: l)) :
  ∃ rm reg_opc mod,
  split_bits b.to_nat [⟨3, rm⟩, ⟨3, reg_opc⟩, ⟨2, mod⟩] :=
by cases h; exact ⟨_, _, _, by assumption⟩

theorem read_ModRM.determ_aux {rex reg1 r1 reg2 r2 l l'}
  (h₁ : read_ModRM rex reg1 r1 l)
  (h₂ : read_ModRM rex reg2 r2 (l ++ l')) :
  (reg1, r1, l') = (reg2, r2, []) :=
begin
  simp,
  cases l with b l, {cases read_ModRM_nil h₁},
  rcases read_ModRM_split h₁ with ⟨rm, reg_opc, r, s⟩,
  rcases read_ModRM_ModRM' s h₁ with ⟨rfl, h₁'⟩,
  rcases read_ModRM_ModRM' s h₂ with ⟨rfl, h₂'⟩,
  refine ⟨rfl, _⟩,
  clear h₁ h₂ s, unfold read_ModRM' at h₁' h₂',
  split_ifs at h₁' h₂',
  { rw h₁'.2 at h₂', exact ⟨h₁'.1.trans h₂'.1.symm, h₂'.2⟩ },
  { cases read_SIB.determ_aux h₁' h₂', exact ⟨rfl, rfl⟩ },
  { rcases h₁' with ⟨i1, h11, h12⟩,
    rcases h₂' with ⟨i2, h21, h22⟩,
    cases bits_to_byte.determ_l_aux h11 h21,
    exact ⟨h12.trans h22.symm, rfl⟩ },
  { rcases h₁' with ⟨i1, h11, h12⟩,
    rcases h₂' with ⟨i2, h21, h22⟩,
    cases read_displacement.determ_aux h11 h21,
    exact ⟨h12.trans h22.symm, rfl⟩ },
end

theorem read_ModRM.determ {rex reg1 r1 reg2 r2 l}
  (h₁ : read_ModRM rex reg1 r1 l)
  (h₂ : read_ModRM rex reg2 r2 l) : (reg1, r1) = (reg2, r2) :=
by cases read_ModRM.determ_aux h₁
  (by rw list.append_nil; exact h₂); refl

theorem read_ModRM.determ₂ {rex reg1 r1 reg2 r2 l1 l2 l1' l2'}
  (h₁ : read_ModRM rex reg1 r1 l1)
  (h₂ : read_ModRM rex reg2 r2 l2)
  (e : l1 ++ l1' = l2 ++ l2') : (reg1, r1, l1, l1') = (reg2, r2, l2, l2') :=
begin
  have : ∀ {reg1 r1 reg2 r2 l1 l2 l1' l2'}
    (h₁ : read_ModRM rex reg1 r1 l1)
    (h₂ : read_ModRM rex reg2 r2 l2)
    (e : ∃ a', l2 = l1 ++ a' ∧ l1' = a' ++ l2'),
    (l1, l1') = (l2, l2'),
  { intros, rcases e_1 with ⟨l3, rfl, rfl⟩,
    cases read_ModRM.determ_aux h₁_1 h₂_1, simp },
  cases (list.append_eq_append_iff.1 e).elim
    (λ h, this h₁ h₂ h)
    (λ h, (this h₂ h₁ h).symm),
  cases read_ModRM.determ h₁ h₂, refl,
end

theorem read_opcode_ModRM.determ_aux {rex v1 r1 v2 r2 l l'}
  (h₁ : read_opcode_ModRM rex v1 r1 l)
  (h₂ : read_opcode_ModRM rex v2 r2 (l ++ l')) : (v1, r1, l') = (v2, r2, []) :=
begin
  cases h₁, cases h₂,
  cases read_ModRM.determ_aux h₁_a h₂_a,
  cases split_bits.determ h₁_a_1 h₂_a_1 rfl, refl,
end

theorem read_opcode_ModRM.determ {rex v1 r1 v2 r2 l}
  (h₁ : read_opcode_ModRM rex v1 r1 l)
  (h₂ : read_opcode_ModRM rex v2 r2 l) : (v1, r1) = (v2, r2) :=
by cases read_opcode_ModRM.determ_aux h₁
  (by rw list.append_nil; exact h₂); refl

theorem read_opcode_ModRM.determ₂_aux {rex v1 r1 v2 r2 l1 l2 l1' l2' l'}
  (h₁ : read_opcode_ModRM rex v1 r1 l1)
  (h₂ : read_opcode_ModRM rex v2 r2 l2)
  (e : l1 ++ l1' ++ l' = l2 ++ l2') : (v1, r1, l1, l1' ++ l') = (v2, r2, l2, l2') :=
begin
  cases h₁, cases h₂,
  rw [list.append_assoc, list.append_eq_append_iff] at e,
  rcases e with ⟨x, rfl, e⟩ | ⟨x, rfl, rfl⟩,
  { cases read_ModRM.determ_aux h₁_a h₂_a, cases e,
    cases split_bits.determ h₁_a_1 h₂_a_1 rfl,
    rw list.append_nil, refl },
  { cases read_ModRM.determ_aux h₂_a h₁_a,
    cases split_bits.determ h₁_a_1 h₂_a_1 rfl,
    rw list.append_nil, refl },
end

theorem read_opcode_ModRM.determ₂ {rex v1 r1 v2 r2 l1 l2 l1' l2'}
  (h₁ : read_opcode_ModRM rex v1 r1 l1)
  (h₂ : read_opcode_ModRM rex v2 r2 l2) :
  l1 ++ l1' = l2 ++ l2' → (v1, r1, l1, l1') = (v2, r2, l2, l2') :=
by simpa using @read_opcode_ModRM.determ₂_aux _ _ _ _ _ _ _ l1' l2' [] h₁ h₂

theorem read_imm8.determ_aux {w1 w2 l l'}
  (h₁ : read_imm8 w1 l) (h₂ : read_imm8 w2 (l ++ l')) : (w1, l') = (w2, []) :=
by cases h₁; cases h₂; refl

theorem read_imm16.determ_aux {w1 w2 l l'}
  (h₁ : read_imm16 w1 l) (h₂ : read_imm16 w2 (l ++ l')) : (w1, l') = (w2, []) :=
by cases h₁; cases h₂; cases bits_to_byte.determ_l_aux h₁_a h₂_a; refl

theorem read_imm32.determ_aux {w1 w2 l l'}
  (h₁ : read_imm32 w1 l) (h₂ : read_imm32 w2 (l ++ l')) : (w1, l') = (w2, []) :=
by cases h₁; cases h₂; cases bits_to_byte.determ_l_aux h₁_a h₂_a; refl

theorem read_imm8.determ {w1 w2 l}
  (h₁ : read_imm8 w1 l) (h₂ : read_imm8 w2 l) : w1 = w2 :=
by cases h₁; cases h₂; refl

theorem read_imm16.determ {w1 w2 l}
  (h₁ : read_imm16 w1 l) (h₂ : read_imm16 w2 l) : w1 = w2 :=
by cases h₁; cases h₂; cases bits_to_byte.determ_l h₁_a h₂_a; refl

theorem read_imm32.determ {w1 w2 l}
  (h₁ : read_imm32 w1 l) (h₂ : read_imm32 w2 l) : w1 = w2 :=
by cases h₁; cases h₂; cases bits_to_byte.determ_l h₁_a h₂_a; refl

theorem read_imm.determ_aux : ∀ {sz w1 w2 l l'},
  read_imm sz w1 l → read_imm sz w2 (l ++ l') → (w1, l') = (w2, [])
| (wsize.Sz8 _) _ _ _ _ := read_imm8.determ_aux
| wsize.Sz16 _ _ _ _ := read_imm16.determ_aux
| wsize.Sz32 _ _ _ _ := read_imm32.determ_aux
| wsize.Sz64 _ _ _ _ := false.elim

theorem read_full_imm.determ_aux : ∀ {sz w1 w2 l l'},
  read_full_imm sz w1 l → read_full_imm sz w2 (l ++ l') → (w1, l') = (w2, [])
| (wsize.Sz8 _) _ _ _ _ := read_imm8.determ_aux
| wsize.Sz16 _ _ _ _ := read_imm16.determ_aux
| wsize.Sz32 _ _ _ _ := read_imm32.determ_aux
| wsize.Sz64 _ _ _ _ := bits_to_byte.determ_l_aux

theorem read_imm.determ {sz w1 w2 l}
  (h₁ : read_imm sz w1 l) (h₂ : read_imm sz w2 l) : w1 = w2 :=
by cases read_imm.determ_aux h₁
  (by rw list.append_nil; exact h₂); refl

theorem read_full_imm.determ {sz w1 w2 l}
  (h₁ : read_full_imm sz w1 l) (h₂ : read_full_imm sz w2 l) : w1 = w2 :=
by cases read_full_imm.determ_aux h₁
  (by rw list.append_nil; exact h₂); refl

def decode_two' (rex : REX) (a : ast) (b0 b1 b2 b3 b4 b5 b6 b7 : bool) (l : list byte) : Prop :=
cond b7
  (cond b6
    ( -- xadd
      [b1, b2, b3, b4, b5] = [ff, ff, ff, ff, ff] ∧
      let v := b0, sz := op_size_W rex v in
      ∃ reg r,
      read_ModRM rex reg r l ∧
      a = ast.xadd sz r reg)
    (cond b5
      (cond b2
        ( -- movsx
          [b1, b4] = [tt, tt] ∧
          let sz2 := op_size_W rex tt,
              sz := if b0 then wsize.Sz16 else wsize.Sz8 rex.is_some in
          ∃ reg r,
          read_ModRM rex reg r l ∧
          a = (if b3 then ast.movsx else ast.movzx) sz (dest_src.R_rm reg r) sz2)
        ( -- cmpxchg
          [b1, b4] = [ff, tt] ∧
          let v := b0, sz := op_size_W rex v in
          ∃ reg r,
          read_ModRM rex reg r l ∧
          a = ast.cmpxchg sz r reg))
      (cond b4
        ( -- setcc
          ∃ reg r code,
          read_ModRM rex reg r l ∧
          cond_code.from_bits b0 b1 b2 b3 = some code ∧
          a = ast.setcc code rex.is_some r)
        ( -- jcc
          ∃ imm code,
          read_imm32 imm l ∧
          cond_code.from_bits b0 b1 b2 b3 = some code ∧
          a = ast.jcc code imm))))
  (cond b6
    ( -- cmov
      [b4, b5] = [ff, ff] ∧
      let sz := op_size tt rex.W tt in
      ∃ reg r code,
      read_ModRM rex reg r l ∧
      cond_code.from_bits b0 b1 b2 b3 = some code ∧
      a = ast.cmov code sz (dest_src.R_rm reg r))
    ( -- syscall
      [b0, b1, b2, b3, b4, b5] = [tt, ff, tt, ff, ff, ff] ∧
      a = ast.syscall ∧
      l = []))

theorem decode_two_two' {rex a b0 b1 b2 b3 b4 b5 b6 b7 l} :
  decode_two rex a (⟨[b0, b1, b2, b3, b4, b5, b6, b7], rfl⟩ :: l) →
  decode_two' rex a b0 b1 b2 b3 b4 b5 b6 b7 l :=
begin
  generalize e : (⟨[b0, b1, b2, b3, b4, b5, b6, b7], rfl⟩ :: l : list byte) = l',
  intro a, cases a,
  { cases e, rcases split_bits_ok a_a with ⟨h₁, h₂, _⟩,
    cases subtype.eq h₁,
    cases bitvec.reify_eq h₂,
    exact ⟨rfl, _, _, _, a_a_1, cond_code.bits_eq a_a_2, rfl⟩ },
  { cases e, rcases split_bits_ok a_a with ⟨h₁, h₂, _⟩,
    cases subtype.eq h₁,
    cases bitvec.reify_eq h₂,
    exact ⟨_, _, a_a_1, cond_code.bits_eq a_a_2, rfl⟩ },
  { cases e, rcases split_bits_ok a_a with ⟨h₁, h₂, _⟩,
    cases subtype.eq h₁,
    cases bitvec.reify_eq h₂,
    exact ⟨_, _, _, a_a_1, cond_code.bits_eq a_a_2, rfl⟩ },
  { cases e, rcases split_bits_ok a_a with ⟨⟨⟩, h₁, _⟩,
    cases bitvec.reify_eq h₁,
    exact ⟨rfl, _, _, a_a_1, rfl⟩ },
  { cases e, rcases split_bits_ok a_a with ⟨⟨⟩, h₁, ⟨⟩, h₂, _⟩,
    cases bitvec.reify_eq h₁,
    cases bitvec.reify_eq h₂,
    exact ⟨rfl, _, _, a_a_1, rfl⟩ },
  { cases e, rcases split_bits_ok a_a with ⟨⟨⟩, h₁, _⟩,
    cases bitvec.reify_eq h₁,
    exact ⟨rfl, _, _, a_a_1, rfl⟩ },
  { injection e, cases congr_arg subtype.val (bitvec.reify_eq' h_1),
    cases h_2, exact ⟨rfl, rfl, rfl⟩ },
end

theorem decode_two_nil {rex a} : ¬ decode_two rex a [].

theorem decode_two.determ_aux {rex a₁ a₂ l l'} :
  decode_two rex a₁ l → decode_two rex a₂ (l ++ l') → (a₁, l') = (a₂, []) :=
begin
  cases l with b l, {exact decode_two_nil.elim},
  apply byte_split b, introv h1 h2,
  replace h1 := decode_two_two' h1,
  replace h2 := decode_two_two' h2,
  unfold decode_two' at h1 h2,
  repeat { do
    `(cond %%e _ _) ← tactic.get_local `h1 >>= tactic.infer_type,
    tactic.cases e $> (); `[dsimp only [cond] at h1 h2] },
  { rcases h1.2 with ⟨rfl, rfl⟩,
    rcases h2.2 with ⟨rfl, ⟨⟩⟩, refl },
  { rcases h1.2 with ⟨reg1, r1, h11, h12, h13, rfl⟩,
    rcases h2.2 with ⟨reg2, r2, h21, h22, h23, rfl⟩,
    cases read_ModRM.determ_aux h12 h22,
    cases h13.symm.trans h23, refl },
  { rcases h1 with ⟨imm1, code1, h11, h12, rfl⟩,
    rcases h2 with ⟨imm2, code2, h21, h22, rfl⟩,
    cases read_imm32.determ_aux h11 h21,
    cases h12.symm.trans h22, refl },
  { rcases h1 with ⟨reg1, r1, code1, h11, h12, rfl⟩,
    rcases h2 with ⟨reg2, r2, code2, h21, h22, rfl⟩,
    cases read_ModRM.determ_aux h11 h21,
    cases h12.symm.trans h22, refl },
  { rcases h1 with ⟨reg1, r1, code1, h11, h12, rfl⟩,
    rcases h2 with ⟨reg2, r2, code2, h21, h22, rfl⟩,
    cases read_ModRM.determ_aux h11 h21, refl },
  { rcases h1.2 with ⟨reg1, r1, h11, rfl⟩,
    rcases h2.2 with ⟨reg2, r2, h21, rfl⟩,
    cases read_ModRM.determ_aux h11 h21, refl },
  { rcases h1.2 with ⟨reg1, r1, h11, rfl⟩,
    rcases h2.2 with ⟨reg2, r2, h21, rfl⟩,
    cases read_ModRM.determ_aux h11 h21, refl },
end

theorem decode_two.determ {rex a₁ a₂ l}
  (h₁ : decode_two rex a₁ l) (h₂ : decode_two rex a₂ l) : a₁ = a₂ :=
by cases decode_two.determ_aux h₁
  (by rw list.append_nil; exact h₂); refl

def decode_hi' (v : bool) (sz : wsize) (r : RM) :
  ∀ (b0 b1 b2 x : bool), ast → list byte → Prop
| ff ff ff ff a l := ∃ imm,
                      read_imm sz imm l ∧
                      a = ast.binop binop.tst sz (dest_src.Rm_i r imm)
| ff tt ff ff a l := a = ast.unop unop.not sz r ∧ l = []
| tt tt ff ff a l := a = ast.unop unop.neg sz r ∧ l = []
| ff ff tt ff a l := a = ast.mul sz r ∧ l = []
| ff tt tt ff a l := a = ast.div sz r ∧ l = []
| ff ff ff tt a l := a = ast.unop unop.inc sz r ∧ l = []
| tt ff ff tt a l := a = ast.unop unop.dec sz r ∧ l = []
| ff tt ff tt a l := a = ast.call (imm_rm.rm r) ∧ l = []
| ff ff tt tt a l := a = ast.jump r ∧ l = []
| ff tt tt tt a l := a = ast.push (imm_rm.rm r) ∧ l = []
| _  _  _  _  a l := false

theorem decode_hi_hi' {v sz r x b0 b1 b2 a l}
  (h : decode_hi v sz r x ⟨[b0, b1, b2], rfl⟩ a l) : decode_hi' v sz r b0 b1 b2 x a l :=
begin
  generalize_hyp e : (⟨[b0, b1, b2], rfl⟩ : bitvec 3) = opc at h,
  induction h; cases congr_arg subtype.val (bitvec.reify_eq' e),
  exact ⟨_, h_a, rfl⟩, all_goals { exact ⟨rfl, rfl⟩ }
end

theorem decode_hi.determ_aux {v sz r x a₁ a₂ l l'} : ∀ {opc},
  decode_hi v sz r x opc a₁ l → decode_hi v sz r x opc a₂ (l ++ l') → (a₁, l') = (a₂, [])
| ⟨[b0, b1, b2], _⟩ h1 h2 := begin
  replace h1 := decode_hi_hi' h1,
  replace h2 := decode_hi_hi' h2, clear decode_hi.determ_aux,
  cases b0; cases b1; cases b2; cases x; cases h1; cases h2,
  { cases read_imm.determ_aux h1_h.1 h2_h.1,
    cases h1_h.2.trans h2_h.2.symm, refl },
  all_goals {
    rw [h1_left, ← h2_left],
    cases h1_right, cases h2_right, refl }
end

theorem decode_hi.determ {v sz r x opc a₁ a₂ l}
  (h₁ : decode_hi v sz r x opc a₁ l) (h₂ : decode_hi v sz r x opc a₂ l) : a₁ = a₂ :=
by cases decode_hi.determ_aux h₁
  (by rw list.append_nil; exact h₂); refl

def decode_aux' (rex : REX) (a : ast) (b0 b1 b2 b3 b4 b5 b6 b7 : bool) (l : list byte) : Prop :=
cond b7
  (cond b6
    (cond b5
      (cond b4
        (cond b2
          (cond b1
            ( -- hi
              let v := b0, sz := op_size_W rex v in
              ∃ opc r l1 l2,
              read_opcode_ModRM rex opc r l1 ∧
              decode_hi v sz r b3 opc a l2 ∧
              l = l1 ++ l2)
            ( -- cmc
              b0 = tt ∧
              a = ast.cmc ∧
              l = []))
          ( -- clc, stc
            [b1, b3] = [ff, tt] ∧
            a = cond b0 ast.stc ast.clc ∧
            l = []))
        (cond b0
          ( -- jump
            [b2, b3] = [ff, tt] ∧
            ∃ imm,
            (if b1 then read_imm8 imm l else read_imm32 imm l) ∧
            a = ast.jcc cond_code.always imm)
          ( -- call
           [b2, b3] = [ff, tt] ∧
            ∃ imm,
            read_imm32 imm l ∧
            a = ast.call (imm_rm.imm imm))))
      ( let v := b0, sz := op_size_W rex v in
        cond b4
        ( -- binop_hi_reg
          [b2, b3] = [ff, ff] ∧
          ∃ opc r op,
          read_opcode_ModRM rex opc r l ∧ opc ≠ 6 ∧
          binop.bits op (rex_reg tt opc) ∧
          let src_dst := if b1 then dest_src.Rm_r r RCX else dest_src.Rm_i r 1 in
          a = ast.binop op sz src_dst)
        (cond b3
          ( -- leave
            [b0, b1, b2] = [tt, ff, ff] ∧
            a = ast.leave ∧
            l = [])
          (cond b2
            ( -- mov_imm
              b1 = tt ∧
              ∃ opc r imm l1 l2,
              read_opcode_ModRM rex opc r l1 ∧
              read_imm sz imm l2 ∧
              a = ast.mov sz (dest_src.Rm_i r imm) ∧
              l = l1 ++ l2)
            (cond b1
              ( -- ret
                ∃ imm,
                (if v then imm = 0 ∧ l = [] else read_imm16 imm l) ∧
                a = ast.ret imm)
              ( -- binop_hi
                ∃ opc r imm op l1 l2,
                read_opcode_ModRM rex opc r l1 ∧ opc ≠ 6 ∧
                binop.bits op (rex_reg tt opc) ∧
                read_imm8 imm l2 ∧
                a = ast.binop op sz (dest_src.Rm_i r imm) ∧
                l = l1 ++ l2))))))
    (cond b5
      (cond b4
        ( -- mov64
          let v := b3, sz := op_size_W rex v in
          ∃ imm,
          read_full_imm sz imm l ∧
          a = ast.mov sz (dest_src.Rm_i (RM.reg ⟨[b0, b1, b2, rex.B], rfl⟩) imm))
        ( -- test_rax
          [b1, b2, b3] = [ff, ff, tt] ∧
          let v := b0, sz := op_size tt rex.W v in
          ∃ imm,
          read_imm sz imm l ∧
          a = ast.binop binop.tst sz (dest_src.Rm_i (RM.reg RAX) imm)))
      (cond b4
        ( -- xchg_rax
          b3 = ff ∧
          let sz := op_size tt rex.W tt in
          a = ast.xchg sz (RM.reg RAX) ⟨[b0, b1, b2, rex.B], rfl⟩ ∧
          l = [])
        (cond b3
          (cond b2
            (cond b1
              ( -- pop_rm
                b0 = tt ∧
                ∃ r,
                read_opcode_ModRM rex 0 r l ∧
                a = ast.pop r)
              ( -- lea
                b0 = tt ∧
                ∃ reg r,
                let sz := op_size tt rex.W tt in
                read_ModRM rex reg r l ∧ RM.is_mem r ∧
                a = ast.lea sz (dest_src.R_rm reg r)))
            ( -- mov
              let v := b0, sz := op_size_W rex v in
              ∃ reg r,
              read_ModRM rex reg r l ∧
              let src_dst := if b1 then dest_src.R_rm reg r else dest_src.Rm_r r reg in
              a = ast.mov sz src_dst))
          (cond b2
            ( let v := b0, sz := op_size_W rex v in
              -- xchg, test
              ∃ reg r,
              read_ModRM rex reg r l ∧
              a = cond b1 (ast.xchg sz r reg)
                (ast.binop binop.tst sz (dest_src.Rm_r r reg)))
            ( -- binop_imm, binop_imm8
              let sz := op_size_W rex (cond b1 tt b0) in
              ∃ opc r l1 imm l2 op,
              read_opcode_ModRM rex opc r l1 ∧
              binop.bits op (EXTZ opc) ∧
              cond b1 (read_imm8 imm l2) (read_imm sz imm l2) ∧
              a = ast.binop op sz (dest_src.Rm_i r imm) ∧
              l = l1 ++ l2))))))
  (cond b6
    (cond b5
      (cond b4
        ( -- jcc8
          ∃ code imm,
          cond_code.from_bits b0 b1 b2 b3 = some code ∧
          read_imm8 imm l ∧
          a = ast.jcc code imm)
        (cond b3
          ( -- push_imm
            [b0, b2] = [ff, ff] ∧
            ∃ imm,
            read_imm (if b1 then wsize.Sz8 ff else wsize.Sz32) imm l ∧
            a = ast.push (imm_rm.imm imm))
          ( -- movsx
            [b0, b1, b2] = [tt, tt, ff] ∧
            ∃ reg r,
            read_ModRM rex reg r l ∧
            a = ast.movsx wsize.Sz32 (dest_src.R_rm reg r) wsize.Sz64)))
      (cond b4
        ( -- pop, push_rm
          let reg := RM.reg ⟨[b0, b1, b2, rex.B], rfl⟩ in
          a = cond b3 (ast.pop reg) (ast.push (imm_rm.rm reg)) ∧
          l = [])
        ( -- prefix byte
          false)))
    (cond b2
      (cond b1
        ( -- decode_two
          [b0, b3, b4, b5] = [tt, tt, ff, ff] ∧
          decode_two rex a l)
        ( -- binop_imm_rax
          let v := b0, sz := op_size_W rex v,
              op := binop.from_bits b3 b4 b5 ff in
          ∃ imm, read_imm sz imm l ∧
          a = ast.binop op sz (dest_src.Rm_i (RM.reg RAX) imm)))
      ( -- binop1
        let v := b0, d := b1, sz := op_size_W rex v,
            op := binop.from_bits b3 b4 b5 ff in
        ∃ reg r, read_ModRM rex reg r l ∧
        let src_dst := if d then dest_src.R_rm reg r else dest_src.Rm_r r reg in
        a = ast.binop op sz src_dst)))

theorem decode_aux_aux' {rex a b0 b1 b2 b3 b4 b5 b6 b7 l} :
  decode_aux rex a (⟨[b0, b1, b2, b3, b4, b5, b6, b7], rfl⟩ :: l) →
  decode_aux' rex a b0 b1 b2 b3 b4 b5 b6 b7 l :=
begin
  generalize e : (⟨[b0, b1, b2, b3, b4, b5, b6, b7], rfl⟩ :: l : list byte) = l',
  intro a, cases a,
  { cases e, rcases split_bits_ok a_a with ⟨⟨⟩, ⟨⟩, ⟨⟩, h₁, h₂, _⟩,
    cases subtype.eq h₁,
    cases bitvec.reify_eq h₂,
    cases binop.bits_eq a_a_2,
    exact ⟨_, _, a_a_1, rfl⟩ },
  { cases e, rcases split_bits_ok a_a with ⟨⟨⟩, h₁, h₂, h₃, _⟩,
    cases bitvec.reify_eq h₁,
    cases subtype.eq h₂,
    cases bitvec.reify_eq h₃,
    cases binop.bits_eq a_a_1,
    exact ⟨_, a_a_2, rfl⟩ },
  { cases e, rcases split_bits_ok a_a with ⟨⟨⟩, h₁, _⟩,
    cases bitvec.reify_eq h₁,
    exact ⟨_, _, _, _, _, _, a_a_1, a_a_3, a_a_2, rfl, rfl⟩ },
  { injection e, cases congr_arg subtype.val (bitvec.reify_eq' h_1),
    exact ⟨_, _, _, _, _, _, a_a, a_a_1, a_a_2, rfl, h_2⟩ },
  { cases e, rcases split_bits_ok a_a with ⟨⟨⟩, h₁, _⟩,
    cases bitvec.reify_eq h₁,
    exact ⟨_, _, _, _, _, _, a_a_1, a_a_2, a_a_3, a_a_4, rfl, rfl⟩ },
  { cases e, rcases split_bits_ok a_a with ⟨⟨⟩, ⟨⟩, h₁, _⟩,
    cases bitvec.reify_eq h₁,
    exact ⟨rfl, _, _, _, a_a_1, a_a_2, a_a_3, rfl⟩ },
  { injection e, cases congr_arg subtype.val (bitvec.reify_eq' h_1),
    cases h_2, exact ⟨rfl, a_a_1⟩ },
  { injection e, cases congr_arg subtype.val (bitvec.reify_eq' h_1),
    cases h_2, exact ⟨rfl, _, _, a_a, rfl⟩ },
  { cases e, rcases split_bits_ok a_a with ⟨⟨⟩, ⟨⟩, h₁, _⟩,
    cases bitvec.reify_eq h₁,
    exact ⟨_, _, a_a_1, rfl⟩ },
  { cases e, rcases split_bits_ok a_a with ⟨h₁, ⟨⟩, h₂, _⟩,
    cases subtype.eq h₁,
    cases bitvec.reify_eq h₂,
    exact ⟨_, a_a_1, rfl⟩ },
  { cases e, rcases split_bits_ok a_a with ⟨⟨⟩, h₁, _⟩,
    cases bitvec.reify_eq h₁,
    exact ⟨rfl, _, _, _, _, _, a_a_1, a_a_2, rfl, rfl⟩ },
  { cases e, rcases split_bits_ok a_a with ⟨⟨⟩, h₁, _⟩,
    cases bitvec.reify_eq h₁,
    exact ⟨_, _, a_a_1, rfl⟩ },
  { cases e, rcases split_bits_ok a_a with ⟨h₁, h₂, _⟩,
    cases subtype.eq h₁,
    cases bitvec.reify_eq h₂,
    exact ⟨rfl, rfl, rfl⟩ },
  { cases e, rcases split_bits_ok a_a with ⟨⟨⟩, ⟨⟩, h₁, _⟩,
    cases bitvec.reify_eq h₁,
    exact ⟨rfl, _, a_a_1, rfl⟩ },
  { cases e, rcases split_bits_ok a_a with ⟨h₁, h₂, _⟩,
    cases subtype.eq h₁,
    cases bitvec.reify_eq h₂,
    exact ⟨rfl, rfl⟩ },
  { cases e, rcases split_bits_ok a_a with ⟨h₁, h₂, _⟩,
    cases subtype.eq h₁,
    cases bitvec.reify_eq h₂,
    exact ⟨rfl, rfl⟩ },
  { injection e, cases congr_arg subtype.val (bitvec.reify_eq' h_1),
    cases h_2, exact ⟨rfl, _, a_a, rfl⟩ },
  { cases e, rcases split_bits_ok a_a with ⟨⟨⟩, ⟨⟩, h₁, _⟩,
    cases bitvec.reify_eq h₁,
    exact ⟨rfl, _, a_a_1, rfl⟩ },
  { cases e, rcases split_bits_ok a_a with ⟨h₁, h₂, _⟩,
    cases subtype.eq h₁,
    cases bitvec.reify_eq h₂,
    exact ⟨_, _, cond_code.bits_eq a_a_1, a_a_2, rfl⟩ },
  { injection e, cases congr_arg subtype.val (bitvec.reify_eq' h_1),
    cases h_2, exact ⟨rfl, _, a_a, rfl⟩ },
  { cases e, rcases split_bits_ok a_a with ⟨⟨⟩, h₁, _⟩,
    cases bitvec.reify_eq h₁,
    exact ⟨_, a_a_1, rfl⟩ },
  { injection e, cases congr_arg subtype.val (bitvec.reify_eq' h_1),
    cases h_2, exact ⟨rfl, rfl, rfl⟩ },
  { injection e, cases congr_arg subtype.val (bitvec.reify_eq' h_1),
    cases h_2, exact ⟨rfl, _, _, a_a, a_a_1, rfl⟩ },
  { cases e, rcases split_bits_ok a_a with ⟨⟨⟩, h₁, _⟩,
    cases bitvec.reify_eq h₁,
    exact ⟨_, _, a_a_1, rfl⟩ },
  { cases e, rcases split_bits_ok a_a with ⟨⟨⟩, h₁, _⟩,
    cases bitvec.reify_eq h₁,
    exact ⟨rfl, _, a_a_1, rfl⟩ },
  { injection e, cases congr_arg subtype.val (bitvec.reify_eq' h_1),
    cases h_2, exact ⟨rfl, rfl, rfl⟩ },
  { injection e, cases congr_arg subtype.val (bitvec.reify_eq' h_1),
    cases h_2, exact ⟨rfl, rfl, rfl⟩ },
  { injection e, cases congr_arg subtype.val (bitvec.reify_eq' h_1),
    cases h_2, exact ⟨rfl, rfl, rfl⟩ },
  { cases e, rcases split_bits_ok a_a_1 with ⟨⟨⟩, h₁, ⟨⟩, h₂, _⟩,
    cases bitvec.reify_eq h₁,
    cases bitvec.reify_eq h₂,
    exact ⟨_, _, _, _, a_a_2, a_a_3, rfl⟩ },
end

theorem decode_aux_nil {rex a} : ¬ decode_aux rex a [].

theorem decode_aux.determ_aux {rex a₁ a₂ l l'} :
  decode_aux rex a₁ l → decode_aux rex a₂ (l ++ l') → (a₁, l') = (a₂, []) :=
begin
  cases l with b l, {exact decode_aux_nil.elim},
  apply byte_split b, introv h1 h2,
  replace h1 := decode_aux_aux' h1,
  replace h2 := decode_aux_aux' h2,
  unfold decode_aux' at h1 h2,
  repeat { do
    `(cond %%e _ _) ← tactic.get_local `h1 >>= tactic.infer_type,
    tactic.cases e $> (); `[dsimp only [cond] at h1 h2] },
  { rcases h1 with ⟨reg1, r1, h11, rfl⟩,
    rcases h2 with ⟨reg2, r2, h21, rfl⟩,
    cases read_ModRM.determ_aux h11 h21, refl },
  { rcases h1 with ⟨imm1, h11, rfl⟩,
    rcases h2 with ⟨imm2, h21, rfl⟩,
    cases read_imm.determ_aux h11 h21, refl },
  { exact decode_two.determ_aux h1.2 h2.2 },
  { cases h2 },
  { rcases h1 with ⟨rfl, rfl⟩,
    rcases h2 with ⟨rfl, ⟨⟩⟩, refl },
  { rcases h1.2 with ⟨reg1, r1, h11, rfl⟩,
    rcases h2.2 with ⟨reg2, r2, h21, rfl⟩,
    cases read_ModRM.determ_aux h11 h21, refl },
  { rcases h1.2 with ⟨imm1, h11, rfl⟩,
    rcases h2.2 with ⟨imm2, h21, rfl⟩,
    cases read_imm.determ_aux h11 h21, refl },
  { rcases h1 with ⟨code1, imm1, h11, h12, rfl⟩,
    rcases h2 with ⟨code2, imm2, h21, h22, rfl⟩,
    cases h11.symm.trans h21,
    cases read_imm8.determ_aux h12 h22, refl },
  { rcases h1 with ⟨opc1, r1, l11, imm1, l12, op1, h11, h12, h13, rfl, rfl⟩,
    rcases h2 with ⟨opc2, r2, l21, imm2, l22, op2, h21, h22, h23, rfl, e⟩,
    cases read_opcode_ModRM.determ₂_aux h11 h21 e,
    cases binop.bits.determ h12 h22,
    cases b1,
    { cases read_imm.determ_aux h13 h23, refl },
    { cases read_imm8.determ_aux h13 h23, refl } },
  { rcases h1 with ⟨reg1, r1, h11, rfl⟩,
    rcases h2 with ⟨reg2, r2, h21, rfl⟩,
    cases read_ModRM.determ_aux h11 h21, refl },
  { rcases h1 with ⟨reg1, r1, h11, rfl⟩,
    rcases h2 with ⟨reg2, r2, h21, rfl⟩,
    cases read_ModRM.determ_aux h11 h21, refl },
  { rcases h1.2 with ⟨reg1, r1, h11, h12, rfl⟩,
    rcases h2.2 with ⟨reg2, r2, h21, h22, rfl⟩,
    cases read_ModRM.determ_aux h11 h21, refl },
  { rcases h1.2 with ⟨r1, h11, h12, rfl⟩,
    rcases h2.2 with ⟨r2, h21, h22, rfl⟩,
    cases read_opcode_ModRM.determ_aux h11 h21, refl },
  { rcases h1.2 with ⟨rfl, rfl⟩,
    rcases h2.2 with ⟨rfl, ⟨⟩⟩, refl },
  { rcases h1.2 with ⟨imm1, h11, rfl⟩,
    rcases h2.2 with ⟨imm2, h21, rfl⟩,
    cases read_imm.determ_aux h11 h21, refl },
  { rcases h1 with ⟨imm1, h11, rfl⟩,
    rcases h2 with ⟨imm2, h21, rfl⟩,
    cases read_full_imm.determ_aux h11 h21, refl },
  { rcases h1 with ⟨opc1, r1, imm1, op1, l11, l12, h11, _, h12, h13, rfl, rfl⟩,
    rcases h2 with ⟨opc2, r2, imm2, op2, l21, l22, h21, _, h22, h23, rfl, e⟩,
    cases read_opcode_ModRM.determ₂_aux h11 h21 e,
    cases binop.bits.determ h12 h22,
    cases read_imm8.determ_aux h13 h23, refl },
  { rcases h1 with ⟨imm1, h11, rfl⟩,
    rcases h2 with ⟨imm2, h21, rfl⟩,
    split_ifs at h11 h21,
    { rcases h11 with ⟨rfl, rfl⟩,
      rcases h21 with ⟨rfl, ⟨⟩⟩, refl },
    { cases read_imm16.determ_aux h11 h21, refl } },
  { rcases h1 with ⟨opc1, r1, imm1, op1, l11, l12, h11, h12, rfl, rfl⟩,
    rcases h2 with ⟨opc2, r2, imm2, op2, l21, l22, h21, h22, rfl, e⟩,
    cases read_opcode_ModRM.determ₂_aux h11 h21 e,
    cases read_imm.determ_aux h12 h22, refl },
  { rcases h1.2 with ⟨rfl, rfl⟩,
    rcases h2.2 with ⟨rfl, ⟨⟩⟩, refl },
  { rcases h1.2 with ⟨opc1, r1, op1, h11, _, h12, rfl⟩,
    rcases h2.2 with ⟨opc2, r2, op2, h21, _, h22, rfl⟩,
    cases read_opcode_ModRM.determ_aux h11 h21,
    cases binop.bits.determ h12 h22, refl },
  { rcases h1.2 with ⟨imm1, h11, rfl⟩,
    rcases h2.2 with ⟨imm2, h21, rfl⟩,
    cases read_imm32.determ_aux h11 h21, refl },
  { rcases h1.2 with ⟨imm1, h11, rfl⟩,
    rcases h2.2 with ⟨imm2, h21, rfl⟩,
    split_ifs at h11 h21,
    { cases read_imm8.determ_aux h11 h21, refl },
    { cases read_imm32.determ_aux h11 h21, refl } },
  { rcases h1.2 with ⟨rfl, rfl⟩,
    rcases h2.2 with ⟨rfl, ⟨⟩⟩, refl },
  { rcases h1.2 with ⟨rfl, rfl⟩,
    rcases h2.2 with ⟨rfl, ⟨⟩⟩, refl },
  { rcases h1 with ⟨opc1, r1, l11, l12, h11, h12, rfl⟩,
    rcases h2 with ⟨opc2, r2, l21, l22, h21, h22, e⟩,
    cases read_opcode_ModRM.determ₂_aux h11 h21 e,
    exact decode_hi.determ_aux h12 h22 },
end

theorem decode_aux.determ {rex a₁ a₂ l}
  (h₁ : decode_aux rex a₁ l) (h₂ : decode_aux rex a₂ l) : a₁ = a₂ :=
by cases decode_aux.determ_aux h₁
  (by rw list.append_nil; exact h₂); refl

theorem decode.no_prefix {rex rex' a l b l'} :
  read_prefixes rex l → b ∈ l → ¬ decode_aux rex' a (b :: l') :=
begin
  rintro ⟨⟩ (rfl|⟨⟨⟩⟩),
  -- generalize e : b :: l' = l₂,
  revert a_1_a, apply byte_split b, intros,
  rcases split_bits_ok a_1_a with ⟨_, ⟨⟩, _⟩,
  exact decode_aux_aux'
end

theorem decode_nil {a} : ¬ decode a [] :=
begin
  generalize e : [] = l, rintro ⟨⟩,
  cases a_1_l1; cases e,
  exact decode_aux_nil a_1_a_2
end

theorem decode.determ_aux {a₁ a₂ l l'}
  (h₁ : decode a₁ l) (h₂ : decode a₂ (l ++ l')) : (a₁, l') = (a₂, []) :=
begin
  generalize_hyp e : l ++ l' = x at h₂,
  induction h₁, induction h₂,
  rw [list.append_assoc, list.append_eq_append_iff] at e,
  rcases e with ⟨_|⟨b, x⟩, rfl, e⟩ | ⟨_|⟨b, x⟩, rfl, rfl⟩,
  { rw list.append_nil at h₂_a_1, cases e,
    cases read_prefixes.determ h₁_a_1 h₂_a_1,
    exact decode_aux.determ_aux h₁_a_2 h₂_a_2 },
  { cases h₁_l2 with b' l2, cases decode_aux_nil h₁_a_2,
    injection e, subst b',
    cases decode.no_prefix h₂_a_1 (list.mem_append_right _ (or.inl rfl)) h₁_a_2 },
  { rw list.append_nil at h₁_a_1,
    cases read_prefixes.determ h₁_a_1 h₂_a_1,
    exact decode_aux.determ_aux h₁_a_2 h₂_a_2 },
  { cases decode.no_prefix h₁_a_1 (list.mem_append_right _ (or.inl rfl)) h₂_a_2 },
end

theorem decode.determ {a₁ a₂ l}
  (h₁ : decode a₁ l) (h₂ : decode a₂ l) : a₁ = a₂ :=
by cases decode.determ_aux h₁
  (by rw list.append_nil; exact h₂); refl

instance : add_comm_monoid perm :=
{ zero := ⟨ff, ff, ff⟩,
  add_assoc := λ a b c,
    show perm.mk (_||_||_) (_||_||_) (_||_||_) = _,
    by repeat {rw bool.bor_assoc}; refl,
  zero_add := λ ⟨r, w, x⟩,
    show perm.mk (ff||_) (ff||_) (ff||_) = _,
    by repeat {rw ff_bor},
  add_zero := λ ⟨r, w, x⟩,
    show perm.mk (_||ff) (_||ff) (_||ff) = _,
    by repeat {rw bor_ff},
  add_comm := λ a b,
    show perm.mk (_||_) (_||_) (_||_) = _,
    by rw [bool.bor_comm, bool.bor_comm a.isW, bool.bor_comm a.isX]; refl,
  ..perm.has_add }

theorem perm.add_self : ∀ p : perm, p + p = p
| ⟨r, w, x⟩ :=
  show perm.mk (r||r) (w||w) (x||x) = _,
  by repeat {rw bor_self}

instance : partial_order perm :=
{ le_refl := perm.add_self,
  le_trans := λ a b c (h₁ : a + b = b) (h₂ : b + c = c),
    show a + c = c, by rw [← h₂, ← add_assoc, h₁],
  le_antisymm := λ a b (h₁ : a + b = b) (h₂ : b + a = a),
    by rw [← h₂, add_comm, h₁],
  ..perm.has_le }

theorem perm.le_add_left {p₁ p₂ : perm} : p₁ ≤ p₁ + p₂ :=
show _=_, by rw [← add_assoc, perm.add_self]

theorem mem.read1.determ {p1 p2 m a b1 b2} :
  mem.read1 p1 m a b1 → mem.read1 p2 m a b2 → b1 = b2 :=
by rintro ⟨_, rfl, _⟩ ⟨_, rfl, _⟩; refl

theorem mem.read'.determ_aux {p1 p2 m a l1 l2}
  (h₁ : mem.read' p1 m a l1) (h₂ : mem.read' p2 m a l2) :
  l1 <+: l2 ∨ l2 <+: l1 :=
begin
  induction h₁ generalizing l2,
  { exact or.inl (list.nil_prefix _) },
  cases h₂,
  { exact or.inr (list.nil_prefix _) },
  cases h₁_a.determ h₂_a,
  rw [list.prefix_cons_inj, list.prefix_cons_inj],
  exact h₁_ih h₂_a_1,
end

theorem mem.read'.determ_len {p1 p2 m a l1 l2}
  (h₁ : mem.read' p1 m a l1) (h₂ : mem.read' p2 m a l2)
  (h : l1.length = l2.length) : l1 = l2 :=
(mem.read'.determ_aux h₁ h₂).elim
  (λ h', list.eq_of_prefix_of_length_eq h' h)
  (λ h', (list.eq_of_prefix_of_length_eq h' h.symm).symm)

theorem mem_decode.determ {p1 p2 m a l1 l2 ast1 ast2}
  (m₁ :  mem.read' p1 m a l1) (h₁ : decode ast1 l1)
  (m₂ :  mem.read' p2 m a l2) (h₂ : decode ast2 l2) :
  (ast1, l1) = (ast2, l2) :=
begin
  rcases mem.read'.determ_aux m₁ m₂ with ⟨x, rfl⟩ | ⟨x, rfl⟩,
  { cases decode.determ_aux h₁ h₂, simp },
  { cases decode.determ_aux h₂ h₁, simp },
end

theorem config.step_noIO {k k₁ k₂} :
  config.step k k₁ → ¬ config.isIO k k₂ :=
λ h₁ h₂, begin
  cases h₁, cases h₂,
  cases mem_decode.determ h₁_a_1 h₁_a_2 h₂_a h₂_a_1,
  rcases h₁_a_3 with ⟨_, s₁, _, ⟨⟩, _⟩
end

theorem mem.write1.determ {m a b m₁ m₂}
  (h₁ : mem.write1 m a b m₁)
  (h₂ : mem.write1 m a b m₂) : m₁ = m₂ :=
by cases h₁; cases h₂; refl

theorem mem.write.determ {m a l m₁ m₂}
  (h₁ : mem.write m a l m₁)
  (h₂ : mem.write m a l m₂) : m₁ = m₂ :=
begin
  induction h₁ generalizing m₂; cases h₂, refl,
  cases mem.write1.determ h₁_a h₂_a,
  cases h₁_ih h₂_a_1, refl
end

theorem config.write_mem.determ {k a l k₁ k₂}
  (h₁ : config.write_mem k a l k₁)
  (h₂ : config.write_mem k a l k₂) : k₁ = k₂ :=
by cases h₁; cases h₂; cases mem.write.determ h₁_a_1 h₂_a_1; refl

theorem EA.write.determ {k ea sz v k₁ k₂}
  (h₁ : EA.write k ea sz v k₁)
  (h₂ : EA.write k ea sz v k₂) : k₁ = k₂ :=
begin
  cases h₁; cases h₂, refl,
  cases bits_to_byte.determ h₁_a_1 h₂_a_1,
  exact config.write_mem.determ h₁_a_2 h₂_a_2
end

theorem config.isIO.determ {k k₁ k₂} :
  config.isIO k k₁ → config.isIO k k₂ →
  ∃ k' v₁ v₂,
    k₁ = config.set_reg k' 11 v₁ ∧
    k₂ = config.set_reg k' 11 v₂ :=
begin
  rintro ⟨l₁, _, m₁, d₁, _, _, ⟨⟩, ⟨⟩, k', a₁, q₁, _, ⟨⟨⟩, rfl⟩, h₁⟩
         ⟨l₂, _, m₂, d₂, _, _, ⟨⟩, ⟨⟩, k'', a₂, q₂, _, ⟨⟨⟩, rfl⟩, h₂⟩,
  cases mem_decode.determ m₁ d₁ m₂ d₂,
  cases EA.write.determ a₁ a₂,
  cases h₁, cases h₂,
  exact ⟨_, _, _, rfl, rfl⟩
end

theorem config.step.no_exit {k k₁ r} :
  config.step k k₁ → ¬ config.exit k r :=
λ h ⟨k', h', _⟩, config.step_noIO h h'

theorem set_reg_ne {k r r' q} (h : r' ≠ r) :
  (config.set_reg k r q).regs r' = k.regs r' :=
if_neg h

theorem config.set_reg_11_exec_exit {k v r} :
  exec_exit (config.set_reg k 11 v) r ↔ exec_exit k r :=
begin
  split; rintro ⟨e⟩; split,
  { rwa set_reg_ne at e, rintro ⟨⟩ },
  { rwa set_reg_ne, rintro ⟨⟩ },
end

theorem config.isIO.determ_exec {k k₁ k₂ r}
  (h₁ : config.isIO k k₁) (h₂ : config.isIO k k₂) :
  exec_exit k₁ r ↔ exec_exit k₂ r :=
begin
  rcases h₁.determ h₂ with ⟨k', v₁, v₂, rfl, rfl⟩,
  simp [config.set_reg_11_exec_exit],
end

theorem exec_io.no_exit {i o k i' o' k' ret r} :
  exec_io i o k (k.regs RAX) i' o' k' ret → ¬ exec_exit k r :=
begin
  rintro h ⟨e⟩, rw e at h,
  rcases h with ⟨_, _, _, _, e⟩ | ⟨_, _, _, _, _, _, _, e⟩;
  cases bitvec.reify_eq₂ e,
end

theorem read_from_fd.io_part {fd i H_dat i'}
  (H : read_from_fd fd i H_dat i') : i' <:+ i :=
begin
  cases H, apply list.suffix_refl,
  exact ⟨_, rfl⟩
end

theorem exec_read.io_part {i k fd count i' k' ret}
  (H : exec_read i k fd count i' k' ret) : i' <:+ i :=
begin
  cases H, apply list.suffix_refl,
  exact read_from_fd.io_part H_a_2
end

theorem exec_io.io_part {k₁ i₁ o₁ k₂ i₂ o₂ call ret}
  (H : exec_io i₁ o₁ k₁ call i₂ o₂ k₂ ret) :
  i₂ <:+ i₁ ∧ o₁ <+: o₂ :=
begin
  induction H, exact ⟨list.suffix_refl _, list.prefix_refl _⟩,
  exact ⟨exec_read.io_part H_a_2, list.prefix_refl _⟩,
end

theorem kcfg.step.no_exit {k k' r} :
  kcfg.step k k' → ¬ config.exit k.k r :=
begin
  rintro (⟨_, _, _, _, h⟩ | ⟨_, _, k₁, k₂, _, _, _, _, h₁, h⟩),
  { exact h.no_exit },
  { rintro ⟨k₃, h₂, e⟩,
    exact h.no_exit ((h₁.determ_exec h₂).2 e) },
end

theorem kcfg.step.io_part {k₁ i₁ o₁ k₂ i₂ o₂}
  (H : kcfg.step ⟨i₁, o₁, k₁⟩ ⟨i₂, o₂, k₂⟩) :
  i₂ <:+ i₁ ∧ o₁ <+: o₂ :=
begin
  cases H, exact ⟨list.suffix_refl _, list.prefix_refl _⟩,
  exact exec_io.io_part H_a_1
end

@[simp] theorem EXTZ_id {n} (w : bitvec n) : EXTZ w = w :=
begin
  suffices : ∀ l n, list.length l = n → (@EXTZ_aux l n).to_list = l,
  { exact subtype.eq (this w.1 _ w.2) },
  intro l, induction l; intros n e; cases e, {refl},
  unfold EXTZ_aux, rw [vector.to_list_cons, l_ih _ rfl],
end

@[simp] theorem EXTS_id {n} (w : bitvec n) : EXTS w = w :=
begin
  suffices : ∀ l a n, list.length l = n → (@EXTS_aux l a n).to_list = l,
  { exact subtype.eq (this w.1 _ _ w.2) },
  intro l, induction l; intros n a e; cases e, {refl},
  unfold EXTS_aux, rw [vector.to_list_cons, l_ih _ _ rfl],
end

theorem EA.read_reg_64 {r k q} :
  (EA.r r).read k wsize.Sz64 q ↔ q = k.regs r :=
by simp [EA.read]

theorem EA.readq_reg_64 {r k q} :
  (EA.r r).readq k wsize.Sz64 q ↔ q = k.regs r :=
by simp [EA.readq, EA.read_reg_64]

theorem EA.write_reg_64 {r k q k'} :
  (EA.r r).write k wsize.Sz64 q k' ↔ k' = k.set_reg r q :=
by split; [{rintro ⟨⟩, refl}, {rintro rfl, constructor}]

theorem EA.writeq_reg_64 {r k q k'} :
  (EA.r r).writeq k wsize.Sz64 q k' ↔ k' = k.set_reg r q :=
by simp [EA.writeq, EA.write_reg_64]

theorem mem.set.read'_exists {p m q w b v}
  (h1 : mem.read' p m q v) : ∃ v', mem.read' p (m.set w b) q v' :=
begin
  induction h1, {exact ⟨_, mem.read'.nil _ _ _⟩},
  cases h1_ih with v1 ih,
  rcases h1_a with ⟨_, rfl, h1⟩,
  exact ⟨_, mem.read'.cons ⟨_, rfl, h1⟩ ih⟩,
end

theorem mem.write.read'_exists {p m q a v v2 m'}
  (h1 : mem.read' p m q v) (h2 : mem.write m a v2 m') :
  ∃ v', mem.read' p m' q v' :=
begin
  induction h2 generalizing v, {exact ⟨_, h1⟩},
  cases h2_a with h3 h4,
  cases mem.set.read'_exists h1 with v1 h1,
  exact h2_ih h1,
end

theorem EA.read.determ {k ea sz w1 w2}
  (h1 : EA.read k ea sz w1) (h2 : EA.read k ea sz w2) : w1 = w2 :=
begin
  cases ea,
  { exact h1.trans h2.symm },
  { cases sz, cases sz, all_goals {exact h1.trans h2.symm} },
  { rcases h1 with ⟨_, a1, b1⟩,
    rcases h2 with ⟨_, a2, b2⟩,
    cases a1.determ_len a2 (b1.1.trans b2.1.symm),
    exact bits_to_byte.determ_l b1 b2 },
end

theorem EA.readq.determ {k ea sz q1 q2} :
  EA.readq k ea sz q1 → EA.readq k ea sz q2 → q1 = q2
| ⟨a1, b1, e1⟩ ⟨a2, b2, e2⟩ :=
  by cases b1.determ b2; exact e1.trans e2.symm

theorem hoare_p.bind {P P' : kcfg → Prop}
  (H : ∀ {{k}}, P k → hoare_p P' k) {k} : hoare_p P k → hoare_p P' k :=
begin
  intro h, induction h,
  exact H h_a,
  exact hoare_p.step h_a (λ k', h_ih _),
  by_cases h_ret = 0,
  { cases H (h_a_1 h),
    { exact hoare_p.zero a },
    { cases a with k' h, cases h.no_exit h_a },
    { exact hoare_p.exit _ _ a a_1 } },
  { exact hoare_p.exit _ _ h_a h.elim },
end

theorem hoare_p.mono {P P' : kcfg → Prop}
  (H : ∀ {{k}}, P k → P' k) {k} : hoare_p P k → hoare_p P' k :=
hoare_p.bind (λ k h, hoare_p.zero (H h))

end x86