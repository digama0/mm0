import x86.x86 data.list.basic

namespace x86

def decoder := state_t (list byte) option
instance : monad decoder := state_t.monad

def read1 : decoder byte :=
⟨λ l, list.cases_on l none (λ b l, some (b, l))⟩

@[class] def bitvec.reify {n} (v : bitvec n) (l : out_param (list bool)) : Prop :=
bitvec.from_bits_fill ff l = v

theorem bitvec.reify.mk {n} (v) {l} [h : @bitvec.reify n v l] :
  bitvec.from_bits_fill ff l = v := h

theorem bitvec.reify_eq {n v l l'} [@bitvec.reify n v l] (h : l' = v.1) :
  l' = (@bitvec.from_bits_fill ff l n).1 := by rwa bitvec.reify.mk v
theorem bitvec.reify_eq' {n v l l'} [@bitvec.reify n v l] (h : l' = v) :
  l' = @bitvec.from_bits_fill ff l n := by rwa bitvec.reify.mk v

theorem bitvec.bits_to_nat_zero (n) : bitvec.bits_to_nat (list.repeat ff n) = 0 :=
by simp [bitvec.bits_to_nat]; induction n; simp *

@[simp] theorem bitvec.to_nat_nil : bitvec.to_nat vector.nil = 0 := rfl

@[simp] theorem bitvec.to_nat_zero (n) : bitvec.to_nat (0 : bitvec n) = 0 :=
bitvec.bits_to_nat_zero _

@[simp] theorem bitvec.to_nat_cons (b) {n} (v : bitvec n) :
  bitvec.to_nat (b :: v) = nat.bit b (bitvec.to_nat v) := 
by cases v; refl

@[simp] theorem bitvec.of_nat_succ (n i : ℕ) :
  bitvec.of_nat n.succ i = i.bodd :: bitvec.of_nat n i.div2 :=
by rw [bitvec.of_nat, nat.bodd_div2_eq, bitvec.of_nat]

@[simp] theorem bitvec.of_nat_bit (n : ℕ) (b i) :
  bitvec.of_nat n.succ (nat.bit b i) = b :: bitvec.of_nat n i :=
by rw [bitvec.of_nat_succ, nat.div2_bit, nat.bodd_bit]

theorem bitvec.of_nat_zero (n) : bitvec.of_nat n 0 = 0 :=
by induction n; [refl, exact congr_arg (vector.cons ff) n_ih]

theorem bitvec.of_nat_one (n) : bitvec.of_nat n 1 = 1 :=
by cases n; [refl, exact congr_arg (vector.cons tt) (bitvec.of_nat_zero _)]

theorem bitvec.to_nat_nth {n} (i j) :
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

theorem bitvec.of_nat_bits_to_nat {n} (l : list bool) :
  bitvec.of_nat n (bitvec.bits_to_nat l) = bitvec.from_bits_fill ff l :=
begin
  rw bitvec.bits_to_nat,
  induction l generalizing n, exact bitvec.of_nat_zero _,
  cases n, refl,
  simp [*, bitvec.bits_to_nat, bitvec.from_bits_fill,
    bitvec.of_nat, nat.bodd_bit, nat.div2_bit]
end

theorem bitvec.reify_iff {n v l} : @bitvec.reify n v l ↔ bitvec.of_nat n (bitvec.bits_to_nat l) = v :=
iff_of_eq $ congr_arg (= v) (bitvec.of_nat_bits_to_nat _).symm

theorem bitvec.of_nat_bits_to_nat_eq {n} (l : list bool) (e : l.length = n) :
  bitvec.of_nat n (bitvec.bits_to_nat l) = ⟨l, e⟩ :=
begin
  induction n generalizing l; cases l; injection e, refl,
  simp [bitvec.bits_to_nat, nat.div2_bit, nat.bodd_bit],
  exact congr_arg (vector.cons l_hd) (n_ih _ h_1)
end

theorem bitvec.of_nat_to_nat : ∀ {n} (v : bitvec n),
  bitvec.of_nat n (bitvec.to_nat v) = v
| n ⟨l, e⟩ := bitvec.of_nat_bits_to_nat_eq l e

theorem bitvec.of_nat_from_bits_fill (n m i) (h : n ≤ m) :
  bitvec.of_nat n i = bitvec.from_bits_fill ff (bitvec.of_nat m i).1 :=
begin
  generalize e : bitvec.of_nat m i = v, cases v with l h, simp,
  induction n generalizing m i l e, exact (vector.eq_nil _).trans (vector.eq_nil _).symm,
  rw [bitvec.of_nat_succ], 
  cases m, cases h,
  rw [bitvec.of_nat_succ] at e,
  generalize e' : bitvec.of_nat m i.div2 = v, cases v with l' h',
  rw e' at e, injection e, subst l,
  rw [n_ih _ _ (nat.le_of_succ_le_succ h) _ _ e', bitvec.from_bits_fill],
end

theorem bitvec.of_nat_bit0_aux {n} (j : bitvec (nat.succ n)) :
  bit0 j = ff :: bitvec.from_bits_fill ff (j.val) := 
begin
  change bitvec.of_nat n.succ (bit0 (bitvec.to_nat j)) = _,
  rw [bitvec.of_nat_succ,
    nat.bodd_bit0, nat.div2_bit0, bitvec.to_nat, bitvec.of_nat_bits_to_nat]
end

theorem bitvec.of_nat_bit0 (n i) : bitvec.of_nat n (bit0 i) = bit0 (bitvec.of_nat n i) :=
begin
  induction n generalizing i, refl,
  rw [bitvec.of_nat_succ,
    nat.bodd_bit0, nat.div2_bit0],
  rw [bitvec.of_nat_from_bits_fill _ _ _ (nat.le_succ _)],
  generalize : bitvec.of_nat n_n.succ i = j,
  rw bitvec.of_nat_bit0_aux,
end

theorem bitvec.of_nat_bit1 (n i) : bitvec.of_nat n (bit1 i) = bit1 (bitvec.of_nat n i) :=
begin
  induction n generalizing i, refl,
  rw [bitvec.of_nat_succ,
    nat.bodd_bit1, nat.div2_bit1],
  rw [bitvec.of_nat_from_bits_fill _ _ _ (nat.le_succ _)],
  generalize : bitvec.of_nat n_n.succ i = j,
  change _ = bitvec.of_nat _ (bitvec.to_nat (bit0 j) + bit0 (@bitvec.to_nat n_n 0) + 1),
  rw [bitvec.to_nat_zero],
  change _ = bitvec.of_nat _ (bitvec.to_nat (bit0 j) + 1),
  rw [bitvec.of_nat_bit0_aux, bitvec.to_nat_cons],
  change _ = bitvec.of_nat _ (nat.bit tt _),
  rw [bitvec.of_nat_bit, bitvec.of_nat_to_nat],
end

instance bitvec.reify_0 {n} : @bitvec.reify n 0 [] := rfl

instance bitvec.reify_1 {n} : @bitvec.reify n 1 [tt] :=
by cases n; exact rfl

instance bitvec.reify_bit0 {n} (v l) [h : @bitvec.reify n v l] :
  bitvec.reify (bit0 v) (ff :: l) :=
bitvec.reify_iff.2 $
by have := bitvec.of_nat_bit0 n (bitvec.bits_to_nat l);
   rwa [bitvec.reify_iff.1 h] at this

instance bitvec.reify_bit1 {n} (v l) [h : @bitvec.reify n v l] :
  bitvec.reify (bit1 v) (tt :: l) :=
bitvec.reify_iff.2 $
by have := bitvec.of_nat_bit1 n (bitvec.bits_to_nat l);
   rwa [bitvec.reify_iff.1 h] at this

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

theorem split_bits.determ {n l₁ l₂} (h₁ : split_bits n l₁) (h₂ : split_bits n l₂)
  (h : l₁.map sigma.fst = l₂.map sigma.fst) : l₁ = l₂ :=
begin
  induction l₁ generalizing n l₂; cases l₂; injection h, refl,
  cases l₁_hd with i v₁, cases l₂_hd with _ v₂, cases h_1,
  clear h h_1, induction i with i generalizing v₁ v₂ n,
  { cases h₁, cases h₂, rw l₁_ih h₁_a h₂_a h_2 },
  { cases h₁, cases h₂, cases i_ih _ _ h₁_a h₂_a, refl }
end

theorem read_prefixes.determ {r₁ r₂ l} : read_prefixes r₁ l → read_prefixes r₂ l → r₁ = r₂ :=
begin
  intros h₁ h₂, cases h₁; cases h₂; congr,
  cases split_bits.determ h₁_a h₂_a rfl, refl,
end

theorem decode_aux_nil {rex a} : ¬ decode_aux rex a [] :=
by rintro ⟨⟩; cases e

theorem decode_nil {a} : ¬ decode a [] :=
begin
  generalize e : [] = l, rintro ⟨⟩,
  cases a_1_l1; cases e,
  exact decode_aux_nil a_1_a_2
end

@[elab_as_eliminator] theorem byte_split {C : byte → Sort*}
   : ∀ b : byte, (∀ b0 b1 b2 b3 b4 b5 b6 b7,
    C ⟨[b0, b1, b2, b3, b4, b5, b6, b7], rfl⟩) → C b
| ⟨[b0, b1, b2, b3, b4, b5, b6, b7], rfl⟩ H := H _ _ _ _ _ _ _ _

theorem decode.no_prefix {rex rex' a l b l'} :
  read_prefixes rex l → b ∈ l → ¬ decode_aux rex' a (b :: l') :=
begin
  rintro ⟨⟩ (rfl|⟨⟨⟩⟩),
  generalize e : b :: l' = l₂,
  revert a_1_a l₂, apply byte_split b, intros,
  rcases split_bits_ok a_1_a with ⟨_, ⟨⟩, _⟩,
  rintro ⟨⟩,
  { cases e, rcases split_bits_ok a_2_a with ⟨_, _, _, _, h, _⟩, cases bitvec.reify_eq h },
  { cases e, rcases split_bits_ok a_2_a with ⟨_, _, _, h, _⟩, cases bitvec.reify_eq h },
  { cases e, rcases split_bits_ok a_2_a with ⟨_, h, _⟩, cases bitvec.reify_eq h },
  { injection e, cases bitvec.reify_eq' h_1 },
  { cases e, rcases split_bits_ok a_2_a with ⟨_, h, _⟩, cases bitvec.reify_eq h },
  { cases e, rcases split_bits_ok a_2_a with ⟨_, _, h, _⟩, cases bitvec.reify_eq h },
  { injection e, cases bitvec.reify_eq' h_1 },
  { injection e, cases bitvec.reify_eq' h_1 },
  { cases e, rcases split_bits_ok a_2_a with ⟨_, _, h, _⟩, cases bitvec.reify_eq h },
  { cases e, rcases split_bits_ok a_2_a with ⟨_, _, h, _⟩, cases bitvec.reify_eq h },
  { cases e, rcases split_bits_ok a_2_a with ⟨_, h, _⟩, cases bitvec.reify_eq h },
  { cases e, rcases split_bits_ok a_2_a with ⟨_, h, _⟩, cases bitvec.reify_eq h },
  { cases e, rcases split_bits_ok a_2_a with ⟨_, h, _⟩, cases bitvec.reify_eq h },
  { cases e, rcases split_bits_ok a_2_a with ⟨_, _, h, _⟩, cases bitvec.reify_eq h },
  { cases e, rcases split_bits_ok a_2_a with ⟨_, h, _⟩, cases bitvec.reify_eq h },
  { cases e, rcases split_bits_ok a_2_a with ⟨_, h, _⟩, cases bitvec.reify_eq h },
  { injection e, cases bitvec.reify_eq' h_1 },
  { cases e, rcases split_bits_ok a_2_a with ⟨_, _, h, _⟩, cases bitvec.reify_eq h },
  { cases e, rcases split_bits_ok a_2_a with ⟨_, h, _⟩, cases bitvec.reify_eq h },
  { injection e, cases bitvec.reify_eq' h_1 },
  { cases e, rcases split_bits_ok a_2_a with ⟨_, h, _⟩, cases bitvec.reify_eq h },
  { injection e, cases bitvec.reify_eq' h_1 },
  { injection e, cases bitvec.reify_eq' h_1 },
  { cases e, rcases split_bits_ok a_2_a with ⟨_, h, _⟩, cases bitvec.reify_eq h },
  { cases e, rcases split_bits_ok a_2_a with ⟨_, h, _⟩, cases bitvec.reify_eq h },
  { injection e, cases bitvec.reify_eq' h_1 },
  { injection e, cases bitvec.reify_eq' h_1 },
  { injection e, cases bitvec.reify_eq' h_1 },
  { cases e, rcases split_bits_ok a_2_a_1 with ⟨_, _, _, h, _⟩, cases bitvec.reify_eq h },
end

theorem decode_aux.determ {rex a₁ a₂ l} : decode_aux rex a₁ l → decode_aux rex a₂ l → a₁ = a₂ :=
sorry

theorem decode.determ : ∀ {a₁ a₂ l}, decode a₁ l → decode a₂ l → a₁ = a₂ :=
suffices ∀ {a₁ a₂ : ast}
  {rex1 rex2 : REX} {l11 l21 l12 l22 : list byte},
  (∃ (r : list byte), l12 = l11 ++ r ∧ l21 = r ++ l22) →
  read_prefixes rex1 l11 →
  decode_aux rex1 a₁ l21 →
  read_prefixes rex2 l12 →
  decode_aux rex2 a₂ l22 → a₁ = a₂,
{ intros a₁ a₂ l h₁ h₂, cases h₁, generalize_hyp e : h₁_l1.append h₁_l2 = x at h₂,
  cases h₂,
  cases list.append_eq_append_iff.1 e,
  exact this h h₁_a_1 h₁_a_2 h₂_a_1 h₂_a_2,
  exact (this h h₂_a_1 h₂_a_2 h₁_a_1 h₁_a_2).symm },
begin
  rintro _ _ _ _ _ _ _ _ ⟨_|⟨b, r⟩, rfl, rfl⟩ p1 aux1 p2 aux2,
  { simp at p2 aux1,
    cases read_prefixes.determ p1 p2,
    exact decode_aux.determ aux1 aux2 },
  { cases decode.no_prefix p2 (list.mem_append_right _ (or.inl rfl)) aux1 }
end

end x86