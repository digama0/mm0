import data.int.basic data.nat.prime data.set.finite .set6

namespace mm
local notation x ` ≡ ` y := eq (↑x : «class») ↑y
local notation x ` ∈' `:50 y:50 := (x : «class») ∈ (y : «class»)

theorem welc' {x : setvar} {A : «class»} :
  x ∈' A ↔ @has_mem.mem Set (set Set) _ x A :=
Class.mem_hom_left _ _


class rel_class (A : «class») (α : out_param Type) :=
(aset : A ∈ V_)
(«to» : α → «class»)
(to_mem {} : ∀ a, «to» a ∈ A)
(to_inj {} : function.injective «to»)
(to_surj {} : ∀ x, x ∈ A → ∃ a, x = «to» a)
open rel_class
local notation `to` := «to»

theorem to_V {A α} [rel_class A α] (a) : to A a ∈ V_ := elexi (to_mem _)

theorem to_inj_iff (A) {α} [rel_class A α] {a b} : to A a = to A b ↔ a = b :=
⟨@to_inj _ _ _ _ _, congr_arg _⟩

theorem to_mem_iff (A) {α} [rel_class A α] {x} : x ∈ A ↔ ∃ a, x = to A a :=
⟨to_surj _, by rintro ⟨a, rfl⟩; exact to_mem _⟩

@[elab_as_eliminator]
theorem to_ind (A) {α} [rel_class A α] (P : «class» → Prop)
  (H : ∀ a, P (to A a)) : ∀ x, x ∈ A → P x :=
λ x hx, let ⟨a, e⟩ := to_surj x hx in e.symm ▸ H _

theorem to_ind_ral (A) {α} [rel_class A α] (P : setvar → wff)
  (H : ∀ a x, ↑x = to A a → P x) : wral P (λ _, A) :=
λ x hx, let ⟨a, e⟩ := to_surj x hx in H a _ e

theorem ral_iff (A) {α} [rel_class A α] (P : «class» → Prop) :
  wral (λ x, P (cv x)) (λ _, A) ↔ ∀ a, P (to A a) :=
⟨λ H a, let ⟨x, e, hx⟩ := @to_mem A _ _ a in e ▸ H _ (welc'.2 hx),
 λ H, to_ind_ral _ _ (λ a x e, by rw [cv, e]; exact H _)⟩

theorem rex_iff (A) {α} [rel_class A α] (P : «class» → Prop) :
  wrex (λ x, P x) (λ _, A) ↔ ∃ a, P (to A a) :=
by classical; exact
dfrex2.trans ((notbii (ral_iff A (λ x, ¬ P x))).trans not_forall_not)

def rel (A) {α} [rel_class A α] (x) (a : α) : Prop :=
x ∈ A ∧ to A a = x

instance prod.rel_class (A B) {α β} [rel_class A α] [rel_class B β] :
  rel_class (cxp A B) (α × β) :=
{ aset := xpex aset aset,
  «to» := λ p, cop (to A p.1) (to B p.2),
  to_mem := λ ⟨a, b⟩, opelxp.2 ⟨to_mem _, to_mem _⟩,
  to_inj := λ ⟨a, b⟩ ⟨c, d⟩ e, prod.mk.inj_iff.2
    (((opth (to_V _) (to_V _)).1 e).imp (λ h, to_inj h) (λ h, to_inj h)),
  to_surj := λ p h, begin
    rcases elxp.1 h with ⟨a, b, e, ha, hb⟩,
    cases to_surj _ ha with x hx,
    cases to_surj _ hb with y hy,
    refine ⟨⟨x, y⟩, e.trans _⟩, rw [hx, hy]
  end }

@[simp] theorem to_xp_eq (A B) {α β} [rel_class A α] [rel_class B β]
  (a b) : to (cxp A B) (a, b) = cop (to A a) (to B b) := rfl

def to_ab (A) {α} [rel_class A α] (P : α → Prop) : «class» :=
crab (λ x, ∃ a, ↑x = to A a ∧ P a) (λ _, A)

theorem to_ab_ss (A) {α} [rel_class A α] (P : α → Prop) :
  to_ab A P ⊆ A := ssrab2

theorem mem_to_ab (A) {α} [rel_class A α] (P : α → Prop) {x} :
  x ∈ to_ab A P ↔ ∃ a, x = to A a ∧ P a :=
⟨λ ⟨y, e, hy, h⟩, e ▸ h, λ ⟨a, e, h⟩,
  let ⟨y, e', _⟩ := @to_mem A _ _ a in
  ⟨y, e'.trans e.symm, e'.symm ▸ to_mem a, a, e', h⟩⟩

theorem to_mem_to_ab (A) {α} [rel_class A α] (P : α → Prop) {a} :
  to A a ∈ to_ab A P ↔ P a :=
(mem_to_ab _ _).trans ⟨λ ⟨a, e, h⟩, to_inj e.symm ▸ h, λ h, ⟨_, rfl, h⟩⟩

def to_opab (A B) {α β} [rel_class A α] [rel_class B β]
  (P : α → β → Prop) : «class» :=
to_ab (cxp A B) (λ p, P p.1 p.2)

theorem to_opab_ss (A B) {α β} [rel_class A α] [rel_class B β]
  (P : α → β → Prop) : to_opab A B P ⊆ cxp A B := to_ab_ss _ _

theorem to_opab_rel (A B) {α β} [rel_class A α] [rel_class B β]
  (P : α → β → Prop) : wrel (to_opab A B P) :=
relss (to_opab_ss _ _ _) relxp

theorem mem_to_opab (A B) {α β} [rel_class A α] [rel_class B β]
  (P : α → β → Prop) {x} :
  x ∈ to_opab A B P ↔ ∃ a b, x = cop (to A a) (to B b) ∧ P a b :=
(mem_to_ab _ _).trans $ by simp [eq_comm]

theorem to_br_to_opab (A B) {α β} [rel_class A α] [rel_class B β]
  (P : α → β → Prop) {a b} :
  wbr (to A a) (to B b) (to_opab A B P) ↔ P a b :=
@to_mem_to_ab (cxp A B) _ _ _ (a, b)

def to_mpt (A B) {α β} [rel_class A α] [rel_class B β] (f : α → β) : «class» :=
to_opab A B (λ a b, f a = b)

theorem to_mpt_fn (A B) {α β} [rel_class A α] [rel_class B β]
  (f : α → β) : wfn (to_mpt A B f) A :=
begin
  refine ⟨dffun4.2 ⟨to_opab_rel _ _ _, _⟩,
    eqssi (sstri (dmss (to_opab_ss _ _ _)) dmxpss) _⟩,
  { rintro x y z ⟨h₁, h₂⟩,
    rcases (mem_to_opab _ _ _).1 h₁ with ⟨a, _, e₁, rfl⟩,
    rcases (mem_to_opab _ _ _).1 h₂ with ⟨b, _, e₂, rfl⟩,
    cases (opth (vex _) (vex _)).1 e₁ with l₁ r₁,
    cases (opth (vex _) (vex _)).1 e₂ with l₂ r₂,
    cases to_inj (l₁.symm.trans l₂),
    exact r₁.trans r₂.symm },
  { refine λ x h, welc'.1 $ to_ind A _ (λ a, _) x (welc'.2 h),
    rcases to_mem (f a) with ⟨b, e, h⟩,
    refine breldm (to_V _) (vex b) _,
    rw [cv, e], exact (to_br_to_opab _ _ _).2 rfl }
end

@[simp] theorem to_mpt_fv (A B) {α β} [rel_class A α] [rel_class B β]
  (f : α → β) (a) : cfv (to A a) (to_mpt A B f) = to B (f a) :=
(fnbrfvb ⟨to_mpt_fn _ _ _, to_mem _⟩).2 $ (to_br_to_opab _ _ _).2 rfl

theorem to_mpt_f (A B) {α β} [rel_class A α] [rel_class B β]
  (f : α → β) : wf A B (to_mpt A B f) :=
ffnfv.2 ⟨to_mpt_fn _ _ _, to_ind_ral A _ $ λ a x e,
  by rw [cv, e, to_mpt_fv A B f a]; apply to_mem⟩

def carrow (A B) := co B A cmap
local infix ` c→ `:25 := carrow
def map.rel_class (A B) {α β} [rel_class A α] [rel_class B β] :
  rel_class (A c→ B) (α → β) :=
{ aset := ovex,
  «to» := to_mpt A B,
  to_mem := λ f, (elmap aset aset).2 (to_mpt_f _ _ f),
  to_inj := λ f g e, funext $ λ a, begin
    have := to_mpt_fv A B g a,
    rw [← e, to_mpt_fv A B f a] at this,
    exact to_inj this
  end,
  to_surj := λ p hp, begin
    have fp := (elmap aset aset).1 hp,
    have := λ a, to_surj (cfv (to A a) p) (ffvelrni fp (to_mem a)),
    choose f hf using this, use f,
    refine (eqfnfv ⟨ffn fp, to_mpt_fn _ _ _⟩).2 (to_ind_ral _ _ _),
    intros a x e, rw [cv, e, to_mpt_fv A B f a], apply hf
  end }

instance : has_zero «class» := ⟨cc0⟩
instance : has_one «class» := ⟨c1⟩
instance : has_add «class» := ⟨λ x y, co x y caddc⟩
instance : has_mul «class» := ⟨λ x y, co x y cmul⟩
instance : has_neg «class» := ⟨cneg⟩
instance : has_sub «class» := ⟨λ x y, co x y cmin⟩
instance : has_div «class» := ⟨λ x y, co x y cdiv⟩
instance : has_dvd «class» := ⟨λ x y, wbr x y cdvds⟩
instance : has_lt «class» := ⟨λ x y, wbr x y clt⟩
instance : has_le «class» := ⟨λ x y, wbr x y cle⟩
instance : has_equiv «class» := ⟨λ x y, wbr x y cen⟩

@[simp] theorem c0_eq : cc0 = 0 := rfl
@[simp] theorem c1_eq : c1 = 1 := rfl
@[simp] theorem add_eq (x y) : co x y caddc = x + y := rfl
@[simp] theorem mul_eq (x y) : co x y cmul = x * y := rfl
@[simp] theorem neg_eq (x) : cneg x = -x := rfl
@[simp] theorem sub_eq (x y) : co x y cmin = x - y := rfl
@[simp] theorem div_eq (x y) : co x y cdiv = x / y := rfl
@[simp] theorem dvd_eq (x y) : wbr x y cdvds = (x ∣ y) := rfl
@[simp] theorem lt_eq (x y) : wbr x y clt = (x < y) := rfl
@[simp] theorem le_eq (x y) : wbr x y cle = (x ≤ y) := rfl
@[simp] theorem en_eq (x y) : wbr x y cen = (x ≈ y) := rfl

local notation `cℕ₀` := cn0
local notation `cℤ` := cz
local notation `cℝ` := cr
local notation `cℂ` := cc

instance : has_coe_to_sort «class» (Type 1) := ⟨λ A, {x // x ∈ A}⟩

local prefix `↟`:max := @_root_.coe (@coe_sort «class» _ _ _) «class» _

def semiring_cn (A : «class») (ss : A ⊆ cℂ)
  («0cl» : (0 : «class») ∈ A) («1cl» : (1 : «class») ∈ A)
  (addcl : ∀ x y, x ∈ A → y ∈ A → x + y ∈ A)
  (mulcl : ∀ x y, x ∈ A → y ∈ A → x * y ∈ A) : comm_semiring A :=
have h : ∀ x : A, ↟x ∈ cℂ := λ x, sselii ss x.2,
{ add := λ x y, ⟨↟x + ↟y, addcl _ _ x.2 y.2⟩,
  add_assoc := λ x y z, subtype.eq (addassi (h x) (h y) (h z)),
  mul := λ x y, ⟨↟x * ↟y, mulcl _ _ x.2 y.2⟩,
  mul_assoc := λ x y z, subtype.eq (mulassi (h x) (h y) (h z)),
  zero := ⟨0, «0cl»⟩,
  zero_add := λ x, subtype.eq (addid2 (h x)),
  add_zero := λ x, subtype.eq (addid1 (h x)),
  add_comm := λ x y, subtype.eq (addcomi (h x) (h y)),
  mul := λ x y, ⟨↟x * ↟y, mulcl _ _ x.2 y.2⟩,
  mul_assoc := λ x y z, subtype.eq (mulassi (h x) (h y) (h z)),
  one := ⟨1, «1cl»⟩,
  one_mul := λ x, subtype.eq (mulid2 (h x)),
  mul_one := λ x, subtype.eq (mulid1 (h x)),
  mul_comm := λ x y, subtype.eq (mulcomi (h x) (h y)),
  left_distrib := λ x y z, subtype.eq (adddii (h x) (h y) (h z)),
  right_distrib := λ x y z, subtype.eq (adddiri (h x) (h y) (h z)),
  zero_mul := λ x, subtype.eq (mul02 (h x)),
  mul_zero := λ x, subtype.eq (mul01 (h x)) }

noncomputable def linear_order_xr (A : «class») (ss : A ⊆ cxr) : linear_order A :=
have h : ∀ x:A, ↟x ∈ cxr := λ x, sselii ss x.2,
{ le := λ x y, ↟x ≤ ↟y,
  lt := λ x y, ↟x < ↟y,
  le_refl := λ x, xrleid (h x),
  le_trans := λ x y z h1 h2, xrletr ⟨h x, h y, h z⟩ ⟨h1, h2⟩,
  le_antisymm := λ x y h1 h2, subtype.eq ((xrletri3 ⟨h x, h y⟩).2 ⟨h1, h2⟩),
  le_total := λ x y, xrletri ⟨h x, h y⟩,
  lt_iff_le_not_le := λ x y, ⟨
    λ h1, ⟨xrltle ⟨h x, h y⟩ h1, (xrltnle ⟨h x, h y⟩).1 h1⟩,
    λ ⟨h1, h2⟩, (xrltnle ⟨h x, h y⟩).2 h2⟩,
  decidable_le := classical.dec_rel _ }

noncomputable def ordered_semiring_re (A : «class») (ss : A ⊆ cℝ)
  («0cl» : (0 : «class») ∈ A) («1cl» : (1 : «class») ∈ A)
  (addcl : ∀ x y, x ∈ A → y ∈ A → x + y ∈ A)
  (mulcl : ∀ x y, x ∈ A → y ∈ A → x * y ∈ A) :
  linear_ordered_semiring A :=
have h : ∀ x:A, ↟x ∈ cℝ := λ x, sselii ss x.2,
{
  -- add_left_cancel := λ x y z e, subtype.eq
  --   ((readdcan ⟨h y, h z, h x⟩).1 (subtype.ext.1 e)),
  -- add_right_cancel := λ x y z e, subtype.eq
  --   ((addcan2 ⟨recn (h x), recn (h z), recn (h y)⟩).1
  --     (subtype.ext.1 e)),
  add_le_add_left := λ x y h1 z, (leadd2 ⟨h x, h y, h z⟩).1 h1,
  le_of_add_le_add_left := λ x y z h1, (leadd2 ⟨h y, h z, h x⟩).2 h1,
  -- mul_le_mul_of_nonneg_left := λ x y z h1 h2, lemul2a ⟨⟨h x, h y, h z, h2⟩, h1⟩,
  -- mul_le_mul_of_nonneg_right := λ x y z h1 h2, lemul1a ⟨⟨h x, h y, h z, h2⟩, h1⟩,
  mul_lt_mul_of_pos_left := λ x y z h1 h2, (ltmul2 ⟨h x, h y, h z, h2⟩).1 h1,
  mul_lt_mul_of_pos_right := λ x y z h1 h2, (ltmul1 ⟨h x, h y, h z, h2⟩).1 h1,
  zero_le_one := «0le1»,
  exists_pair_ne := ⟨⟨_, «0cl»⟩, ⟨_, «1cl»⟩, mt subtype.coe_inj.2 «0ne1»⟩,
  decidable_le := by classical; apply_instance,
  ..linear_order_xr _ (sstri ss ressxr),
  ..semiring_cn _ (sstri ss ax_resscn) «0cl» «1cl» addcl mulcl }

def ring_cn (A : «class») (ss : A ⊆ cℂ)
  («0cl» : (0 : «class») ∈ A) («1cl» : (1 : «class») ∈ A)
  (addcl : ∀ x y, x ∈ A → y ∈ A → x + y ∈ A)
  (negcl : ∀ x, x ∈ A → -x ∈ A)
  (mulcl : ∀ x y, x ∈ A → y ∈ A → x * y ∈ A) : comm_ring A :=
have h : ∀ x : A, ↟x ∈ cℂ := λ x, sselii ss x.2,
{ neg := λ x, ⟨-↟x, negcl _ x.2⟩,
  add_left_neg := λ x, subtype.eq $
    (addcomi (mm.negcl (h x)) (h x)).trans (negid (h x)),
  ..semiring_cn _ ss «0cl» «1cl» addcl mulcl }

noncomputable def ordered_ring_re (A : «class») (ss : A ⊆ cℝ)
  («0cl» : (0 : «class») ∈ A) («1cl» : (1 : «class») ∈ A)
  (addcl : ∀ x y, x ∈ A → y ∈ A → x + y ∈ A)
  (negcl : ∀ x, x ∈ A → -x ∈ A)
  (mulcl : ∀ x y, x ∈ A → y ∈ A → x * y ∈ A) :
  linear_ordered_comm_ring A :=
have h : ∀ x : A, ↟x ∈ cℝ := λ x, sselii ss x.2,
{ mul_pos := λ x y h1 h2, mulgt0 ⟨⟨h x, h1⟩, ⟨h y, h2⟩⟩,
  ..ring_cn _ (sstri ss ax_resscn) «0cl» «1cl» addcl negcl mulcl,
  ..ordered_semiring_re _ ss «0cl» «1cl» addcl mulcl }

noncomputable def field_cn (A : «class») (ss : A ⊆ cℂ)
  («0cl» : (0 : «class») ∈ A) («1cl» : (1 : «class») ∈ A)
  (addcl : ∀ x y, x ∈ A → y ∈ A → x + y ∈ A)
  (negcl : ∀ x, x ∈ A → -x ∈ A)
  (mulcl : ∀ x y, x ∈ A → y ∈ A → x * y ∈ A)
  (reccl : ∀ x:«class», x ∈ A → x ≠ 0 → 1 / x ∈ A) : field A :=
begin
  classical,
  letI := ring_cn _ ss «0cl» «1cl» addcl negcl mulcl,
  have h : ∀ {{x}}, x ∈ A → x ∈ cℂ := λ x, sselii ss,
  let inv := λ x : A,
    if h : ↟x = 0 then (0:A) else ⟨1 / ↟x, reccl _ x.2 h⟩,
  have n0 : ∀ {x:A}, x ≠ 0 → (x:«class») ≠ 0 := λ x h, (mt subtype.eq h:_),
  have inveq : ∀ {x:A}, x ≠ 0 → ↟(inv x) = 1 / ↟x :=
    λ x h, by simp [inv, n0 h],
  exact
  { inv := inv,
    mul_inv_cancel := λ x x0, subtype.eq (show ↟x * ↟(inv x) = 1,
      by rw [inveq x0]; exact recid ⟨h x.2, n0 x0⟩),
    exists_pair_ne := ⟨⟨_, «0cl»⟩, ⟨_, «1cl»⟩, mt subtype.coe_inj.2 «0ne1»⟩,
    inv_zero := dif_pos rfl,
    ..‹comm_ring A› }
end

noncomputable def ordered_field_re (A : «class») (ss : A ⊆ cℝ)
  («0cl» : (0 : «class») ∈ A) («1cl» : (1 : «class») ∈ A)
  (addcl : ∀ x y, x ∈ A → y ∈ A → x + y ∈ A)
  (negcl : ∀ x, x ∈ A → -x ∈ A)
  (mulcl : ∀ x y, x ∈ A → y ∈ A → x * y ∈ A)
  (reccl : ∀ x:«class», x ∈ A → x ≠ 0 → 1 / x ∈ A) :
  linear_ordered_field A :=
{ ..field_cn _ (sstri ss ax_resscn) «0cl» «1cl» addcl negcl mulcl reccl,
  ..ordered_ring_re _ ss «0cl» «1cl» addcl negcl mulcl }

noncomputable instance nn0.ordered_semiring : linear_ordered_semiring cℕ₀ :=
ordered_semiring_re _ nn0ssre «0nn0» «1nn0» (λ x y, nn0addcli) (λ x y, nn0mulcli)

@[simp] theorem cn0_zero : ↟(0 : cℕ₀) = 0 := rfl
@[simp] theorem cn0_one : ↟(1 : cℕ₀) = 1 := rfl
@[simp] theorem cn0_add (x y : cℕ₀) : ↟(x + y) = ↟x + ↟y := rfl
@[simp] theorem cn0_mul (x y : cℕ₀) : ↟(x * y) = ↟x * ↟y := rfl
@[simp] theorem cn0_le {x y : cℕ₀} : ↟x ≤ ↟y ↔ x ≤ y := iff.rfl
@[simp] theorem cn0_lt {x y : cℕ₀} : ↟x < ↟y ↔ x < y := iff.rfl

noncomputable instance z.ordered_ring : linear_ordered_comm_ring cℤ :=
ordered_ring_re _ zssre «0z» «1z»
  (λ x y h1 h2, zaddcl ⟨h1, h2⟩) (λ x, znegcl)
  (λ x y h1 h2, zmulcl ⟨h1, h2⟩)

@[simp] theorem cz_zero : ↟(0 : cℤ) = 0 := rfl
@[simp] theorem cz_one : ↟(1 : cℤ) = 1 := rfl
@[simp] theorem cz_add (x y : cℤ) : ↟(x + y) = ↟x + ↟y := rfl
@[simp] theorem cz_neg (x : cℤ) : ↟(-x) = -↟x := rfl
@[simp] theorem cz_sub (x y : cℤ) : ↟(x - y) = ↟x - ↟y := negsub ⟨zcn x.2, zcn y.2⟩
@[simp] theorem cz_mul (x y : cℤ) : ↟(x * y) = ↟x * ↟y := rfl
@[simp] theorem cz_le {x y : cℤ} : ↟x ≤ ↟y ↔ x ≤ y := iff.rfl
@[simp] theorem cz_lt {x y : cℤ} : ↟x < ↟y ↔ x < y := iff.rfl

noncomputable instance re.ordered_field : linear_ordered_field cℝ :=
ordered_field_re _ ssid «0re» «1re»
  (λ x y, readdcli) (λ x, renegcl)
  (λ x y, remulcli) (λ x, rereccli)

@[simp] theorem cr_zero : ↟(0 : cℝ) = 0 := rfl
@[simp] theorem cr_one : ↟(1 : cℝ) = 1 := rfl
@[simp] theorem cr_add (x y : cℝ) : ↟(x + y) = ↟x + ↟y := rfl
@[simp] theorem cr_neg (x : cℝ) : ↟(-x) = -↟x := rfl
@[simp] theorem cr_sub (x y : cℝ) : ↟(x - y) = ↟x - ↟y := negsub ⟨recn x.2, recn y.2⟩
@[simp] theorem cr_mul (x y : cℝ) : ↟(x * y) = ↟x * ↟y := rfl
@[simp] theorem cr_le {x y : cℝ} : ↟x ≤ ↟y ↔ x ≤ y := iff.rfl
@[simp] theorem cr_lt {x y : cℝ} : ↟x < ↟y ↔ x < y := iff.rfl

noncomputable instance cn.field : field cℂ :=
field_cn _ ssid «0cn» «ax_1cn»
  (λ x y, addcli) (λ x, negcl)
  (λ x y, mulcli) (λ x, reccli)

@[simp] theorem cc_zero : ↟(0 : cℂ) = 0 := rfl
@[simp] theorem cc_one : ↟(1 : cℂ) = 1 := rfl
@[simp] theorem cc_add (x y : cℂ) : ↟(x + y) = ↟x + ↟y := rfl
@[simp] theorem cc_neg (x : cℂ) : ↟(-x) = -↟x := rfl
@[simp] theorem cc_sub (x y : cℂ) : ↟(x - y) = ↟x - ↟y := negsub ⟨x.2, y.2⟩
@[simp] theorem cc_mul (x y : cℂ) : ↟(x * y) = ↟x * ↟y := rfl

theorem wb_congr (P : «class» → Prop) {x:setvar} {A : «class»} :
  ↑x = A → (P x ↔ P A) := λ h, by rw h

@[elab_as_eliminator]
theorem nn0ind' (P : «class» → Prop) {n} (h : n ∈ cℕ₀)
  (H0 : P 0) (H1 : ∀ x ∈ cℕ₀, P x → P (x + 1)) : P n :=
@nn0ind _ _ _ _ _ (λ _, n)
  (λ _ _, wb_congr P) (λ _ _, wb_congr P)
  (λ _ _, wb_congr P) (λ _ _, wb_congr P) (λ _, H0) (λ x, H1 _) ∅ h

instance nn0.rel_class : rel_class cℕ₀ ℕ :=
{ aset := nn0ex,
  «to» := λ n, ↟(n:cℕ₀),
  to_mem := λ n, (n:cℕ₀).2,
  to_inj := λ m n e, nat.cast_inj.1 (subtype.eq e),
  to_surj := λ x h, begin
    refine nn0ind' _ h ⟨0, rfl⟩ _,
    rintro _ h ⟨n, rfl⟩, exact ⟨n+1, rfl⟩
  end }

@[simp] theorem to_cn0_val (x : ℕ) : to cℕ₀ x = (x : cℕ₀).1 := rfl
theorem to_cn0_mem {x : «class»} : x ∈ cℕ₀ ↔ ∃ n:ℕ, x = (n : cℕ₀).1 :=
to_mem_iff cℕ₀

@[simp] theorem to_cn0_zero : ↟((0 : ℕ) : cℕ₀) = 0 := rfl
@[simp] theorem to_cn0_one : ↟((1 : ℕ) : cℕ₀) = 1 := by simp
@[simp] theorem to_cn0_add (x y : ℕ) : ↟((x + y:ℕ):cℕ₀) = ↟(x:cℕ₀) + ↟(y:cℕ₀) := by simp
@[simp] theorem to_cn0_mul (x y : ℕ) : ↟((x * y:ℕ):cℕ₀) = ↟(x:cℕ₀) * ↟(y:cℕ₀) := by simp
@[simp] theorem to_cn0_le {x y : ℕ} : ↟(x:cℕ₀) ≤ ↟(y:cℕ₀) ↔ x ≤ y := by simp
@[simp] theorem to_cn0_lt {x y : ℕ} : ↟(x:cℕ₀) < ↟(y:cℕ₀) ↔ x < y := by simp
theorem to_cn0_two : ↟((2 : ℕ) : cℕ₀) = c2 := oveq1 to_cn0_one

@[simp] theorem to_cn0_eq {x y : ℕ} : ↟(x:cℕ₀) = ↟(y:cℕ₀) ↔ x = y :=
to_inj_iff cℕ₀

@[simp] theorem nat_cast_cz : ∀ n : ℕ, ↟(n : cℤ) = ↟(n : cℕ₀)
| 0     := rfl
| (n+1) := oveq1 (nat_cast_cz n)

@[simp] theorem nat_cast_cz' (n : ℕ) : ↟((n : ℤ) : cℤ) = ↟(n : cℕ₀) :=
nat_cast_cz _

instance z.rel_class : rel_class cℤ ℤ :=
{ aset := zex,
  «to» := λ n, ↟(n:cℤ),
  to_mem := λ n, (n:cℤ).2,
  to_inj := λ m n e, int.cast_inj.1 (subtype.eq e),
  to_surj := λ x h, begin
    rcases elznn0.1 h with ⟨xre, h | h⟩,
    { cases to_surj _ h with n e, refine ⟨n, _⟩,
      exact e.trans (nat_cast_cz' n).symm },
    { cases to_surj _ h with n e, use -n,
      rw [int.cast_neg n], show x = -↟((n:ℤ):cℤ),
      rw nat_cast_cz',
      exact (negneg (recn xre)).symm.trans (negeq e) }
  end }

@[simp] theorem to_cz_val (x : ℤ) : to cℤ x = ↟(x : cℤ) := rfl
theorem to_cz_mem {x : «class»} : x ∈ cℤ ↔ ∃ n:ℤ, x = ↟(n : cℤ) := to_mem_iff cℤ
@[simp] theorem to_cz_eq {x y : ℤ} : ↟(x:cℤ) = ↟(y:cℤ) ↔ x = y := to_inj_iff cℤ

@[simp] theorem to_cz_zero : ↟((0 : ℤ) : cℤ) = 0 := rfl
@[simp] theorem to_cz_one : ↟((1 : ℤ) : cℤ) = 1 := by simp
@[simp] theorem to_cz_add (x y : ℤ) : ↟((x + y:ℤ):cℤ) = ↟(x:cℤ) + ↟(y:cℤ) := by simp
@[simp] theorem to_cz_neg (x : ℤ) : ↟((-x:ℤ):cℤ) = -↟(x:cℤ) := by simp
@[simp] theorem to_cz_sub (x y : ℤ) : ↟((x - y:ℤ):cℤ) = ↟(x:cℤ) - ↟(y:cℤ) := by rw [int.cast_sub, cz_sub]
@[simp] theorem to_cz_mul (x y : ℤ) : ↟((x * y:ℤ):cℤ) = ↟(x:cℤ) * ↟(y:cℤ) := by simp
@[simp] theorem to_cz_le {x y : ℤ} : ↟(x:cℤ) ≤ ↟(y:cℤ) ↔ x ≤ y := by simp
@[simp] theorem to_cz_lt {x y : ℤ} : ↟(x:cℤ) < ↟(y:cℤ) ↔ x < y := by simp
theorem to_cz_two : ↟((2 : ℤ) : cℤ) = c2 := oveq1 to_cz_one

@[simp] theorem to_cz_dvd {x y : ℤ} : ↟(x:cℤ) ∣ ↟(y:cℤ) ↔ x ∣ y :=
(divides ⟨(x:cℤ).2, (y:cℤ).2⟩).trans $
(rex_iff cℤ (λ z, z * ↟(x:cℤ) = ↟(y:cℤ))).trans $
exists_congr $ λ z,
by rw [← to_inj_iff cℤ, eq_comm, mul_comm]; simp

@[simp] theorem to_cn0_dvd {x y : ℕ} : ↟(x:cℕ₀) ∣ ↟(y:cℕ₀) ↔ x ∣ y :=
by rw [← int.coe_nat_dvd, ← to_cz_dvd, nat_cast_cz', nat_cast_cz']

def cz_gcd (a b : cℤ) : cℕ₀ := ⟨co a b cgcd, gcdcl ⟨a.2, b.2⟩⟩

theorem cz_gcd_eq (a b : ℤ) : cz_gcd a b = int.gcd a b :=
begin
  refine subtype.eq (dvdseq ⟨⟨(_:cℕ₀).2, (_:cℕ₀).2⟩,
    ⟨_, _⟩⟩),
  { cases @to_surj cℕ₀ _ _ _ (cz_gcd a b).2 with x hx,
    replace hx := subtype.eq hx, rw hx,
    cases gcddvds ⟨(a:cℤ).2, (b:cℤ).2⟩ with h1 h2,
    refine to_cn0_dvd.2 (nat.dvd_gcd _ _);
      rw [← int.coe_nat_dvd, int.dvd_nat_abs, ← to_cz_dvd,
        nat_cast_cz', ← hx],
    exacts [h1, h2] },
  { dsimp, rw ← nat_cast_cz',
    refine dvdsgcd ⟨(_:cℤ).2, (_:cℤ).2, (_:cℤ).2⟩ ⟨_, _⟩;
      refine (@to_cz_dvd (int.gcd a b) _).2
        (int.dvd_nat_abs.1 (int.coe_nat_dvd.2 _));
      [apply nat.gcd_dvd_left, apply nat.gcd_dvd_right] }
end

theorem mem_cn {n : ℕ} : ↟(n:cℕ₀) ∈ cn ↔ n ≠ 0 :=
(baib (elnnne0) (_:cℕ₀).2).trans $ not_congr $ @to_inj_iff cℕ₀ _ _ n 0

theorem mem_cprime {p : ℕ} : ↟(p:cℕ₀) ∈ cprime ↔ nat.prime p :=
begin
  have ge2 : ↟(p:cℕ₀) ∈ cfv c2 cuz ↔ 2 ≤ p,
  { refine (eluz ⟨«2z», nn0z (_:cℕ₀).2⟩).trans _,
    rw ← to_cn0_two, exact @nat.cast_le cℕ₀ _ _ 2 p },
  refine iff.trans ⟨λ h, _, λ h, _⟩ nat.prime_def_lt''.symm,
  { refine ⟨ge2.1 (prmuz2 h), λ m hm, _⟩,
    cases (dvdsprime ⟨h, mem_cn.2 _⟩).1 (to_cn0_dvd.2 hm) with e e,
    { exact or.inr (to_cn0_eq.1 e) },
    { rw [c1_eq, ← cn0_one, ← nat.cast_one] at e,
      exact or.inl (to_cn0_eq.1 e) },
    { rintro rfl, cases zero_dvd_iff.1 hm,
      exact «0nnn» (prmnn h) } },
  { refine isprm2.2 ⟨ge2.2 h.1, λ z hz, _⟩,
    cases to_cn0_mem.1 (nnnn0 hz) with m hm, simp [hm],
    rw [← to_cn0_one, to_cn0_eq],
    exact h.2 _ }
end

theorem is_finite (A) {α} [rel_class A α] (s : set α) :
  set.finite s ↔ to_ab A (λ a, a ∈ s) ∈ cfn :=
begin
  have ab0 : to_ab A (λ (a : α), a ∈ (∅ : set α)) = ∅,
  { apply eq0.2, rintro x ⟨_, _, _, _, _, ⟨⟩⟩ },
  have absuc : ∀ (a : α) (s : set α),
    to_ab A (λ (a_1 : α), a_1 ∈ insert a s) =
    to_ab A (λ (a : α), a ∈ s) ∪ csn (to A a),
  { refine λ a s, eqriv (λ x, _),
    refine pm5_21nii (sseli (to_ab_ss _ _))
      (sseli (unssi (to_ab_ss _ _) (snssi (to_mem _)))) (λ h, _),
    rcases to_surj _ h with ⟨b, e⟩, rw [e], simp [to_mem_to_ab],
    exact (elun.trans (or.comm.trans $ or_congr
      ((elsn (to_V _)).trans (to_inj_iff _))
      (to_mem_to_ab _ _))).symm },
  split,
  { refine λ h, set.finite.induction_on h _ (λ a s hn h IH, _),
    { rw ab0, exact «0fin» },
    { rw absuc, exact unfi ⟨IH, snfi⟩ } },
  { let P := λ x, x ⊆ A → ∃ s:set α,
      set.finite s ∧ to_ab A (λ (a : α), a ∈ s) = x,
    have := @findcard2 _ _ _ _ _ (λ _ _, to_ab A (λ (a : α), a ∈ s))
      (λ _ _ _, wb_congr P) (λ _ _ _, wb_congr P)
      (λ _ _ _, wb_congr P) (λ _ _ _, wb_congr P)
      (λ _ _ _, (_ : P ∅)) (λ x y _ IH, _) ∅ ∅,
    { intro h,
      rcases this h (to_ab_ss A (λ (a : α), a ∈ s)) with ⟨t, tf, e⟩,
      have : t = s := set.ext (λ a,
        (to_mem_to_ab A _).symm.trans ((eleq2 e).trans (to_mem_to_ab A _))),
      exact this ▸ tf },
    { refine λ _, ⟨∅, set.finite_empty, ab0⟩ },
    { intro h, cases unss.2 h with h1 h2,
      rcases IH h1 with ⟨s, sf, e⟩,
      cases to_surj _ ((snss (vex _)).2 h2) with a e',
      rw [e.symm, e'],
      exact ⟨_, set.finite.insert a sf, absuc _ _⟩ } }
end

theorem dirith_aux₁ {n a : «class»} :
  n ∈ cn ∧ a ∈ cℤ ∧ co a n cgcd = 1 →
  cab (λ x, ↑x ∈ cprime ∧ n ∣ x - a) ≈ cn :=
dirith

theorem dirith_aux₂ {n : ℕ} {a : ℤ} (n0 : n ≠ 0) (h : int.gcd a n = 1) :
  to_ab cℕ₀ (λ x, nat.prime x ∧ ↑n ∣ ↑x - a) ≈ cn :=
begin
  refine eqbrtri (eqriv $ λ x, _) (dirith_aux₁ ⟨mem_cn.2 n0, (a:cℤ).2, _⟩),
  { refine (mem_to_ab _ _).trans (iff.trans _ (abid _).symm),
    dsimp, split,
    { rintro ⟨n, e, h₁, h₂⟩, simp [e],
      refine ⟨mem_cprime.2 h₁, _⟩,
      rwa [← nat_cast_cz', ← nat_cast_cz', ← to_cz_sub, to_cz_dvd] },
    { rintro ⟨h₁, h₂⟩,
      cases to_cn0_mem.1 (nnnn0 (prmnn h₁)) with m hm,
      simp [hm] at h₁ h₂ ⊢,
      rw [← nat_cast_cz', ← nat_cast_cz', ← to_cz_sub, to_cz_dvd] at h₂,
      exact ⟨mem_cprime.1 h₁, h₂⟩ } },
  { rw [← nat_cast_cz'],
    refine congr_arg subtype.val (_ : cz_gcd a n = 1),
    rw [← int.cast_coe_nat, cz_gcd_eq, h, nat.cast_one] }
end

theorem dirith' {n : ℕ} {a : ℤ} (n0 : n ≠ 0) (g1 : int.gcd a n = 1) :
  ¬ set.finite {x | nat.prime x ∧ ↑n ∣ ↑x - a} :=
λ h, ominf $ (enfi nnenom).1 $
  (enfi (dirith_aux₂ n0 g1)).1 $ (is_finite cℕ₀ _).1 h

end mm
