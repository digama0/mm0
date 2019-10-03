import zfc

def deps := list bool

def deps.single (n : ℕ) : deps :=
nat.rec ([tt]) (λ _, list.cons ff) n
-- | 0 := [tt]
-- | (n+1) := ff :: deps.single n

def deps.union (d1 : deps) : deps → deps :=
list.rec id (λ a l₁ IH l₂,
  list.cases_on l₂ l₁ (λ b l₂, (a || b) :: IH l₂)) d1
-- | [] l := l
-- | l [] := l
-- | (a :: l₁) (b :: l₂) := (a || b) :: deps.union l₁ l₂

def deps.contains (d : deps) : ℕ → bool :=
list.rec (λ _, ff) (λ a l₁ IH n, nat.cases_on n a IH) d

def deps.disjoint (d : deps) (l : list ℕ) : bool :=
l.all (λ n, bnot (d.contains n))

def deps.filter_out (d : deps) {α} : list α → list α :=
list.rec id (λ a d' IH l,
  list.cases_on l ([]) $ λ b l', cond a (IH l') (b :: IH l')) d

def deps.below (d : deps) (n : ℕ) : bool := d.length ≤ n

inductive mm0_sort | set | wff | Class

inductive {u} mm0_context : ℕ → Type
| empty : mm0_context 0
| lvar {n} : mm0_context n → mm0_context (n + 1)
| rvar {n} (d : deps) : mm0_sort → d.below n → mm0_context n → mm0_context n

def mm0_context.rsize : ∀ {n}, mm0_context n → ℕ
| _ mm0_context.empty := 0
| _ (mm0_context.lvar c) := c.rsize
| _ (mm0_context.rvar _ _ _ c) := c.rsize.succ

def mm0_context.sort_rev : ∀ {n} (c : mm0_context n), ℕ → option mm0_sort
| _ mm0_context.empty _ := none
| _ (mm0_context.lvar c) i := c.sort_rev i
| _ (mm0_context.rvar d s h c) 0 := some s
| _ (mm0_context.rvar d s h c) (i+1) := c.sort_rev i

def mm0_context.sort {n} (c : mm0_context n) (i : ℕ) : option mm0_sort :=
c.rsize.psub i.succ >>= c.sort_rev

def mm0_context.rvar_deps_rev : ∀ {n} (c : mm0_context n), ℕ → deps
| _ mm0_context.empty _ := ([])
| _ (mm0_context.lvar c) i := c.rvar_deps_rev i
| _ (mm0_context.rvar d s h c) 0 := d
| _ (mm0_context.rvar d s h c) (i+1) := c.rvar_deps_rev i

def mm0_context.rvar_deps {n} (c : mm0_context n) (i : ℕ) : deps :=
c.rvar_deps_rev (c.rsize - i.succ)

def mm0_value : mm0_sort → Type 1
| mm0_sort.set := ulift ℕ
| mm0_sort.wff := fol.formula zfc.L_ZFC
| mm0_sort.Class := fol.formula zfc.L_ZFC
local infix ` ∈' `:100 := fol.formula_of_relation zfc.ZFC_el

namespace fol

def move0 (k n : ℕ) : ℕ := if n = k then 0 else n + 1
def map_lift (f : ℕ → ℕ) (k n : ℕ) : ℕ := if n < k then n else f (n - k) + k

namespace preterm

def map_vars {L} (f : ℕ → ℕ) : ∀ {l}, preterm L l → preterm L l
| _ &k          := &(f k)
| _ (func f)    := func f
| _ (app t₁ t₂) := app (map_vars t₁) (map_vars t₂)

end preterm

def preterm.deps {L} : ∀ {n}, preterm L n → deps
| _ (preterm.var k) := deps.single k
| _ (preterm.func f) := ([])
| _ (preterm.app t s) := t.deps.union s.deps

def preformula.deps {L} : ∀ {n}, preformula L n → deps
| _ preformula.falsum := ([])
| _ (preformula.equal t₁ t₂) := t₁.deps.union t₂.deps
| _ (preformula.rel R) := ([])
| _ (preformula.apprel f t) := f.deps.union f.deps
| _ (preformula.imp f₁ f₂) := f₁.deps.union f₂.deps
| _ (preformula.all f) := f.deps.tail

namespace preformula

def map_vars {L} (f : ℕ → ℕ) : ∀ {l}, preformula L l → ℕ → preformula L l
| _ falsum       m := falsum
| _ (t₁ ≃ t₂)    m := t₁.map_vars (map_lift f m) ≃ t₂.map_vars (map_lift f m)
| _ (rel R)      m := rel R
| _ (apprel r t) m := apprel (map_vars r m) (t.map_vars (map_lift f m))
| _ (f₁ ⟹ f₂)   m := map_vars f₁ m ⟹ map_vars f₂ m
| _ (∀' f)       m := ∀' map_vars f (m+1)

end preformula

def ax_1 {L} {Γ : set (formula L)} {A B : formula L} : Γ ⊢ A ⟹ (B ⟹ A) :=
impI $ impI axm2

def ax_2 {L} {Γ : set (formula L)} {A B C : formula L} :
  Γ ⊢ (A ⟹ (B ⟹ C)) ⟹ ((A ⟹ B) ⟹ (A ⟹ C)) :=
impI $ impI $ impI $ impE _ (impE _ (weakening1 axm2) axm1) $ impE _ axm2 axm1

def ax_3 {L} {Γ : set (formula L)} {A B : formula L} :
  Γ ⊢ (∼A ⟹ ∼B) ⟹ (B ⟹ A) :=
impI $ impI $ falsumE $ impE _ (impE _ (weakening1 axm2) axm1) axm2

end fol

def mm0_value.deps : ∀ {s}, mm0_value s → deps
| mm0_sort.set ⟨n⟩ := deps.single n
| mm0_sort.wff f := fol.preformula.deps f
| mm0_sort.Class f := (fol.preformula.deps f).tail

inductive mm0_context.value_empty (bv : list ℕ) : list ℕ → Type 1
| refl : mm0_context.value_empty bv

def mm0_context.value' : ∀ {n}, mm0_context n → Type 1
| _ mm0_context.empty := punit
| _ (mm0_context.lvar c) := mm0_context.value' c × ℕ
| _ (mm0_context.rvar d s h c) := mm0_context.value' c × mm0_value s

def mm0_context.value_bv : ∀ {n c}, @mm0_context.value' n c → list ℕ → list ℕ
| _ mm0_context.empty _ r := r
| _ (@mm0_context.lvar n c) v r := mm0_context.value_bv v.1 (v.2 :: r)
| _ (mm0_context.rvar d s h c) v r := mm0_context.value_bv v.1 r

def mm0_context.value_ok (bv : list ℕ) : ∀ {n} c, @mm0_context.value' n c → bool
| _ mm0_context.empty _ := true
| _ (mm0_context.lvar c) v := mm0_context.value_ok c v.1
| _ (mm0_context.rvar d s h c) v :=
  v.2.deps.disjoint (deps.filter_out d bv) && mm0_context.value_ok c v.1

def mm0_context.value_bv_ok {n} (c) (v : @mm0_context.value' n c) : bool :=
let bv := mm0_context.value_bv v ([]) in
bv.nodup && mm0_context.value_ok bv c v

def mm0_context.value {n} (c : mm0_context n) : Type 1 :=
{v : @mm0_context.value' n c | mm0_context.value_bv_ok c v}

inductive mm0_prim_term : Type
| wtru : mm0_prim_term
| wi : mm0_prim_term
| wn : mm0_prim_term
| wal : mm0_prim_term
| wceq : mm0_prim_term
| wcel : mm0_prim_term
| cab : mm0_prim_term

def mm0_prim_term.tgt : mm0_prim_term → mm0_sort
| mm0_prim_term.wtru := mm0_sort.wff
| mm0_prim_term.wi := mm0_sort.wff
| mm0_prim_term.wn := mm0_sort.wff
| mm0_prim_term.wal := mm0_sort.wff
| mm0_prim_term.wceq := mm0_sort.wff
| mm0_prim_term.wcel := mm0_sort.wff
| mm0_prim_term.cab := mm0_sort.Class

def mm0_prim_term.args : ∀ t : mm0_prim_term, Σ n, mm0_context n
| mm0_prim_term.wtru := ⟨0, mm0_context.empty⟩
| mm0_prim_term.wi := ⟨0,
    mm0_context.rvar ([]) mm0_sort.wff rfl $
    mm0_context.rvar ([]) mm0_sort.wff rfl $
    mm0_context.empty⟩
| mm0_prim_term.wn := ⟨0,
    mm0_context.rvar ([]) mm0_sort.wff rfl $
    mm0_context.empty⟩
| mm0_prim_term.wal := ⟨1,
    mm0_context.rvar ([tt]) mm0_sort.wff rfl $
    mm0_context.lvar $ mm0_context.empty⟩
| mm0_prim_term.wceq := ⟨0,
    mm0_context.rvar ([]) mm0_sort.Class rfl $
    mm0_context.rvar ([]) mm0_sort.Class rfl $
    mm0_context.empty⟩
| mm0_prim_term.wcel := ⟨0,
    mm0_context.rvar ([]) mm0_sort.Class rfl $
    mm0_context.rvar ([]) mm0_sort.Class rfl $
    mm0_context.empty⟩
| mm0_prim_term.cab := ⟨1,
    mm0_context.rvar ([tt]) mm0_sort.wff rfl $
    mm0_context.lvar $ mm0_context.empty⟩

def mm0_prim_term.value' : ∀ (t : mm0_prim_term), t.args.2.value' → mm0_value t.tgt
| mm0_prim_term.wtru _ := ⊤
| mm0_prim_term.wi ⟨⟨_, f₁⟩, f₂⟩ := f₁ ⟹ f₂
| mm0_prim_term.wn ⟨_, f⟩ := ∼f
| mm0_prim_term.wal ⟨⟨_, x⟩, f⟩ := ∀' f.map_vars (fol.move0 x) 0
| mm0_prim_term.wceq ⟨⟨_, e₁⟩, e₂⟩ := ∀' (e₁ ⇔ e₂)
| mm0_prim_term.wcel ⟨⟨_, A⟩, B⟩ := ∃' (∀' (&1 ∈' &0 ⇔ A ↑ 1) ⊓ B)
| mm0_prim_term.cab ⟨⟨_, x⟩, f⟩ := f.map_vars (fol.move0 x) 0

def mm0_prim_term.value (t : mm0_prim_term) (v : t.args.2.value) : mm0_value t.tgt := t.value' v.1

inductive mm0_preterm : ∀ {γ} (Γ : mm0_context γ) {m}, mm0_context m → mm0_sort → Type
| lvar {γ Γ} (i) : i < γ → @mm0_preterm γ Γ _ mm0_context.empty mm0_sort.set
| rvar {γ Γ} (i) {s} : @mm0_context.sort γ Γ i = some s → mm0_preterm Γ mm0_context.empty s
| prim {γ Γ} (t : mm0_prim_term) : @mm0_preterm γ Γ _ t.args.2 t.tgt
| lapp {γ Γ n c s} (i) :
  @mm0_preterm γ Γ _ (@mm0_context.lvar n c) s → i < γ → mm0_preterm Γ c s
| rapp {γ Γ n d' s' h c s} :
  @mm0_preterm γ Γ _ (@mm0_context.rvar n d' s' h c) s →
  mm0_preterm Γ mm0_context.empty s' →
  mm0_preterm Γ c s
| defn {γ Γ n c s} : mm0_preterm c mm0_context.empty s → @mm0_preterm γ Γ n c s

def mm0_term {γ} (Γ : mm0_context γ) : mm0_sort → Type := mm0_preterm Γ mm0_context.empty

def mm0_preterm.weak_deps : ∀ {γ Γ m c s}, @mm0_preterm γ Γ m c s → deps
| _ _ _ _ _ (@mm0_preterm.lvar _ _ i _) := deps.single i
| _ _ _ _ _ (@mm0_preterm.rvar _ Γ i _ _) := Γ.rvar_deps i
| _ _ _ _ _ (@mm0_preterm.prim _ _ t) := ([])
| _ _ _ _ _ (@mm0_preterm.lapp _ _ _ _ _ i f _) := f.weak_deps.union (deps.single i)
| _ _ _ _ _ (@mm0_preterm.rapp _ _ _ _ _ _ _ _ f t) := f.weak_deps.union t.weak_deps
| _ _ _ _ _ (@mm0_preterm.defn _ _ _ _ _ t) := ([])

def mm0_context.value'.lnth_rev : ∀ {n} {c : mm0_context n} (i : ℕ), c.value' → ℕ
| _ mm0_context.empty i _ := 0
| _ (mm0_context.lvar c) 0 v := v.2
| _ (mm0_context.lvar c) (n+1) v := v.1.lnth_rev n
| _ (mm0_context.rvar d s h c) n v := v.1.lnth_rev n

def mm0_context.value'.lnth {n} {c : mm0_context n} (i : ℕ) (v : c.value') : ℕ :=
v.lnth_rev (n - i.succ)

def mm0_lvar.value {n} {c : mm0_context n} (i : ℕ) (v : c.value) : ℕ :=
mm0_context.value'.lnth i v.1

def mm0_ovalue : option mm0_sort → Type 1
| none := punit
| (some s) := mm0_value s

def mm0_context.value'.rnth_rev :
  ∀ {n} {c : mm0_context n}, c.value' → ∀ i, mm0_ovalue (c.sort_rev i)
| _ mm0_context.empty _ i := ⟨⟩
| _ (mm0_context.lvar c) v i := v.1.rnth_rev i
| _ (mm0_context.rvar d s h c) v 0 := v.2
| _ (mm0_context.rvar d s h c) v (i+1) := v.1.rnth_rev i

theorem mm0_context.sort_rev_eq {n} (c : mm0_context n) {i s}
  (h : mm0_context.sort c i = some s) :
  c.sort_rev (c.rsize - i.succ) = some s :=
begin
  unfold mm0_context.sort at h,
  rw nat.sub_eq_psub,
  cases c.rsize.psub i.succ, {cases h},
  exact h
end

def mm0_context.value'.rnth {n} {c : mm0_context n} (v : c.value')
  {i s} (h : mm0_context.sort c i = some s) : mm0_value s :=
begin
  have := v.rnth_rev (c.rsize - i.succ),
  rwa c.sort_rev_eq h at this
end

def mm0_preterm.value' : ∀ {γ} {Γ : mm0_context γ} (V : Γ.value')
  {m c s}, @mm0_preterm _ Γ m c s → c.value' → mm0_value s
| _ _ V _ _ _ (@mm0_preterm.lvar _ _ i h) v := ⟨V.lnth i⟩
| _ _ V _ _ s (@mm0_preterm.rvar _ _ i _ h) v := V.rnth h
| _ _ V _ _ s (@mm0_preterm.prim _ _ t) v := mm0_prim_term.value' _ v
| _ _ V m c s (@mm0_preterm.lapp _ _ n c' _ i f t) v :=
  mm0_preterm.value' V f $ by exact (v, V.lnth i)
| _ _ V m c s (@mm0_preterm.rapp _ _ n d' s' h c' _ f t) v :=
  mm0_preterm.value' V f $ by exact (v, mm0_preterm.value' V t $ by split)
| _ _ V m c s (@mm0_preterm.defn _ _ _ _ _ t) v :=
  mm0_preterm.value' v t $ by split

def mm0_preterm.value {γ} {Γ : mm0_context γ} (V : Γ.value)
  {m c s} (t : @mm0_preterm _ Γ m c s) (v : c.value) : mm0_value s := t.value' V.1 v.1

def mm0_term.value {γ} {Γ : mm0_context γ} (V : Γ.value)
  {s} (t : mm0_term Γ s) : mm0_value s := mm0_preterm.value V t ⟨⟨⟩, rfl⟩

section
open tactic

meta def name.is_numeric : name → bool
| (name.mk_numeral _ name.anonymous) := tt
| (name.mk_numeral _ n) := n.is_numeric
| (name.mk_string _ n) := n.is_numeric
| _ := ff

meta def is_forall_domain : pexpr → bool
| (expr.const n ([])) := n.is_numeric
| _ := ff

meta def ref_apply (r : ref expr) (n : name) : tactic unit := do
  m ← read_ref r,
  e ← mk_const n,
  m' ← mk_mvar,
  to_expr ```(%%e %%m') >>= unify m,
  write_ref r m'

meta def tactic.mk_term : expr → pexpr → tactic unit
| m (expr.pi x bi b t) := do
  if is_forall_domain b then do
    m1 ← mk_mvar,
    m2 ← mk_mvar,
    to_expr ```(((mm0_preterm.prim mm0_prim_term.wal).rapp %%m2).lapp %%m1) >>= unify m,
    tactic.mk_term m1 (expr.local_const x x bi ``(ℕ)),
    tactic.mk_term m2 $ (expr.lam x bi b t).subst (expr.local_const x x bi ``(ℕ))
  else do
    m1 ← mk_mvar,
    m2 ← mk_mvar,
    to_expr ```(((mm0_preterm.prim mm0_prim_term.wi).rapp %%m2).rapp %%m1) tt ff >>= unify m,
    tactic.mk_term m1 b,
    tactic.mk_term m2 $
      (expr.lam x bi b t).subst (expr.local_const x x bi ``(ℕ))
| m (expr.local_const _ (name.mk_string v name.anonymous) _ _) :=
  if v.front = 'v' then do
    let i := v.mk_iterator.next.next_to_string.to_nat,
    e ← mk_mvar,
    to_expr ```(mm0_preterm.rvar %%(reflect i) %%e) >>= unify m,
    to_expr ```(rfl) >>= unify e
  else if v.front = 'x' then do
    let i := v.mk_iterator.next.next_to_string.to_nat,
    e ← mk_mvar,
    to_expr ```(mm0_preterm.rvar %%(reflect i) %%e) >>= unify m,
    to_expr ```(rfl) >>= unify e
    -- using_new_ref m $ λ r, do
    --   ref_apply r `mm0_preterm.lvar,
    --   iterate_exactly i $ do
    --     repeat $ ref_apply r `mm0_lvar.rtail,
    --     ref_apply r `mm0_lvar.ltail,
    --   repeat $ ref_apply r `mm0_lvar.rtail,
    --   m ← read_ref r,
    --   to_expr ```(mm0_lvar.head) >>= unify m
  else fail v
| m e@(expr.app e1 e2) := match expr.erase_annotations e1 with
  | (expr.const `not ([])) := do
    m' ← mk_mvar,
    to_expr ```((mm0_preterm.prim mm0_prim_term.wn).rapp %%m') tt ff >>= unify m,
    tactic.mk_term m' e2
  | e1' := trace e1'.to_raw_fmt >> failed
  end
| m e := match expr.is_annotation e with
  | some (_, e') := tactic.mk_term m e'
  | none := trace e.to_raw_fmt >> failed
  end

meta def tactic.interactive.mk_term :
  interactive.parse interactive.types.texpr → tactic unit
| e := do m ← get_goals, tactic.mk_term m.head e

end

inductive mm0_stmt {γ} (Γ : mm0_context γ) : Type
| proof : mm0_term Γ mm0_sort.wff → mm0_stmt
| conv {s} : mm0_term Γ s → mm0_term Γ s → mm0_stmt

def mm0_stmt.value {γ} {Γ : mm0_context γ} : mm0_stmt Γ → Type 1
| (mm0_stmt.proof t) := Π V, fol.Theory.fst zfc.ZFC ⊢ t.value V
| (mm0_stmt.conv t₁ t₂) := Π V, plift $ t₁.value V = t₂.value V

def mm0_thm.value {γ} {Γ : mm0_context γ} :
  list (mm0_term Γ mm0_sort.wff) → mm0_term Γ mm0_sort.wff → Type 1
| ([])      conc := (mm0_stmt.proof conc).value
| (h :: hs) conc := (mm0_stmt.proof h).value → mm0_thm.value hs conc

def mm0_subst {γ} (Γ : mm0_context γ) : ∀ {n}, mm0_context n → Type
| _ mm0_context.empty := punit
| _ (mm0_context.lvar c) := mm0_subst c × {i // i < γ}
| _ (mm0_context.rvar d s h c) := mm0_subst c × mm0_term Γ s

def mm0_subst.lnth_rev {γ Γ} : ∀ {n c}, ℕ → @mm0_subst γ Γ n c → ℕ
| _ mm0_context.empty i σ := 0
| _ (mm0_context.lvar c) 0 σ := σ.2.1
| _ (mm0_context.lvar c) (n+1) σ := σ.1.lnth_rev n
| _ (mm0_context.rvar d s h c) n σ := σ.1.lnth_rev n

def mm0_subst.lnth {γ Γ n c} (i : ℕ) (σ : @mm0_subst γ Γ n c) : ℕ :=
σ.lnth_rev (n - i.succ)

theorem mm0_subst.lnth_rev_lt {γ Γ} : ∀ {n c i} (σ : @mm0_subst γ Γ n c),
  i < n → mm0_subst.lnth_rev i σ < γ
| _ (mm0_context.lvar c) 0 σ h := σ.2.2
| _ (mm0_context.lvar c) (n+1) σ h := σ.1.lnth_rev_lt (nat.lt_of_succ_lt_succ h)
| _ (mm0_context.rvar _ _ _ c) n σ h := σ.1.lnth_rev_lt h

theorem mm0_subst.lnth_lt {γ Γ n c i} (σ : @mm0_subst γ Γ n c)
  (h : i < n) : mm0_subst.lnth i σ < γ :=
σ.lnth_rev_lt (nat.sub_lt (lt_of_le_of_lt (zero_le _) h) (nat.succ_pos _))

def mm0_oterm {γ} (Γ : mm0_context γ) : option mm0_sort → Type
| none := punit
| (some s) := mm0_term Γ s

def mm0_subst.rnth_rev {γ Γ} : ∀ {n c} (i : ℕ),
  @mm0_subst γ Γ n c → mm0_oterm Γ (c.sort_rev i)
| _ mm0_context.empty i σ := ⟨⟩
| _ (mm0_context.lvar c) i σ := σ.1.rnth_rev i
| _ (mm0_context.rvar d s h c) 0 σ := σ.2
| _ (mm0_context.rvar d s h c) (i+1) σ := σ.1.rnth_rev i

def mm0_subst.rnth {γ Γ n c} (σ : @mm0_subst γ Γ n c)
  (i) {s} (h : mm0_context.sort c i = some s) : mm0_term Γ s :=
begin
  have := σ.rnth_rev (c.rsize - i.succ),
  rwa c.sort_rev_eq h at this
end

def mm0_subst.apply : ∀ {γ Γ δ Δ} (σ : @mm0_subst γ Γ δ Δ),
  ∀ {n c s}, @mm0_preterm _ Δ n c s → mm0_preterm Γ c s
| γ Γ δ Δ σ _ _ _ (mm0_preterm.lvar i h) :=
  mm0_preterm.lvar (σ.lnth i) (σ.lnth_lt h)
| γ Γ δ Δ σ _ _ _ (mm0_preterm.rvar i h) := σ.rnth i h
| γ Γ δ Δ σ _ _ _ (mm0_preterm.prim t) := mm0_preterm.prim t
| γ Γ δ Δ σ _ _ _ (mm0_preterm.lapp i f h) :=
  (σ.apply f).lapp (σ.lnth i) (σ.lnth_lt h)
| γ Γ δ Δ σ _ _ _ (mm0_preterm.rapp f t) := (σ.apply f).rapp (σ.apply t)
| γ Γ δ Δ σ _ _ _ (mm0_preterm.defn t) := mm0_preterm.defn t

inductive mm0_axiom : Type
| ax_1 | ax_2 | ax_3 | ax_mp

def mm0_axiom.args : ∀ t : mm0_axiom, Σ n, mm0_context n
| mm0_axiom.ax_1 := ⟨0,
    mm0_context.rvar ([]) mm0_sort.wff rfl $
    mm0_context.rvar ([]) mm0_sort.wff rfl $
    mm0_context.empty⟩
| mm0_axiom.ax_2 := ⟨0,
    mm0_context.rvar ([]) mm0_sort.wff rfl $
    mm0_context.rvar ([]) mm0_sort.wff rfl $
    mm0_context.rvar ([]) mm0_sort.wff rfl $
    mm0_context.empty⟩
| mm0_axiom.ax_3 := ⟨0,
    mm0_context.rvar ([]) mm0_sort.wff rfl $
    mm0_context.rvar ([]) mm0_sort.wff rfl $
    mm0_context.empty⟩
| mm0_axiom.ax_mp := ⟨0,
    mm0_context.rvar ([]) mm0_sort.wff rfl $
    mm0_context.rvar ([]) mm0_sort.wff rfl $
    mm0_context.empty⟩

def mm0_axiom.hyps : ∀ t : mm0_axiom, list (mm0_term t.args.2 mm0_sort.wff)
| mm0_axiom.ax_1 := []
| mm0_axiom.ax_2 := []
| mm0_axiom.ax_3 := []
| mm0_axiom.ax_mp := [by mk_term v0, by mk_term v0 → v1]

def mm0_axiom.conc : ∀ t : mm0_axiom, mm0_term t.args.2 mm0_sort.wff
| mm0_axiom.ax_1 := by mk_term v0 → v1 → v0
| mm0_axiom.ax_2 := by mk_term (v0 → v1 → v2) → (v0 → v1) → v0 → v2
| mm0_axiom.ax_3 := by mk_term (¬ v0 → ¬ v1) → v1 → v0
| mm0_axiom.ax_mp := by mk_term v1

def mm0_axiom.sound : ∀ t : mm0_axiom, mm0_thm.value t.hyps t.conc
| mm0_axiom.ax_1 := λ V, fol.ax_1
| mm0_axiom.ax_2 := λ V, fol.ax_2
| mm0_axiom.ax_3 := λ V, fol.ax_3
| mm0_axiom.ax_mp := λ h₁ h₂ V, fol.prf.impE _ (h₂ V) (h₁ V)

inductive mm0_preproof {γ Γ}
  (hyps : list (@mm0_term γ Γ mm0_sort.wff)) :
  list (mm0_term Γ mm0_sort.wff) → mm0_term Γ mm0_sort.wff → Type
| Axiom (A : mm0_axiom) (σ : mm0_subst Γ A.args.2) :
  mm0_preproof (A.hyps.map σ.apply) (σ.apply A.conc)
| app {h hs p} : mm0_preproof (h :: hs) p → mm0_preproof ([]) h → mm0_preproof hs p
| hyp (i h) : mm0_preproof ([]) (hyps.nth_le i h)

def mm0_proof {γ Γ} (hyps : list (mm0_term Γ mm0_sort.wff)) :
  @mm0_term γ Γ mm0_sort.wff → Type :=
mm0_preproof hyps ([])

def mm0_thm.weaken1 {γ Γ} : ∀ hyps {t},
  (mm0_stmt.proof t).value → @mm0_thm.value γ Γ hyps t
| ([])    t h := h
| (l::ls) t h := λ _, mm0_thm.weaken1 ls h

def mm0_thm.weaken {γ Γ} : ∀ {hs hyps t},
  mm0_thm.value hs t → @mm0_thm.value γ Γ (hs ++ hyps) t
| ([])    ls t h := mm0_thm.weaken1 ls h
| (e::es) ls t h := λ x, mm0_thm.weaken (h x)

def mm0_subst.sound {γ Γ} : ∀ {n c} (σ : @mm0_subst γ Γ n c) {hs t},
  mm0_thm.value hs t → mm0_thm.value (hs.map σ.apply) (σ.apply t) :=
sorry

def mm0_preproof.app_sound1 {γ Γ s} : ∀ {hs p},
  ((@mm0_stmt.proof γ Γ s).value → @mm0_thm.value γ Γ hs p) →
  mm0_thm.value hs s → mm0_thm.value hs p
| ([]) t f v := f v
| (h::hs) t f v := λ x, mm0_preproof.app_sound1 (λ y, f y x) (v x)

def mm0_preproof.app_sound {γ Γ}
  (hyps : list (@mm0_term γ Γ mm0_sort.wff)) : ∀ {s hs p},
  ((mm0_stmt.proof s).value → mm0_thm.value (hs ++ hyps) p) →
  mm0_thm.value hyps s → mm0_thm.value (hs ++ hyps) p
| s ([]) t f v := mm0_preproof.app_sound1 f v
| s (h::hs) t f v := λ x, mm0_preproof.app_sound (λ y, f y x) v

def mm0_preproof.hyp_sound {γ Γ} : ∀ hs i h, @mm0_thm.value γ Γ hs (list.nth_le hs i h)
| ([]) _ h' := absurd h' (nat.not_lt_zero _)
| (h::hs) 0     h' := λ x, mm0_thm.weaken1 _ x
| (h::hs) (n+1) h' := λ x, mm0_preproof.hyp_sound _ _ _

def mm0_preproof.sound {γ Γ hyps} :
  ∀ {hs t}, @mm0_preproof γ Γ hyps hs t → mm0_thm.value (hs ++ hyps) t
| _ _ (mm0_preproof.Axiom _ A σ) := mm0_thm.weaken $ σ.sound A.sound
| _ _ (mm0_preproof.app P p) := mm0_preproof.app_sound _ P.sound p.sound
| _ _ (mm0_preproof.hyp i h) := mm0_preproof.hyp_sound _ _ _
