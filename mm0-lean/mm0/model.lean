import .mm0

namespace mm0
universe u
def sort_data.model (α : Type u) (sd : sort_data) : Type u :=
cond sd.provable (set α) punit

section
parameters (A U : Type u)

def second : Type u := (A → U) → U
def termval : Type u := list second → second

def second.supported (s : set A) (F : second) : Prop :=
∀ v w : A → U, (∀ x ∉ s, v x = w x) → F v = F w

def env.model' : list decl → Type u
| [] := punit
| (decl.sort s sd :: E') := set U × set U × env.model' E'
| (decl.term _ a r :: E') := termval × env.model' E'
| (decl.defn _ a r _ :: E') := termval → env.model' E'
| (decl.ax _ _ _ :: E') := env.model' E'
| (decl.thm _ _ _ :: E') := env.model' E'

def terms_model := term_id → termval → Prop

structure env_ctx_model :=
(sorts : sort_id → U → Prop)
(provs : sort_id → U → Prop)
(ss : ∀ {{s x}}, provs s x → sorts s x)
(terms : sort_id → termval → Prop)

def env_ctx_model.insert_sort (id) (S P : U → Prop) (H : ∀ x, P x → S x)
  (E : env_ctx_model) : bool → env_ctx_model
| ff := {
  sorts := λ s x, E.sorts s x ∨ id = s ∧ S x,
  ss := λ s x h, (or.inl (E.ss h)),
  ..E}
| tt := {
  sorts := λ s x, E.sorts s x ∨ id = s ∧ S x,
  provs := λ s x, E.provs s x ∨ id = s ∧ P x,
  ss := λ s x, or.imp (@env_ctx_model.ss _ _ _) (and.imp_right (H _)),
  ..E}

def env_ctx_model.insert_term (id F) (E : env_ctx_model) : env_ctx_model :=
{terms := λ f F', E.terms f F' ∨ id = f ∧ F = F', ..E}

variables (E : env_ctx_model)
/-
def valuation.ok (Γ : rlist (var_id × sort_id)) (vs : finset var_id) (f : A → U) : Prop :=
∀ v s, (v, s) ∈ Γ → v ∈ vs → E.sorts s (f v)

def dep_type.model.ok (Γ : rlist (var_id × sort_id)) : dep_type → second → Prop
| (s, vs) F := ∀ l, valuation.ok E Γ vs l → E.sorts s (F l)

def dep_type.model.supported (S : finset var_id) (Γ : rlist (var_id × sort_id)) : dep_type → second U → Prop
| (s, vs) F := F.supported (S ∪ vs)

def binders.ok'
  (D : rlist (var_id × sort_id) → dep_type → second → Prop)
  (P : rlist (var_id × sort_id) → ℕ → Prop) :
  list binder → rlist (var_id × sort_id) → ℕ → list second → Prop
| [] Γ n [] := P Γ n
| [] Γ n (_::_) := false
| (binder.bound s :: bis) Γ n l :=
  binders.ok' bis (Γ |> (n, s)) (n+1) l
| (binder.reg s vs :: bis) Γ n [] := false
| (binder.reg s vs :: bis) Γ n (a :: l) := D Γ (s, vs) a → binders.ok' bis Γ (n+1) l

def binders.supported' (P : rlist (var_id × sort_id) → ℕ → Prop) : list binder → rlist (var_id × sort_id) → ℕ → list (second U) → Prop
| [] Γ n [] := P Γ n
| [] Γ n (_::_) := false
| (binder.bound s :: bis) Γ n l :=
  binders.ok' bis (Γ |> (n, s)) (n+1) l
| (binder.reg s vs :: bis) Γ n [] := false
| (binder.reg s vs :: bis) Γ n (a :: l) :=
  dep_type.model.ok E Γ (s, vs) a → binders.ok' bis Γ (n+1) l

def binders.ok (bis : list binder) (l : list second)
  (D : rlist (var_id × sort_id) → dep_type → second → Prop)
  (P : rlist (var_id × sort_id) → ℕ → Prop) : Prop :=
binders.ok' D P bis [-] 0 l

def term.model.ok (bis : list binder) (ret : dep_type) (F : termval) : Prop :=
∀ l,
  binders.ok bis l (dep_type.model.ok E) (λ Γ _, dep_type.model.ok E Γ ret (F l)) ∧
∀ S, binders.ok bis l
  (λ Γ d F, dep_type.model.ok E Γ d F ∧ F.supported (S ∪ d.2))
  (λ Γ _, (F l).supported (S ∪ ret.2))

def add_dummies : rlist (var_id × sort_id) → ℕ → list sort_id → rlist (var_id × sort_id)
| Γ n [] := Γ
| Γ n (s::ds) := add_dummies (Γ |> (n, s)) (n+1) ds

def sexpr.eval (Γ : rlist (var_id × sort_id)) : sexpr → termval
| none := term.model.ok E bis ret F
| (some (ds, val)) := ∀ l, binders.ok E bis l $ λ Γ n,
  ∀ l', bound_vars.ok E Γ ret.2 l' →
  F l l' =

def defn.model.ok (bis : list binder) (ret : dep_type) (F : termval) : option (list sort_id × sexpr) → Prop
| none := term.model.ok E bis ret F
| (some (ds, val)) := ∀ l, binders.ok E bis l $ λ Γ n,
  ∀ f, valuation.ok E Γ ret.2 f →
  let Γ' := add_dummies Γ n ds in
  F l f =

inductive env.model'.ok : env_ctx_model → ∀ E', env.model' E' → Prop
| nil {E} : env.model'.ok E [] ⟨⟩
| sort {E s sd E' S P H M} :
  env.model'.ok (env_ctx_model.insert_sort s S P H E (sort_data.provable sd)) E' M →
  env.model'.ok E (decl.sort s sd :: E') (S, P, M)
| term {E f a r E' F M} :
  term.model.ok E a r F →
  env.model'.ok (env_ctx_model.insert_term f F E) E' M →
  env.model'.ok E (decl.term f a r :: E') (F, M)
| defn {E f a r o E'} {M : termval → env.model' E'} :
  (∀ F,
    defn.model.ok E a r F o →
    env.model'.ok (env_ctx_model.insert_term f F E) E' (M F)) →
  env.model'.ok E (decl.defn f a r o :: E') M
-/
end

end mm0
