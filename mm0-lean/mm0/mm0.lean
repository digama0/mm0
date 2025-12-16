import data.finset.basic

namespace mm0

@[derive has_reflect]
structure sort_data := (pure strict provable free : bool := ff)

def sort_id := ℕ
def term_id := ℕ
def thm_id := ℕ
def var_id := ℕ

inductive binder
| bound : sort_id → binder
| reg : sort_id → finset var_id → binder

def binder.sort : binder → sort_id
| (binder.bound s) := s
| (binder.reg s _) := s

-- Lean doesn't do great with nested inductives
-- inductive sexpr
-- | var : var_id → sexpr
-- | app : term_id → list sexpr → sexpr

inductive sexpr
| var : var_id → sexpr
| term : term_id → sexpr
| app1 : sexpr → sexpr → sexpr

def sexpr.app' : sexpr → list sexpr → sexpr
| f [] := f
| f (x :: xs) := sexpr.app' (sexpr.app1 f x) xs

def sexpr.app (t : term_id) : list sexpr → sexpr :=
sexpr.app' (sexpr.term t)

def dep_type := sort_id × finset var_id

@[reducible] def ctx := list binder

inductive decl
| sort : sort_id → sort_data → decl
| term : term_id → ctx → dep_type → decl
| defn : term_id → ctx → dep_type → option (list sort_id × sexpr) → decl
| ax : ctx → list sexpr → sexpr → decl
| thm : ctx → list sexpr → sexpr → decl

@[reducible] def env := list decl

def env.get_sd (e : env) (s sd) : Prop :=
decl.sort s sd ∈ e

inductive env.get_term (e : env) (t a r) : option (list sort_id × sexpr) → Prop
| term : decl.term t a r ∈ e → env.get_term none
| defn {o} : decl.defn t a r o ∈ e → env.get_term o

def env.get_thm (e : env) (t a r) : Prop :=
decl.ax t a r ∈ e ∨ decl.thm t a r ∈ e

def env.is_sort (e : env) (s) : Prop := ∃ sd, e.get_sd s sd

def ctx.is_bound (Γ : ctx) (x) : Prop :=
∃ s, Γ.nth x = some (binder.bound s)

def dep_type.ok (e Γ) : dep_type → Prop
| ⟨s, vs⟩ := env.is_sort e s ∧ ∀ x ∈ vs, ctx.is_bound Γ x

-- Lean doesn't like induction on lists on the right, but
-- we write it this way for consistency with mm0.mm0
inductive ctx.ok (e : env) : ctx → Prop
| nil : ctx.ok []
| bound {s sd Γ} :
  env.get_sd e s sd → ¬ sd.strict →
  ctx.ok Γ → ctx.ok (Γ ++ [binder.bound s])
| reg {s vs Γ} : dep_type.ok e Γ (s, vs) →
  ctx.ok Γ → ctx.ok (Γ ++ [binder.reg s vs])

-- Helper function to allow defining the mutual recursive functions Expr and ExprBi
def sexpr.ok_bi' (e : env) (Γ : ctx) (e : sexpr) (P : sort_id → Prop) : binder → Prop
| (binder.bound s) := ∃ v, e = sexpr.var v ∧ Γ.nth v = some (binder.bound s)
| (binder.reg s vs) := P s

-- The lean version has an extra argument because there are preterms
-- (unapplied expressions)
inductive sexpr.ok' (e : env) (Γ : ctx) : sexpr → list binder → sort_id → Prop
| var {v bi} : Γ.nth v = some bi → sexpr.ok' (sexpr.var v) [] bi.sort
| term {f bis ret o} : e.get_term f bis ret o →
  sexpr.ok' (sexpr.term f) bis ret.1
| app_var {f s v bis ret} :
  Γ.nth v = some (binder.bound s) →
  sexpr.ok' f (binder.bound s :: bis) ret →
  sexpr.ok' (sexpr.app1 f (sexpr.var v)) bis ret
| app_reg {f x s vs bis ret} :
  sexpr.ok' f (binder.reg s vs :: bis) ret →
  sexpr.ok' x [] s →
  sexpr.ok' (sexpr.app1 f x) bis ret

def sexpr.ok (E : env) (Γ : ctx) (e : sexpr) (s : sort_id) : Prop :=
sexpr.ok' E Γ e [] s

def sexpr.ok_bi (E : env) (Γ : ctx) (e : sexpr) : binder → Prop
| (binder.bound s) := ∃ v, e = sexpr.var v ∧ Γ.nth v = some (binder.bound s)
| (binder.reg s vs) := sexpr.ok E Γ e s

def sexpr.ok_prov (E : env) (Γ : ctx) (e : sexpr) : Prop :=
∃ s sd, sexpr.ok E Γ e s ∧ E.get_sd s sd ∧ sd.provable

def append_dummies (Γ : ctx) (ds : list sort_id) : ctx :=
Γ ++ ds.map binder.bound

def sexpr.has_var (Γ : ctx) : sexpr → var_id → Prop
| (sexpr.var u) v := ∃ bi, Γ.nth u = some bi ∧
  match bi with
  | binder.bound s := u = v
  | binder.reg s vs := v ∈ vs
  end
| (sexpr.term f) v := false
| (sexpr.app1 f x) v := f.has_var v ∨ x.has_var v

def maybe_free_args (es : list sexpr) (a : binder) (v : var_id) : Prop :=
∃ s vs, a = binder.reg s vs ∧ ¬ ∃ u ∈ vs, es.nth u = some (sexpr.var v)

def sexpr.free' (E : env) (Γ : ctx) (v : var_id) :
  sexpr → list sexpr → list Prop → Prop
| (sexpr.var u) _ _ := sexpr.has_var Γ (sexpr.var u) v
| (sexpr.term f) es ps := ∃ args r rs o,
  E.get_term f args (r, rs) o ∧
  (∃ n free a, ps.nth n = some free ∧ args.nth n = some a ∧
    free ∧ maybe_free_args es a v) ∧
  ∃ u ∈ rs, es.nth u = some (sexpr.var v)
| (sexpr.app1 f x) es ps :=
  sexpr.free' f (x :: es) (sexpr.free' x [] [] :: ps)

def sexpr.free (E : env) (Γ : ctx) (e : sexpr) (v : var_id) : Prop :=
sexpr.free' E Γ v e [] []

def term_ok (E : env) (t args ret) : Prop :=
(¬ ∃ a r v, E.get_term t a r v) ∧
ctx.ok E args ∧ dep_type.ok E args ret ∧
  ∃ sd, E.get_sd ret.1 sd ∧ ¬ sd.pure

def defn_ok (E : env) (t args ret ds e) : Prop :=
term_ok E t args ret ∧ let Γ := append_dummies args ds in
  Γ.ok E ∧ sexpr.ok E Γ e ret.1 ∧
    ∀ v, sexpr.free E Γ e v → v ∈ ret.2 ∨
      ∃ sd s, (Γ.nth v = some (binder.bound s) ∧
        E.get_sd s sd ∧ sd.free)

def axiom_ok (E : env) (args hs) (ret : sexpr) : Prop :=
ctx.ok E args ∧ ∀ x ∈ list.cons ret hs, sexpr.ok_prov E args x

def decl.ok (E : env) : decl → Prop
| (decl.sort id sd) := true
| (decl.term t args ret) := term_ok E t args ret
| (decl.defn t args ret none) := term_ok E t args ret
| (decl.defn t args ret (some (ds, e))) := defn_ok E t args ret ds e
| (decl.ax args hs ret) := axiom_ok E args hs ret
| (decl.thm args hs ret) := axiom_ok E args hs ret

inductive env.ok : env → Prop
| nil : env.ok []
| cons {E d} : env.ok E → decl.ok E d → env.ok (E ++ [d])

inductive env.extend : env → env → Prop
| nil : env.extend [] []
| keep {E1 E2 d} : env.extend E1 E2 → env.extend (E1 ++ [d]) (E2 ++ [d])
| defn_skip {E1 E2 id a r o} :
  env.extend E1 E2 →
  env.extend E1 (E2 ++ [decl.defn id a r o])
| defn_def {E1 E2 id a r o} :
  env.extend E1 E2 →
  env.extend (E2 ++ [decl.defn id a r none]) (E2 ++ [decl.defn id a r o])
| thm_skip {E1 E2 a h r} :
  env.extend E1 E2 →
  env.extend E1 (E2 ++ [decl.thm a h r])

instance : inhabited sexpr := ⟨sexpr.var (0:ℕ)⟩

def sexpr.subst (σ : list sexpr) : sexpr → sexpr
| (sexpr.var v) := σ.inth v
| (sexpr.term f) := sexpr.term f
| (sexpr.app1 f x) := f.subst.app1 x.subst

-- In mm0.mm0, we use a type CExpr to denote proofs and existentially
-- quantify over them to get the proof judgment. In Lean, we can do this
-- directly with an inductive proof predicate.
inductive conv' (E : env) (Γ : ctx) : sexpr → sexpr → list binder → sort_id → Prop
| refl {e args s} : sexpr.ok' E Γ e args s → conv' e e args s
| symm {e1 e2 s} : conv' e1 e2 [] s → conv' e2 e1 [] s
| cong {f1 f2 bi bis x1 x2 s} :
  sexpr.ok_bi E Γ x1 bi → sexpr.ok_bi E Γ x2 bi →
  conv' f1 f2 (bi :: bis) s →
  conv' x1 x2 [] bi.sort →
  conv' (sexpr.app1 f1 x1) (sexpr.app1 f2 x2) bis s
| unfold {t args ret ys val es zs e2 s} :
  E.get_term t args ret (some (ys, val)) →
  list.forall₂ (sexpr.ok_bi E Γ) es args →
  list.forall₂ (λ y z, Γ.nth z = some (binder.bound y)) ys zs →
  conv' (sexpr.app t es) e2 [] s →
  conv' (sexpr.subst (es ++ list.map sexpr.var zs) val) e2 [] s

def conv (E : env) (Γ : ctx) (e1 e2 : sexpr) (s : sort_id) : Prop :=
conv' E Γ e1 e2 [] s

def safe_subst (Γ : ctx) (σ : list sexpr) : Prop :=
∀ u v, (∃ s, Γ.nth u = some (binder.bound s)) →
  v < Γ.length → ¬ sexpr.has_var Γ (sexpr.var v) u →
  ∀ y e2, σ.nth u = some (sexpr.var y) → σ.nth v = some e2 →
    ¬ e2.has_var Γ y

-- We generalize to a possibly infinite set of hypotheses for no particular reason
inductive proof (E : env) (Γ : ctx) (Hs : set sexpr) : sexpr → Prop
| hyp {h} : h ∈ Hs → proof h
| thm {args hs ret σ} :
  E.get_thm args hs ret →
  list.forall₂ (sexpr.ok_bi E Γ) σ args →
  safe_subst Γ σ →
  (∀ h ∈ hs, proof (sexpr.subst σ h)) →
  proof (sexpr.subst σ ret)
| conv {e1 e2 s} : conv E Γ e1 e2 s → proof e1 → proof e2

inductive env.proof' : env → Prop
| nil : env.proof' []
| sort {E s sd} : env.proof' E → env.proof' (E ++ [decl.sort s sd])
| term {E id a r} : env.proof' E → env.proof' (E ++ [decl.term id a r])
| defn {E id a r o} : env.proof' E → env.proof' (E ++ [decl.defn id a r (some o)])
| ax {E a h r} : env.proof' E → env.proof' (E ++ [decl.ax a h r])
| thm {E a hs r ds} :
  let Γ := append_dummies a ds in
  ctx.ok E Γ → proof E Γ {h | h ∈ hs} r →
  env.proof' E → env.proof' (E ++ [decl.thm a hs r])

def env.proof (E : env) : Prop := ∃ E', env.extend E E' ∧ E'.proof'

end mm0
