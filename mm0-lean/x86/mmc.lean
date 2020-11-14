import algebra.group_power data.list.alist

namespace alist

def map {α} {β γ : α → Type*} (f : ∀ a, β a → γ a) (l : alist β) : alist γ :=
⟨l.entries.map (λ a, ⟨a.1, f a.1 a.2⟩),
  show (list.map _ _).nodup, by rw list.map_map; exact l.2⟩

end alist

noncomputable theory
local attribute [instance] classical.prop_decidable
namespace mmc

inductive wsize | S8 | S16 | S32 | S64 | Sinf

def wsize.nat_ok : wsize → nat → Prop
| wsize.S8 n := n < 2^8
| wsize.S16 n := n < 2^16
| wsize.S32 n := n < 2^32
| wsize.S64 n := n < 2^64
| wsize.Sinf n := true

def wsize.int_ok : wsize → int → Prop
| wsize.S8 n := -2^7 ≤ n ∧ n < 2^7
| wsize.S16 n := -2^15 ≤ n ∧ n < 2^16
| wsize.S32 n := -2^31 ≤ n ∧ n < 2^32
| wsize.S64 n := -2^64 ≤ n ∧ n < 2^64
| wsize.Sinf n := true

inductive unop | neg | not | bnot (sz : wsize)
inductive binop | and | or | band | bor | lt | le | eq

def user_type : Type := sorry
def func : Type := sorry
def pure_proof : Type := sorry

def var : Type := nat
def tvar : Type := nat
inductive label : Type
| self : label
| reg : nat → label

mutual inductive arg, ty, prop, pexp
with arg : Type
| mk : var → bool → ty → arg

with ty : Type
| var : tvar → ty -- a type variable α
| core_var : tvar → ty -- the core of a variable, |α|
| void | unit | bool -- basic types
| nat (_:wsize) | int (_:wsize) -- integral types
| inter : ty → ty → ty -- intersection type
| union : ty → ty → ty -- union type
| pair : ty → ty → ty -- tuple type
| sigma : arg → ty → ty -- dependent tuple type
| prop : prop → ty -- propositions as types
| user : user_type → ty → pexp → ty -- a user-defined type

with prop : Type
-- basic FOL operations
| true | false
| all : var → ty → prop → prop
| ex : var → ty → prop → prop
| imp : prop → prop → prop
| not : prop → prop
| and : prop → prop → prop
| or : prop → prop → prop

| emp : prop -- the empty heap
| sep : prop → prop → prop -- separating conjunction
| wand : prop → prop → prop -- separating implication
| pexp : pexp → prop -- a boolean proposition as a predicate
| eq : pexp → pexp → prop -- equality of general types
| heap : pexp → pexp → prop -- the points-to assertion x |-> v
| has_ty : pexp → ty → prop -- the [x : ty] typing assertion

with pexp : Type
| var : var → pexp -- a variable reference
| star | tt | ff -- unit and bool constants
| const : ℤ → pexp -- integer constants
| unop : unop → pexp → pexp -- unary operations
| binop : binop → pexp → pexp → pexp -- binary operations
| if_ : option var → pexp → pexp → pexp → pexp -- a conditional expression (possibly dependent)
| pair : pexp → pexp → pexp -- a pair (or dependent pair) ⟨x, y⟩
| call : func → pexp → pexp -- a function call f(x)

def arg.ty : arg → ty
| (arg.mk _ _ τ) := τ

def arg.var : arg → var
| (arg.mk x _ _) := x

inductive place
| var : var → place

inductive tuple_pat
| blank : tuple_pat
| var : var → bool → tuple_pat
| typed : tuple_pat → ty → tuple_pat
| pair : tuple_pat → tuple_pat → tuple_pat

inductive exp
| var : var → exp -- a variable reference
| star | tt | ff -- unit and bool constants
| const : ℤ → exp -- integer constants
| unop : unop → exp → exp -- unary operations
| binop : binop → exp → exp → exp -- binary operations
| if_ : option var → exp → exp → exp → exp -- a conditional expression (possibly dependent)
| pair : exp → exp → exp -- a pair (or dependent pair) ⟨x, y⟩
| call : func → exp → exp -- a function or procedure call

-- a variable declaration let h := t := e in e'
| let_ : option var → tuple_pat → exp → exp → exp
-- a mutation let h := η ← e in e'
| mut : option var → place → exp → exp → exp
-- an unreachable statement
| unreachable : exp → exp
-- declaring jump labels
| label : list (label × arg × exp) → exp → exp
-- jump to a label or return
| goto : label → exp → exp

-- proof of an entailment: proves Q from P where P -* Q is pure
| entail : exp → pure_proof → exp
-- Evaluate a boolean to produce a proof
| assert : exp → exp
-- Extract the type of a variable
| typeof : exp → exp

def user_core : user_type → ty → pexp → ty := sorry
def pure_proof.ok : pure_proof → prop → prop → Prop := sorry

def pexp.to_exp : pexp → exp
| (pexp.var i) := exp.var i
| pexp.star := exp.star
| pexp.tt := exp.tt
| pexp.ff := exp.ff
| (pexp.const n) := exp.const n
| (pexp.unop o e) := exp.unop o e.to_exp
| (pexp.binop o e₁ e₂) := exp.binop o e₁.to_exp e₂.to_exp
| (pexp.if_ b c e₁ e₂) := exp.if_ b c.to_exp e₁.to_exp e₂.to_exp
| (pexp.pair e₁ e₂) := exp.pair e₁.to_exp e₂.to_exp
| (pexp.call f e) := exp.call f e.to_exp

def exp.pure (e : exp) : Prop := ∃ pe, pexp.to_exp pe = e

noncomputable mutual def arg.core, ty.core, prop.core
with arg.core : arg → arg
| (arg.mk x ghost t) := arg.mk x ghost t.core

with ty.core : ty → ty
| (ty.var α) := ty.core_var α
| (ty.core_var α) := ty.core_var α
| ty.void := ty.void
| ty.unit := ty.unit
| ty.bool := ty.bool
| (ty.nat s) := ty.nat s
| (ty.int s) := ty.int s
| (ty.inter a b) := ty.inter a.core b.core
| (ty.union a b) := ty.union a.core b.core
| (ty.pair a b) := ty.pair a.core b.core
| (ty.sigma a b) := ty.sigma a.core b.core
| (ty.user T t e) := ty.user T t.core e
| (ty.prop A) := ty.prop A.core

with prop.core : prop → prop
| prop.true := prop.true
| prop.false := prop.false
| (prop.all x t A) := if t = t.core then prop.all x t A.core else prop.emp
| (prop.ex x t A) := if t = t.core then prop.ex x t A.core else prop.emp
| (prop.imp A B) := if A = A.core then prop.imp A B.core else prop.emp
| (prop.not A) := if A = A.core then prop.not A.core else prop.emp
| (prop.and A B) := prop.and A.core B.core
| (prop.or A B) := prop.or A.core B.core
| prop.emp := prop.emp
| (prop.sep A B) := prop.sep A.core B.core
| (prop.wand A B) := if A = A.core then prop.wand A B.core else prop.emp
| (prop.pexp e) := prop.pexp e
| (prop.eq e₁ e₂) := prop.eq e₁ e₂
| (prop.heap _ _) := prop.emp
| (prop.has_ty e t) := prop.has_ty e t.core

def tuple_pat.size : tuple_pat → ℕ
| (tuple_pat.blank) := 0
| (tuple_pat.var x γ) := 1
| (tuple_pat.typed t _) := t.size
| (tuple_pat.pair t t') := t.size + t'.size

-- substitute e for x
def ty.subst (x : var) (e : pexp) : ty → ty := sorry
def prop.subst (x : var) (e : pexp) : prop → prop := sorry

inductive tuple_pat.to_pexp : tuple_pat → pexp → Prop
| var {x γ} : tuple_pat.to_pexp (tuple_pat.var x γ) (pexp.var x)
| typed {t τ e} :
  tuple_pat.to_pexp t e →
  tuple_pat.to_pexp (tuple_pat.typed t τ) e
| pair {t t' e e'} :
  tuple_pat.to_pexp t e →
  tuple_pat.to_pexp t' e' →
  tuple_pat.to_pexp (tuple_pat.pair t t') (pexp.pair e e')

structure ctx := (args : list arg)

def ctx.app : ctx → list arg → ctx
| ⟨R⟩ S := ⟨S.reverse ++ R⟩

def ctx.get : ctx → var → bool → ty → Prop
| ⟨R⟩ x γ τ := arg.mk x γ τ ∈ R

def ctx.modify (f : arg → arg) (idx : ℕ) : ctx → ctx
| ⟨R⟩ := ⟨list.modify_nth f idx R⟩

inductive tuple_pat.ok : ctx → tuple_pat → ty → list arg → Prop
| blank {Γ τ} : tuple_pat.ok Γ tuple_pat.blank τ []
| var {Γ x γ τ} : tuple_pat.ok Γ (tuple_pat.var x γ) τ [arg.mk x γ τ]
| typed {Γ t τ R} :
  tuple_pat.ok Γ t τ R →
  tuple_pat.ok Γ (tuple_pat.typed t τ) τ R
| sum {Γ x t τ S te t' τ' S' γ} :
  tuple_pat.ok Γ t τ S →
  tuple_pat.to_pexp t te →
  tuple_pat.ok (Γ.app S) t' (ty.subst x te τ') S' →
  tuple_pat.ok Γ (tuple_pat.pair t t') (ty.sigma (arg.mk x γ τ) τ') (S ++ S')
| ex {Γ x t τ S te t' A S'} :
  tuple_pat.ok Γ t τ S →
  tuple_pat.to_pexp t te →
  tuple_pat.ok (Γ.app S) t' (ty.prop (prop.subst x te A)) S' →
  tuple_pat.ok Γ (tuple_pat.pair t t') (ty.prop (prop.ex x τ A)) (S ++ S')
| list {Γ t τ S t' τ' S'} :
  tuple_pat.ok Γ t τ S →
  tuple_pat.ok Γ t' τ' S' →
  tuple_pat.ok Γ (tuple_pat.pair t t') (ty.pair τ τ') (S ++ S')
| sep {Γ t A S t' B S'} :
  tuple_pat.ok Γ t (ty.prop A) S →
  tuple_pat.ok Γ t' (ty.prop B) S' →
  tuple_pat.ok Γ (tuple_pat.pair t t') (ty.prop (prop.sep A B)) (S ++ S')
| and {Γ t A S t' B S'} :
  tuple_pat.ok Γ t (ty.prop A) S →
  tuple_pat.ok Γ t' (ty.prop $ prop.core B) S' →
  tuple_pat.ok Γ (tuple_pat.pair t t') (ty.prop (prop.and A B)) (S ++ S')

-- substitute for the type variables in an expression
def ty.tsubst : tvar → ty → ty → ty := sorry
def pexp.tsubst : tvar → ty → pexp → pexp := sorry

-- Typing for primitive operations (assumes exactly one type variable)
def user.type : user_type → tvar → ty → Prop := sorry

def func.type : func → arg → ty → Prop := sorry
def proc.type : func → arg → ty → Prop := sorry

def ty.ptr := ty.nat wsize.S64

inductive unop.ok : unop → ty → ty → Prop
| neg : unop.ok unop.neg (ty.int wsize.Sinf) (ty.int wsize.Sinf)
| not : unop.ok unop.not ty.bool ty.bool
| bnot {s τ} :
  τ = ty.nat s ∨ (∃ s', τ = ty.int s' ∧ s = wsize.Sinf) →
  unop.ok (unop.bnot s) τ τ

def ty.numeric : ty → Prop
| (ty.nat _) := true
| (ty.int _) := true
| _ := false

mutual inductive ty.uninhabited, prop.uninhabited, pexp.uninhabited
with ty.uninhabited : ty → Prop
| void : ty.uninhabited ty.void
| prop {p} : prop.uninhabited p → ty.uninhabited (ty.prop p)

with prop.uninhabited : prop → Prop
| false : prop.uninhabited prop.false
| anl {p q} : prop.uninhabited p → prop.uninhabited (prop.and p q)
| anr {p q} : prop.uninhabited q → prop.uninhabited (prop.and p q)
| or {p q} : prop.uninhabited p → prop.uninhabited q → prop.uninhabited (prop.or p q)
| sepl {p q} : prop.uninhabited p → prop.uninhabited (prop.sep p q)
| sepr {p q} : prop.uninhabited q → prop.uninhabited (prop.sep p q)
| exl {x t A} : ty.uninhabited t → prop.uninhabited (prop.ex x t A)
| exr {x t A} : prop.uninhabited A → prop.uninhabited (prop.ex x t A)
| pexp {e} : pexp.uninhabited e → prop.uninhabited (prop.pexp e)

with pexp.uninhabited : pexp → Prop
| ff : pexp.uninhabited pexp.ff
| anl {p q} : pexp.uninhabited p → pexp.uninhabited (pexp.binop binop.and p q)
| anr {p q} : pexp.uninhabited q → pexp.uninhabited (pexp.binop binop.and p q)
| or {p q} : pexp.uninhabited p → pexp.uninhabited q → pexp.uninhabited (pexp.binop binop.or p q)
| if_ {h c p q} : pexp.uninhabited p → pexp.uninhabited q → pexp.uninhabited (pexp.if_ h c p q)

inductive binop.ok : binop → ty → ty → ty → Prop
| and : binop.ok binop.and ty.bool ty.bool ty.bool
| or : binop.ok binop.or ty.bool ty.bool ty.bool
| band {τ} : ty.numeric τ → binop.ok binop.band τ τ τ
| bor {τ} : ty.numeric τ → binop.ok binop.bor τ τ τ
| lt {τ₁ τ₂} : ty.numeric τ₁ → ty.numeric τ₂ → binop.ok binop.lt τ₁ τ₂ ty.bool
| le {τ₁ τ₂} : ty.numeric τ₁ → ty.numeric τ₂ → binop.ok binop.le τ₁ τ₂ ty.bool
| eq {τ₁ τ₂} : ty.numeric τ₁ → ty.numeric τ₂ → binop.ok binop.eq τ₁ τ₂ ty.bool

mutual inductive arg.ok, ty.ok, prop.ok, pexp.ok
with arg.ok : ctx → arg → Prop
| var {Γ x γ τ} : ty.ok Γ τ → arg.ok Γ (arg.mk x γ τ)

with ty.ok : ctx → ty → Prop
| void {Γ} : ty.ok Γ ty.void
| unit {Γ} : ty.ok Γ ty.unit
| bool {Γ} : ty.ok Γ ty.bool
| nat {Γ s} : ty.ok Γ (ty.nat s)
| int {Γ s} : ty.ok Γ (ty.int s)
| union {Γ A B} : ty.ok Γ A → ty.ok Γ B → ty.ok Γ (ty.union A B)
| inter {Γ A B} : ty.ok Γ A → ty.ok Γ B → ty.ok Γ (ty.inter A B)
| pair {Γ A B} : ty.ok Γ A → ty.ok Γ B → ty.ok Γ (ty.pair A B)
| sigma {Γ A B} : arg.ok Γ A → ty.ok (Γ.app [A]) B → ty.ok Γ (ty.sigma A B)
| user {Γ U ℓ α τ e} :
  user.type U α ℓ →
  ty.ok Γ τ →
  pexp.ok Γ e (ty.tsubst α τ ℓ) →
  ty.ok Γ (ty.user U τ e)
| prop {Γ A} : prop.ok Γ A → ty.ok Γ (ty.prop A)

with prop.ok : ctx → prop → Prop
| true {Γ} : prop.ok Γ prop.true
| false {Γ} : prop.ok Γ prop.false
| all {Γ:ctx} {τ:ty} {x A} :
  prop.ok (Γ.app [arg.mk x ff τ.core]) A →
  prop.ok Γ (prop.all x τ A)
| ex {Γ:ctx} {τ:ty} {x A} :
  prop.ok (Γ.app [arg.mk x ff τ.core]) A →
  prop.ok Γ (prop.ex x τ A)
| imp {Γ A B} : prop.ok Γ A → prop.ok Γ B → prop.ok Γ (prop.imp A B)
| not {Γ A} : prop.ok Γ A → prop.ok Γ (prop.not A)
| and {Γ A B} : prop.ok Γ A → prop.ok Γ B → prop.ok Γ (prop.and A B)
| or {Γ A B} : prop.ok Γ A → prop.ok Γ B → prop.ok Γ (prop.or A B)

| emp {Γ} : prop.ok Γ prop.emp
| sep {Γ A B} : prop.ok Γ A → prop.ok Γ B → prop.ok Γ (prop.sep A B)
| wand {Γ A B} : prop.ok Γ A → prop.ok Γ B → prop.ok Γ (prop.wand A B)
| pexp {Γ e} : pexp.ok Γ e ty.bool → prop.ok Γ (prop.pexp e)
| eq {Γ e₁ e₂ τ} : pexp.ok Γ e₁ τ → pexp.ok Γ e₂ τ → prop.ok Γ (prop.eq e₁ e₂)
| heap {Γ l v τ} : pexp.ok Γ l ty.ptr → ty.ok Γ τ →
  pexp.ok Γ v (ty.core τ) → prop.ok Γ (prop.heap l v)
| has_ty {Γ e τ} : ty.ok Γ τ →
  pexp.ok Γ e (ty.core τ) → prop.ok Γ (prop.has_ty e τ)

with pexp.ok : ctx → pexp → ty → Prop
| var {Γ:ctx} {x γ τ} : Γ.get x γ τ → pexp.ok Γ (pexp.var x) τ.core
| star {Γ} : pexp.ok Γ pexp.star ty.unit
| tt {Γ} : pexp.ok Γ pexp.tt ty.bool
| ff {Γ} : pexp.ok Γ pexp.ff ty.bool
| nat {Γ s n} : wsize.nat_ok s n → pexp.ok Γ (pexp.const (n:ℕ)) (ty.nat s)
| int {Γ s n} : wsize.int_ok s n → pexp.ok Γ (pexp.const n) (ty.int s)
| neg {Γ e} : pexp.ok Γ e (ty.int wsize.Sinf) →
  pexp.ok Γ (pexp.unop unop.neg e) (ty.int wsize.Sinf)
| unop {Γ o e τ τ'} :
  unop.ok o τ τ' →
  pexp.ok Γ e τ →
  pexp.ok Γ (pexp.unop o e) τ'
| binop {Γ o e₁ e₂ τ₁ τ₂ τ'} :
  binop.ok o τ₁ τ₂ τ' →
  pexp.ok Γ e₁ τ₁ →
  pexp.ok Γ e₂ τ₂ →
  pexp.ok Γ (pexp.binop o e₁ e₂) τ'
| if_ {Γ c e₁ e₂ τ} :
  pexp.ok Γ c ty.bool → pexp.ok Γ e₁ τ → pexp.ok Γ e₂ τ →
  pexp.ok Γ (pexp.if_ none c e₁ e₂) τ
| dif {Γ h c e₁ e₂ τ} :
  pexp.ok Γ c ty.bool →
  pexp.ok (Γ.app [arg.mk h ff (ty.prop (prop.pexp c))]) e₁ τ →
  pexp.ok (Γ.app [arg.mk h ff (ty.prop (prop.not (prop.pexp c)))]) e₂ τ →
  pexp.ok Γ (pexp.if_ (some h) c e₁ e₂) τ
| pair {Γ e₁ e₂ τ₁ τ₂} :
  pexp.ok Γ e₁ τ₁ →
  pexp.ok Γ e₂ τ₂ →
  pexp.ok Γ (pexp.pair e₁ e₂) (ty.pair τ₁ τ₂)
| dpair {Γ:ctx} {e₁ e₂ x γ τ B} :
  ty.ok (Γ.app [arg.mk x γ τ]) B →
  pexp.ok Γ e₁ τ →
  pexp.ok Γ e₂ (B.subst x e₁) →
  pexp.ok Γ (pexp.pair e₁ e₂) (ty.sigma (arg.mk x γ τ) B)
| call {Γ:ctx} {f x γ τ τ' e} :
  func.type f (arg.mk x γ τ) τ' →
  pexp.ok Γ e τ →
  pexp.ok Γ (pexp.call f e) (τ'.subst x e)

inductive ctx.ok : ctx → Prop
| nil : ctx.ok ⟨[]⟩
| cons {Γ R} : ctx.ok Γ → arg.ok Γ R → ctx.ok (Γ.app [R])

structure mctx :=
(ctx : ctx)
(labels : alist (λ _:label, arg))
(muts : alist (λ _:var, pexp × ty))

instance : has_coe mctx ctx := ⟨mctx.ctx⟩

def mctx.ok : mctx → Prop
| ⟨Γ, labs, muts⟩ := Γ.ok ∧
  (∀ k x γ τ, labs.lookup k = some (arg.mk x γ τ) → ty.ok Γ τ) ∧
  (∀ x e τ, muts.lookup x = some (e, τ) → pexp.ok Γ e τ)

def mctx.app : mctx → list arg → mctx
| ⟨Γ, labs, muts⟩ R := ⟨Γ.app R, labs, muts⟩

def mctx.appl : mctx → alist (λ _:label, arg) → mctx
| ⟨Γ, labs, muts⟩ ks := ⟨Γ, labs.union ks, muts⟩

def mctx.mut : mctx → var → pexp → ty → mctx
| ⟨Γ, labs, muts⟩ x e τ := ⟨Γ, labs, muts.insert x (e, τ)⟩

def mctx.modify (f : arg → arg) (idx : ℕ) : mctx → mctx
| ⟨Γ, labs, muts⟩ := ⟨Γ.modify f idx, labs, muts⟩

def mctx.move : ℕ → mctx → mctx := mctx.modify arg.core

def mctx.move_all : mctx → mctx
| ⟨⟨Γ⟩, labs, muts⟩ := ⟨⟨Γ.map arg.core⟩, labs, muts⟩

def ty.sigmas : list arg → ty
| [] := ty.unit
| (A::R) := ty.sigma A (ty.sigmas R)

def pexp.pairs : list pexp → pexp
| [] := pexp.star
| (e::es) := pexp.pair e (pexp.pairs es)

inductive mctx.merge : mctx → mctx → Prop
| refl {Γ} : mctx.merge Γ Γ
| trans {Γ₁ Γ₂ Γ₃} : mctx.merge Γ₁ Γ₂ → mctx.merge Γ₂ Γ₃ → mctx.merge Γ₁ Γ₃
| drop {Γ : mctx} {R} :
  (∀ i e τ, Γ.muts.lookup i = some (e, τ) → pexp.ok Γ e τ) →
  mctx.merge (Γ.app R) Γ
| drop_label {Γ : mctx} {ks} : mctx.merge (Γ.appl ks) Γ
| move {Γ i} : mctx.merge Γ (Γ.move i)
| mut {Γ : mctx} {R : list arg} {es} :
  R.map arg.core <+ Γ.ctx.1.map arg.core →
  R.mmap (λ R:arg, Γ.muts.lookup R.var) = some es →
  pexp.ok Γ (pexp.pairs (es.map prod.fst)) (ty.sigmas R) →
  mctx.merge Γ ⟨Γ.ctx, Γ.labels, list.foldr alist.erase Γ.muts (R.map arg.var)⟩

mutual inductive exp.ok_merge, exp.ok
with exp.ok_merge : mctx → exp → ty → mctx → Prop
| mk {Γ e τ Γ' Γ''} :
  exp.ok Γ e τ Γ' → mctx.merge Γ' Γ'' → exp.ok_merge Γ e τ Γ''

with exp.ok : mctx → exp → ty → mctx → Prop
| var {Γ:mctx} {x γ τ} : Γ.1.get x γ τ → exp.ok Γ (exp.var x) τ.core Γ
| star {Γ} : exp.ok Γ exp.star ty.unit Γ
| tt {Γ} : exp.ok Γ exp.tt ty.bool Γ
| ff {Γ} : exp.ok Γ exp.ff ty.bool Γ
| nat {Γ s n} : wsize.nat_ok s n → exp.ok Γ (exp.const (n:ℕ)) (ty.nat s) Γ
| int {Γ s n} : wsize.int_ok s n → exp.ok Γ (exp.const n) (ty.int s) Γ
| neg {Γ Γ' e} : exp.ok Γ e (ty.int wsize.Sinf) Γ' →
  exp.ok Γ (exp.unop unop.neg e) (ty.int wsize.Sinf) Γ'
| unop {Γ o e τ τ' Γ'} :
  unop.ok o τ τ' →
  exp.ok Γ e τ Γ' →
  exp.ok Γ (exp.unop o e) τ' Γ'
| binop {Γ Γ₁ Γ₂ o e₁ e₂ τ₁ τ₂ τ'} :
  binop.ok o τ₁ τ₂ τ' →
  exp.ok Γ e₁ τ₁ Γ₁ →
  exp.ok Γ₁ e₂ τ₂ Γ₂ →
  exp.ok Γ₂ (exp.binop o e₁ e₂) τ' Γ₂
| if_ {Γ Γ' Γ'' c e₁ e₂ τ} :
  exp.ok Γ c ty.bool Γ' → exp.ok_merge Γ' e₁ τ Γ'' → exp.ok Γ' e₂ τ Γ'' →
  exp.ok Γ (exp.if_ none c e₁ e₂) τ Γ''
| dif {Γ Γ' : mctx} {h c e₁ e₂ τ} :
  pexp.ok Γ c ty.bool →
  let A := arg.mk h ff (ty.prop (prop.pexp c)),
      B := arg.mk h ff (ty.prop (prop.not (prop.pexp c))) in
  exp.ok_merge (Γ.app [A]) e₁ τ (Γ'.app [A]) →
  exp.ok_merge (Γ.app [B]) e₂ τ (Γ'.app [B]) →
  exp.ok Γ (exp.if_ (some h) (pexp.to_exp c) e₁ e₂) τ Γ'
| pair {Γ Γ₁ Γ₂ e₁ e₂ τ₁ τ₂} :
  exp.ok Γ e₁ τ₁ Γ₁ →
  exp.ok Γ₁ e₂ τ₂ Γ₂ →
  exp.ok Γ (exp.pair e₁ e₂) (ty.pair τ₁ τ₂) Γ₂
| dpair {Γ Γ₁ Γ₂ : mctx} {e₁ e₂ x γ τ B} :
  ty.ok (Γ.app [arg.mk x γ τ]) B →
  exp.ok Γ (pexp.to_exp e₁) τ Γ₁ →
  exp.ok Γ₁ e₂ (B.subst x e₁) Γ₂ →
  exp.ok Γ (exp.pair (pexp.to_exp e₁) e₂) (ty.sigma (arg.mk x γ τ) B) Γ₂
| func {Γ Γ' f x γ τ τ' e} :
  func.type f (arg.mk x γ τ) τ' →
  exp.ok Γ (pexp.to_exp e) τ Γ' →
  exp.ok Γ (exp.call f (pexp.to_exp e)) (τ'.subst x e) Γ'

| proc {Γ Γ' : mctx} {f x γ τ τ' e} :
  proc.type f (arg.mk x γ τ) τ' →
  (∀ e, τ'.subst x e = τ') →
  exp.ok Γ e τ Γ' →
  exp.ok Γ (exp.call f e) τ' Γ'
| let_ {Γ Γ' Γ'' : mctx} {R t e₁ e₂ τ τ'} :
  exp.ok Γ e₁ τ Γ' →
  tuple_pat.ok Γ' t τ R →
  ty.ok ↑Γ'' τ' →
  exp.ok_merge (Γ'.app R) e₂ τ' (Γ''.app R) →
  exp.ok Γ (exp.let_ none t e₁ e₂) τ' Γ''
| let_hyp {Γ Γ' : mctx} {R h t te e₁ e₂ τ τ'} :
  pexp.ok ↑Γ e₁ τ →
  tuple_pat.ok ↑Γ t τ R →
  tuple_pat.to_pexp t te →
  ty.ok ↑Γ' τ' →
  let R' := R ++ [arg.mk h ff (ty.prop (prop.eq te e₁))] in
  exp.ok_merge (Γ.app R') e₂ τ' (Γ'.app R') →
  exp.ok Γ (exp.let_ (some h) t (pexp.to_exp e₁) e₂) τ' Γ'
| mut {Γ Γ' Γ'' : mctx} {x γ e₁ e₂ τ τ' τ''} :
  exp.ok Γ (pexp.to_exp e₁) τ Γ' →
  Γ'.1.get x γ τ'' →
  ty.ok ↑Γ'' τ' →
  exp.ok (Γ'.mut x e₁ τ) e₂ τ' Γ'' →
  exp.ok Γ (exp.mut none (place.var x) (pexp.to_exp e₁) e₂) τ' Γ''
| unreachable {Γ Γ' e τ τ'} :
  ty.uninhabited τ →
  exp.ok Γ e τ Γ' →
  ty.ok Γ τ' →
  exp.ok Γ (exp.unreachable e) τ' Γ
| label {Γ Γ' : mctx} {ls : list (label × arg × exp)} {ks : alist (λ _:label,arg)} {e τ} :
  ks.entries = ls.map (λ p, ⟨p.1, p.2.1⟩) →
  (∀ k R e, (k,R,e) ∈ ls →
    let Γ₁ := (Γ.move_all.appl ks).app [R] in
    exp.ok_merge Γ₁ e ty.void Γ₁.move_all) →
  exp.ok (Γ.appl ks) e τ Γ' →
  exp.ok Γ (exp.label ls e) τ Γ'
| goto {Γ Γ' : mctx} {k e τ τ' x γ} :
  Γ.labels.lookup k = some (arg.mk x γ τ) →
  exp.ok_merge Γ e τ Γ' →
  ty.ok Γ τ' →
  exp.ok Γ (exp.goto k e) τ' Γ

| entail {Γ Γ' p q A B} :
  exp.ok Γ p (ty.prop A) Γ' →
  pure_proof.ok q A B →
  exp.ok Γ (exp.entail p q) (ty.prop B) Γ'
| assert {Γ Γ' e} :
  exp.ok Γ (pexp.to_exp e) ty.bool Γ' →
  exp.ok Γ (exp.assert (pexp.to_exp e)) (ty.prop (prop.pexp e)) Γ'
| typeof {Γ e τ Γ'} :
  exp.ok Γ (pexp.to_exp e) τ Γ' →
  exp.ok Γ (exp.typeof (pexp.to_exp e)) (ty.prop (prop.has_ty e τ)) Γ'

end mmc
