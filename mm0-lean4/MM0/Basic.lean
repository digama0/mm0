noncomputable section
namespace MMCC

def Var := Nat

def RegNum := Fin 16 deriving LT
def RSP : RegNum := (4 : Fin 16)
def Int.toUInt64 (n : Int) : UInt64 :=
  (n.emod UInt64.size).toNat.toUInt64

def textStart : UInt64 := 0x400078

instance : Coe String (List UInt8) := ⟨fun s => s.toUTF8.toList⟩

axiom Heap : Type

axiom SProp : Type

axiom Result : Type

axiom UInt64.bytes : UInt64 → List UInt8

axiom Result.ok : SProp → Result → Prop
axiom SProp.false : SProp
axiom SProp.emp : SProp
axiom SProp.heap : Heap → SProp
axiom SProp.sep : SProp → SProp → SProp
axiom SProp.and : SProp → SProp → SProp
axiom SProp.or : SProp → SProp → SProp
axiom SProp.lift : Prop → SProp

instance : Coe Prop SProp := ⟨SProp.lift⟩
infixl:72 " ∗ " => SProp.sep
infixl:70 " ∧ₛ " => SProp.and
infixl:70 " ∨ₛ " => SProp.or

axiom SProp.exists : ∀ {α}, (α → SProp) → SProp
notation:75 "∃ₛ " x ", " p => SProp.exists fun x => p

axiom SProp.reg : RegNum → Nat → SProp
infix:80 " ↦ᵣ " => SProp.reg

axiom SProp.code : UInt64 → List UInt8 → SProp
infix:80 " ↦ᶜ " => SProp.code

axiom SProp.block : UInt64 → List UInt8 → SProp
infix:80 " ↦ " => SProp.block

axiom SProp.ip : UInt64 → SProp
prefix:80 "RIP ↦ " => SProp.ip
axiom SProp.flagsNone : SProp
notation "flags ↦ -" => SProp.flagsNone

axiom SProp.blockS (lo a n : Nat) : SProp
notation:80 a " ↦[" lo "] -×" n:80 => SProp.blockS lo a n

axiom SProp.OK : SProp

def Valuation := Var → Nat
def VProp := Valuation → SProp
def VProp.emp : VProp := fun _ => .emp
def Ty := Valuation → Nat → SProp
def Expr := Valuation → Nat
def Ty.unit : Ty := fun _ _ => .emp
def Ty.false : Ty := fun _ _ => .false
def asTy (P : VProp) : Ty := fun vs _ => P vs
def isTyped (e : Expr) (ty : Ty) : VProp := fun vs => ty vs (e vs)
def isHyp (ty : Ty) : VProp := fun vs => ty vs 0
def Ty.typed (e : Expr) (ty : Ty) : Ty := asTy (isTyped e ty)
def eVar (v : Var) : Expr := fun vs => vs v
axiom Ty.moved : Ty → Ty

inductive ReturnABI
  | noRet

axiom ReturnABI.returnType : ReturnABI → SProp

inductive Epilogue
  | free : Nat → Epilogue → Epilogue
  | pop : RegNum → Epilogue → Epilogue
  | ret : Epilogue

def Epilogue.value : Epilogue → Option (List RegNum × Nat)
  | .ret => some ([], 0)
  | .free n epi => do
    let (regs, 0) ← epi.value | none
    unless n != 0 do none
    some (regs, n)
  | .pop reg epi => do
    let (regs, 0) ← epi.value | none
    some (reg :: regs, 0)

structure Epilogue' where
  val : Epilogue
  regs : List RegNum
  sp : Nat
  ok : val.value = some (regs, sp)

structure GCtx where
  content : List UInt8
  fileSz : UInt64
  memSz : UInt64
  result : Result
  len_eq : content.length = fileSz.toNat
  le : fileSz ≤ memSz
  lt : textStart.toNat + memSz.toNat < UInt64.size

structure PCtx1 where
  ret : ReturnABI
  epi : Epilogue'
  se : Bool

structure PCtx extends GCtx, PCtx1

def BlockLoc := Option UInt64

structure Frame where
  frame : Heap
  retAddr : UInt64
  pushed : List UInt64
  lo : Nat
  top : Nat
  le : lo ≤ top
  lt : top < UInt64.size

def Frame.stackBot (fr : Frame) (sp n : Nat) : SProp :=
  (fr.lo + 2^12 + n ≤ sp) ∧ₛ
  fr.lo ↦[fr.lo] -×(sp - fr.lo)

def Frame.stackLayout'
    (fr : Frame) (n sz : Nat) (pushed : List UInt8) (L : Nat → Nat → SProp) : SProp :=
  let sp := fr.top - pushed.length - sz
  RSP ↦ᵣ sp ∗ fr.stackBot sp n ∗ L fr.lo sp ∗ (sp + sz).toUInt64 ↦ pushed

def Frame.stackLayout (fr : Frame) (n sz : Nat) (L : Nat → Nat → SProp) : SProp :=
  fr.stackLayout' n sz ((fr.pushed ++ [fr.retAddr]).bind UInt64.bytes) L

def mainLayout (content : List UInt8) (ip : UInt64) : SProp :=
  textStart ↦ᶜ content ∗ RIP ↦ ip ∗ SProp.OK ∗ flags ↦ -

def okReturn (pctx : PCtx) (fr : Frame) : Prop :=
  pctx.result.ok <| SProp.heap fr.frame ∗
    (mainLayout pctx.content fr.retAddr ∗
      fr.stackLayout' 8 0 [] (fun _ _ => .emp) ∗
      pctx.ret.returnType)

inductive VCtx where
  | emp
  | var (n : Option Nat) (ty : Ty)
  | and (A B : VCtx)

def VCtx.eval : VCtx → VProp
  | .emp => .emp
  | .var (some n) ty => isTyped (eVar n) ty
  | .var none ty => isHyp ty
  | .and A B => fun vs => A.eval vs ∗ B.eval vs

inductive VCtx.OK1 : VCtx → Prop where
  | var : VCtx.OK1 (.var n ty)
  | and : VCtx.OK1 A → VCtx.OK1 B → VCtx.OK1 (.and A B)

inductive VCtx.OK : VCtx → Prop where
  | emp : VCtx.OK .emp
  | nonempty : VCtx.OK1 A → VCtx.OK A

inductive VCtx.push : VCtx → VCtx → VCtx → Prop where
  | one : VCtx.push .emp A A
  | suc : VCtx.push vctx A (.and vctx A)
  | rot : VCtx.push vctx ty (.and (.and A B) C) → VCtx.push vctx ty (.and A (.and B C))

inductive VCtx.get : VCtx → VCtx → Prop where
  | push : VCtx.push A ty A' → VCtx.get A' ty
  | l : VCtx.get A ty → VCtx.get (.and A B) ty
  | r : VCtx.get B ty → VCtx.get (.and A B) ty
  | rot : VCtx.get (.and (.and A B) C) ty → VCtx.get (.and A (.and B C)) ty

inductive isMoved : Ty → Ty → Prop where

inductive VCtx.take : VCtx → VCtx → VCtx → Prop where
  | move : isMoved ty moved → VCtx.take (.var n ty) (.var n ty) (.var n moved)
  | ref : isMoved ty moved → VCtx.take (.var n ty) (.var n moved) (.var n ty)
  | l : VCtx.take A ty A' → VCtx.take (.and A B) ty (.and A' B)
  | r : VCtx.take B ty B' → VCtx.take (.and A B) ty (.and A B')

inductive StackLayout where
  | emp
  | pad (off n : Nat)
  | and (A B : StackLayout)

def StackLayout.eval : StackLayout → Valuation → Nat → Nat → SProp
  | .emp, _, _, _ => .emp
  | .pad off n, _, lo, sp => (sp + off) ↦[lo] -×n
  | .and A B, vs, lo, sp => A.eval vs lo sp ∗ B.eval vs lo sp

inductive MCtx where
  | emp
  | free (r : RegNum)
  | stkFree (off n : Nat)
  | reg (reg : RegNum) (val : Expr)
  | and (A B : MCtx)

def MCtx.lctx : MCtx → Valuation → SProp
  | .emp, _ => .emp
  | .free r, _ => ∃ₛ v, r ↦ᵣ v
  | .stkFree _ _, _ => .emp
  | .reg r val, vs => r ↦ᵣ val vs
  | .and A B, vs => A.lctx vs ∗ B.lctx vs

def MCtx.mctx : MCtx → StackLayout
  | .emp => .emp
  | .free _ => .emp
  | .stkFree off n => .pad off n
  | .reg _ _ => .emp
  | .and A B => .and A.mctx B.mctx

inductive MCtx.OKReg : MCtx → RegNum → RegNum → Prop where
  | emp : MCtx.OKReg .emp (0:Fin _) (0:Fin _)
  | free : MCtx.OKReg (.free r) r r
  | reg : MCtx.OKReg (.reg r v) r r
  | and : MCtx.OKReg A a b → b < c → MCtx.OKReg A c d → MCtx.OKReg (A.and B) a d

inductive MCtx.OKStack : MCtx → Prop where

inductive MCtx.OK : MCtx → Prop where
  | nostack : MCtx.OKReg A a b → OK A
  | stack : MCtx.OKReg A a b → MCtx.OKStack B → OK (.and A B)

structure TCtx where
  vctx : VCtx
  vctxSz : Nat
  mctx : MCtx

def TCtx.type (tctx : TCtx) : VProp :=
  fun vs => tctx.vctx.eval vs ∗ tctx.mctx.lctx vs

def TCtx.layout (tctx : TCtx) : StackLayout := tctx.mctx.mctx

inductive TCtx.pushVar : TCtx → Ty → TCtx → Prop where
  | mk {vctx mctx} : VCtx.push vctx (.var (some sz) ty) vctx' →
    TCtx.pushVar ⟨vctx, sz, mctx⟩ ty ⟨vctx', sz + 1, mctx⟩

inductive TCtx.pushHyp : TCtx → Ty → TCtx → Prop where
  | mk {vctx mctx} : VCtx.push vctx (.var none ty) vctx' →
    TCtx.pushHyp ⟨vctx, sz, mctx⟩ ty ⟨vctx', sz, mctx⟩

inductive TCtx.readHyp : TCtx → Ty → Prop where
  | unit : TCtx.readHyp tctx .unit
  | var {vctx} : vctx.get (.var n ty) → TCtx.readHyp ⟨vctx, n, tctx⟩ ty

axiom Variant : Type
axiom Variant.eval : Variant → Valuation → Nat → Prop

inductive LabelGroup
  | and : LabelGroup → LabelGroup → LabelGroup
  | one : BlockLoc → Variant → TCtx → LabelGroup

def LabelGroup.eval : LabelGroup → Valuation → Nat → List UInt8 → Epilogue' → Frame → Nat → SProp
  | .one x var tctx, vs, v, c, epi, fr, p => (SProp.heap fr.frame ∗
    (match x with
    | some x => mainLayout c (textStart + p.toUInt64 + x)
    | none => ∃ₛ ip, mainLayout c ip) ∗
    var.eval vs v ∗
    fr.stackLayout 8 epi.sp (tctx.layout.eval vs) ∗ tctx.type vs)
  | .and a b, vs, v, c, epi, fr, p => a.eval vs v c epi fr p ∨ₛ b.eval vs v c epi fr p

inductive findLabel : LabelGroup → BlockLoc → Variant → TCtx → Prop
  | one : findLabel (.one x var tctx) x var tctx
  | l : findLabel A x var tctx → findLabel (.and A B) x var tctx
  | r : findLabel B x var tctx → findLabel (.and A B) x var tctx

def LabelGroups := List (Expr × LabelGroup)

def LabelGroups.eval : LabelGroups → List UInt8 → Epilogue' → Frame → Nat → SProp
  | [], _, _, _, _ => .false
  | (var, ls) :: labs, c, epi, fr, p =>
    (∃ₛ vs, ls.eval vs (var vs) c epi fr p) ∨ₛ eval labs c epi fr p

structure BCtx extends PCtx where
  labelGroups : LabelGroups

def okCodeN (bctx : BCtx) (tctx : TCtx) (fr : Frame) (ip : Nat) : Prop :=
  bctx.result.ok <| SProp.heap fr.frame ∗ (
    mainLayout bctx.content (textStart + ip.toUInt64) ∗
    ∃ₛ vs, fr.stackLayout 8 bctx.epi.sp (tctx.layout.eval vs) ∗ tctx.type vs)

inductive LAsm where
  | nil
  | at (x : Nat) (A : LAsm)
  | entry (p : Nat) (A : LAsm)
  | seq (A B : LAsm)

inductive LAsm.eval : LAsm → Nat → List UInt8 → Nat → Prop
  | nil : eval .nil p [] x
  | at : eval A p s x → eval (.at x A) p s x
  | entry : eval A p s x → eval (.entry p A) p s x
  | seq : eval A p t₁ x → eval B p t₂ (x + t₁.length) → eval (.seq A B) p (t₁ ++ t₂) x

inductive GAsm where
  | proc (p : Nat) (A : LAsm)
  | seq (A B : GAsm)

inductive GAsm.eval : GAsm → List UInt8 → Nat → Prop
  | proc : A.eval p t₁ 0 → t₁ ≠ [] → eval (.proc p A) (t₁ ++ t₂) x
  | seq : eval A t₁ x → eval B t₂ (x + t₁.length) → eval (.seq A B) (t₁ ++ t₂) x

def sublistAt (n : Nat) (L₁ L₂ : List α) : Prop := ∃ l r, L₁ = l ++ L₂ ++ r ∧ l.length = n

def okScope (bctx : BCtx) (fr : Frame) (p : Nat) : Prop :=
  okReturn bctx.toPCtx fr ∧ bctx.epi.regs.length = fr.pushed.length ∧
  bctx.result.ok (bctx.labelGroups.eval bctx.content bctx.epi fr p)

def okAsmd (bctx : BCtx) (code : LAsm) (p x y : Nat) : Prop :=
  ∃ s, y = x + s.length ∧ textStart.toNat + p + y < UInt64.size ∧
    sublistAt (p + x) bctx.content s ∧ code.eval p s x

def okCode (bctx : BCtx) (tctx : TCtx) (code : LAsm) (tctx' : TCtx) : Prop :=
  ∀ p x y fr, okAsmd bctx code p x y → okScope bctx fr p →
    okCodeN bctx tctx' fr (p + y) → okCodeN bctx tctx fr (p + x)
