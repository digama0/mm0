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

inductive EpilogueR where
  | pop : RegNum → EpilogueR → EpilogueR
  | ret : EpilogueR

inductive Epilogue where
  | free : Nat → EpilogueR → Epilogue
  | nostack : EpilogueR → Epilogue

def EpilogueR.regs : EpilogueR → List RegNum
  | .ret => []
  | .pop reg epi => reg :: epi.regs

def Epilogue.regs : Epilogue → List RegNum
  | .free _ epi | .nostack epi => epi.regs

def Epilogue.sp : Epilogue → Nat
  | .free n _ => n
  | .nostack _ => 0

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
  epi : Epilogue
  se : Bool

structure PCtx extends GCtx, PCtx1

def BlockLoc := Option Nat

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

@[match_pattern] def VCtx.hyp := VCtx.var none

def VCtx.eval : VCtx → VProp
  | .emp => .emp
  | .var (some n) ty => isTyped (eVar n) ty
  | .hyp ty => isHyp ty
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

inductive MCtxR where
  | emp
  | false
  | free (r : RegNum)
  | reg (reg : RegNum) (val : Expr)
  | and (A B : MCtxR)

inductive MCtxR.OK : MCtxR → RegNum → RegNum → Prop where
  | emp : MCtxR.OK .emp (0:Fin _) (0:Fin _)
  | free : MCtxR.OK (.free r) r r
  | reg : MCtxR.OK (.reg r v) r r
  | and : MCtxR.OK A a b → b < c → MCtxR.OK A c d → MCtxR.OK (A.and B) a d

def MCtxR.eval : MCtxR → Valuation → SProp
  | .emp, _ => .emp
  | .false, _ => .false
  | .free r, _ => ∃ₛ v, r ↦ᵣ v
  | .reg r val, vs => r ↦ᵣ val vs
  | .and A B, vs => A.eval vs ∗ B.eval vs

inductive MCtxS where
  | free (off n : Nat)
  | and (A B : MCtxS)

inductive MCtx where
  | nostack : MCtxR → MCtx
  | stack : MCtxR → MCtxS → MCtx

def MCtx.R : MCtx → MCtxR
  | .nostack r | .stack r _ => r

def MCtxS.layout : MCtxS → StackLayout
  | .free off n => .pad off n
  | .and A B => .and A.layout B.layout

def MCtx.layout : MCtx → StackLayout
  | .nostack _ => .emp
  | .stack _ s => s.layout

inductive MCtxS.OK : MCtxS → Prop where

inductive MCtx.OK : MCtx → Prop where
  | nostack : MCtxR.OK A a b → OK (.nostack A)
  | stack : MCtxR.OK A a b → MCtxS.OK B → OK (.stack A B)

inductive MCtxR.push : MCtxR → MCtxR → MCtxR → Prop
  | emp : MCtxR.push .emp A A
  | oneL : MCtxR.push A B (.and B A)
  | oneR : MCtxR.push A B (.and A B)
  | R : MCtxR.push B val B' → MCtxR.push (.and A B) val (.and A B')
  | L : MCtxR.push A val A' → MCtxR.push (.and A B) val (.and A' B)
  | rotL : MCtxR.push M val (.and A (.and B C)) → MCtxR.push M val (.and (.and A B) C)
  | rotR : MCtxR.push M val (.and (.and A B) C) → MCtxR.push M val (.and A (.and B C))

inductive MCtxS.push : MCtxS → MCtxS → MCtxS → Prop
  | oneL : MCtxS.push A B (.and B A)
  | oneR : MCtxS.push A B (.and A B)
  | R : MCtxS.push B val B' → MCtxS.push (.and A B) val (.and A B')
  | L : MCtxS.push A val A' → MCtxS.push (.and A B) val (.and A' B)
  | rotL : MCtxS.push M val (.and A (.and B C)) → MCtxS.push M val (.and (.and A B) C)
  | rotR : MCtxS.push M val (.and (.and A B) C) → MCtxS.push M val (.and A (.and B C))

inductive MCtxInsert where
  | free (r : RegNum)
  | reg (reg : RegNum) (val : Expr)
  | stkFree (off n : Nat)

inductive MCtx.push : MCtx → MCtxR ⊕ MCtxS → MCtx → Prop
  | reg : MCtxR.push A val A' → MCtx.push (.nostack A) (.inl val) (.nostack A')
  | reg' : MCtxR.push A val A' → MCtx.push (.stack A B) (.inl val) (.stack A' B)
  | stk0 : MCtx.push (.nostack A) (.inr val) (.stack A val)
  | stk : MCtxS.push B val B' → MCtx.push (.stack A B) (.inr val) (.stack A B')

structure TCtx where
  vctx : VCtx
  vctxSz : Nat
  mctx : MCtx

def TCtx.type (tctx : TCtx) : VProp :=
  fun vs => tctx.vctx.eval vs ∗ tctx.mctx.R.eval vs

def TCtx.layout (tctx : TCtx) : StackLayout := tctx.mctx.layout

inductive TCtx.pushVar : TCtx → Ty → TCtx → Prop where
  | mk {vctx mctx} : VCtx.push vctx (.var (some sz) ty) vctx' →
    TCtx.pushVar ⟨vctx, sz, mctx⟩ ty ⟨vctx', sz + 1, mctx⟩

inductive TCtx.pushHyp : TCtx → Ty → TCtx → Prop where
  | mk {vctx mctx} : VCtx.push vctx (.var none ty) vctx' →
    TCtx.pushHyp ⟨vctx, sz, mctx⟩ ty ⟨vctx', sz, mctx⟩

inductive TCtx.readHyp : TCtx → Ty → Prop where
  | unit : TCtx.readHyp tctx .unit
  | var {vctx} : vctx.get (.var n ty) → TCtx.readHyp ⟨vctx, n, tctx⟩ ty

def TCtx.false : TCtx where
  vctx := .hyp .false
  vctxSz := 0
  mctx := .nostack .false

axiom Variant : Type
axiom Variant.eval : Variant → Valuation → Nat → Prop

inductive LabelGroup
  | and : LabelGroup → LabelGroup → LabelGroup
  | one : BlockLoc → Variant → TCtx → LabelGroup

def okCodeP (c : List UInt8) (epi : Epilogue) (tctx : TCtx)
    (fr : Frame) (p : Nat) (ip : BlockLoc) (vs : Valuation) : SProp :=
  SProp.heap fr.frame ∗ (
    (match ip with
    | some x => mainLayout c (textStart + p.toUInt64 + x.toUInt64)
    | none => ∃ₛ ip, mainLayout c ip) ∗
    fr.stackLayout 8 epi.sp (tctx.layout.eval vs) ∗ tctx.type vs)

def LabelGroup.eval : LabelGroup → Valuation → Nat → List UInt8 → Epilogue → Frame → Nat → SProp
  | .one ip var tctx, vs, v, c, epi, fr, p => var.eval vs v ∗ okCodeP c epi tctx fr p ip vs
  | .and a b, vs, v, c, epi, fr, p => a.eval vs v c epi fr p ∨ₛ b.eval vs v c epi fr p

inductive findLabel : LabelGroup → BlockLoc → Variant → TCtx → Prop
  | one : findLabel (.one x var tctx) x var tctx
  | l : findLabel A x var tctx → findLabel (.and A B) x var tctx
  | r : findLabel B x var tctx → findLabel (.and A B) x var tctx

def LabelGroups := List (Expr × LabelGroup)

def LabelGroups.eval : LabelGroups → List UInt8 → Epilogue → Frame → Nat → SProp
  | [], _, _, _, _ => .false
  | (var, ls) :: labs, c, epi, fr, p =>
    (∃ₛ vs, ls.eval vs (var vs) c epi fr p) ∨ₛ eval labs c epi fr p

inductive findLabels : LabelGroups → Expr → LabelGroup → Prop
  | one : findLabels ((var, ls) :: labs) var ls
  | cons : findLabels labs var ls → findLabels ((var', ls') :: labs) var ls

structure BCtx extends PCtx where
  labelGroups : LabelGroups

def okCodeN (bctx : BCtx) (tctx : TCtx) (fr : Frame) (p : Nat) (ip : BlockLoc) : Prop :=
  bctx.result.ok <| ∃ₛ vs, okCodeP bctx.content bctx.epi tctx fr p ip vs

inductive IRM where
  | reg : RegNum → IRM
  | imm32 : UInt32 → IRM

inductive Size where
  | sz64
instance : OfNat Size 64 := ⟨.sz64⟩

axiom Inst : Type
axiom Inst.push : IRM → Inst
axiom Inst.pop : RegNum → Inst
axiom Inst.ret : Inst
axiom Inst.sub : Size → RegNum → IRM → Inst
axiom Inst.add : Size → RegNum → IRM → Inst
axiom Inst.jump : Nat → Inst

axiom Inst.eval : Inst → Nat → List UInt8 → Nat → Prop

inductive LAsm where
  | nil
  | inst (_ : Inst)
  | at (x : Nat) (A : LAsm)
  | entry (p : Nat) (A : LAsm)
  | seq (A B : LAsm)

inductive LAsm.eval : LAsm → Nat → List UInt8 → Nat → Prop
  | nil : eval .nil p [] x
  | inst : I.eval p s x → eval (.inst I) p s x
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

def okCode.sema (bctx : BCtx) (tctx : TCtx) (code : LAsm) (tctx' : TCtx) : Prop :=
  ∀ p x y fr, okAsmd bctx code p x y → okScope bctx fr p →
    okCodeN bctx tctx' fr p (some y) → okCodeN bctx tctx fr p (some x)

inductive okPrologue :
    (epi : EpilogueR) → (mctx : MCtxR) →
    (code : LAsm) → (epi' : Epilogue) → (mctx' : MCtx) → Prop
  | push :
    MCtxR.push mctx₁ (.free r) mctx₂ →
    okPrologue (.pop r epi) mctx₂ code epi' mctx₃ →
    okPrologue epi mctx₁ (.seq (.inst (.push (.reg r))) code) epi' mctx₃
  | alloc0 : MCtxR.OK mctx a b → okPrologue epi mctx .nil (.nostack epi) (.nostack mctx)
  | alloc : MCtxR.OK mctx a b → n.toNat ≤ 2^12-8 →
    okPrologue epi mctx (.inst (.sub 64 RSP (.imm32 n)))
      (.free n.toNat epi) (.stack mctx (.free 0 n.toNat))

axiom assembled : GCtx → GAsm → Prop

inductive okAssembled : PCtx → LAsm → Prop
  | I : assembled pctx.toGCtx (.proc start code) → okAssembled pctx code
  | l : okAssembled pctx (.seq A B) → okAssembled pctx A
  | r : okAssembled pctx (.seq A B) → okAssembled pctx B

inductive Arg where
  | var (ty : Ty)
  | hyp (ty : Ty)

inductive Args where
  | nil
  | snoc (a : Args) (b : Arg)

inductive accumArgs : Args → VCtx → Nat → Prop
  | nil : accumArgs .nil .emp 0
  | var :
    accumArgs args vtcx n →
    VCtx.push vtcx (.var (some n) ty) vctx' →
    accumArgs (.snoc args (.var ty)) vtcx' (n+1)
  | hyp :
    accumArgs args vtcx n →
    VCtx.push vtcx (.hyp ty) vctx' →
    accumArgs (.snoc args (.hyp ty)) vtcx' n

structure ArgsM where
  args : Args
  mctx : MCtxR

def Clobbers := List RegNum
inductive accumClob : Clobbers → MCtxR → MCtxR → Prop
  | nil : accumClob [] mctx mctx
  | cons : MCtxR.push mctx₁ (.free r) mctx₁ →
    accumClob clob mctx₂ mctx₃ → accumClob (r :: clob) mctx₁ mctx₃

axiom checkRet : BCtx → TCtx → ReturnABI → Prop

def EpilogueR.toCode : EpilogueR → LAsm
  | .ret => .inst .ret
  | .pop r epi => .seq (.inst (.pop r)) epi.toCode

def Epilogue.toCode : Epilogue → LAsm
  | .nostack epi => epi.toCode
  | .free n epi => .seq (.inst (.add 64 RSP (.imm32 n.toUInt32))) epi.toCode

inductive getEpi : BCtx → ReturnABI → LAsm → Prop
  | mk : getEpi ⟨⟨gctx, ret, epi, se⟩, labs⟩ ret epi.toCode

inductive okPushVariant : Expr → Variant → TCtx → TCtx → Prop

inductive variantValue : Variant → Expr → Prop

mutual

inductive addLabels : BCtx → LabelGroup → LabelGroup → Prop
  | and : addLabels bctx ls A → addLabels bctx ls B → addLabels bctx ls (.and A B)
  | none :
    variantValue var val →
    okCode ⟨bctx, (val, ls) :: L⟩ tctx .nil .false →
    addLabels ⟨bctx, L⟩ ls (.one none var tctx)
  | some :
    okAssembled pctx (.at ip code) →
    variantValue var val →
    okCode ⟨bctx, (val, ls) :: L⟩ tctx code .false →
    addLabels ⟨bctx, L⟩ ls (.one (some ip) var tctx)

inductive okLabels : BCtx → LabelGroup → Prop
  | l : okLabels bctx (.and A B) → okLabels bctx A
  | r : okLabels bctx (.and A B) → okLabels bctx B
  | mk : addLabels bctx ls ls → okLabels bctx ls

inductive okBlock : BCtx → BlockLoc → TCtx → Prop
  | weak : okCode bctx tctx .nil tctx' → okBlock bctx ip tctx' → okBlock bctx ip tctx
  | mk : okAssembled bctx.toPCtx (.at ip code) →
    okCode bctx tctx code .false → okBlock bctx (some ip) tctx
  | unreachable : okCode bctx tctx .nil .false → okBlock bctx none tctx
  | label :
    findLabels L var1 ls →
    findLabel ls ip var2 tctx →
    okPushVariant var1 var2 tctx tctx' →
    okBlock ⟨pctx, L⟩ ip tctx'
  | ofLabel : okLabels bctx (.one ip var tctx) → okBlock bctx ip tctx

inductive okCode : BCtx → TCtx → LAsm → TCtx → Prop
  | epilogue : getEpi bctx ret code → checkRet bctx tctx ret → okCode bctx tctx code .false
  | jump : okBlock bctx (some tgt) tctx → okCode bctx tctx (.inst (.jump tgt)) .false

end

inductive okProc : GCtx → Nat → ArgsM → ReturnABI → List RegNum → Bool → Prop
  | mk :
    okAssembled pctx (.entry start (.seq prol code)) →
    accumArgs args vctx₁ sz₁ →
    accumClob clob mctx₁ mctx₂ →
    okPrologue .ret mctx₂ prol pctx.epi mctx₃ →
    okCode ⟨pctx, []⟩ ⟨vctx₁, sz₁, mctx₃⟩ code .false →
    okProc pctx.toGCtx start ⟨args, mctx₁⟩ pctx.ret clob pctx.se

inductive buildStart : GCtx → PCtx → TCtx → Prop
  | mk : buildStart gctx ⟨gctx, .noRet, .nostack .ret, true⟩ ⟨.emp, 0, .nostack .emp⟩

inductive okStart : GCtx → Prop
  | mk :
    okAssembled pctx (.entry start (.seq .nil code)) →
    buildStart gctx pctx tctx →
    okCode ⟨pctx, []⟩ tctx code .false →
    okStart gctx
