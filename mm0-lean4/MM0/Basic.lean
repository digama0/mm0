noncomputable section

inductive List.Forall₂ (R : α → β → Prop) : List α → List β → Prop
  | nil : Forall₂ R [] []
  | cons {a b l₁ l₂} : R a b → Forall₂ R l₁ l₂ → Forall₂ R (a :: l₁) (b :: l₂)

namespace MMCC

abbrev u8 := UInt8
abbrev u64 := UInt64
axiom encodeList : List Nat → Nat
axiom decodeList : Nat → List Nat

def sublistAt (n : Nat) (L₁ L₂ : List α) : Prop := ∃ l r, L₁ = l ++ L₂ ++ r ∧ l.length = n

def Var := Nat

def RegNum := Fin 16 deriving LT
def RSP : RegNum := (4 : Fin 16)
def Int.toUInt64 (n : Int) : u64 :=
  (n.emod UInt64.size).toNat.toUInt64

def textStart : u64 := 0x400078

instance : Coe String (List u8) := ⟨fun s => s.toUTF8.toList⟩

axiom Heap : Type

axiom SProp : Type

axiom Result : Type

axiom UInt64.bytes : u64 → List u8

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
axiom SProp.bigsep : ∀ {α}, (α → SProp) → SProp
notation:75 "Xₛ " x ", " p => SProp.bigsep fun x => p

axiom SProp.reg : RegNum → u64 → SProp
infix:80 " ↦ᵣ " => SProp.reg

axiom SProp.code : u64 → List u8 → SProp
infix:80 " ↦ᶜ " => SProp.code

axiom SProp.block : u64 → List u8 → SProp
infix:80 " ↦ " => SProp.block

axiom SProp.ip : u64 → SProp
prefix:80 "RIP ↦ " => SProp.ip
axiom SProp.flagsNone : SProp
notation "flags ↦ -" => SProp.flagsNone

axiom SProp.blockS (lo a n : Nat) : SProp
notation:80 a " ↦[" lo "] -×" n:80 => SProp.blockS lo a n

axiom SProp.OK : SProp

inductive Base where
  | zero
  | rip
  | reg (_ : RegNum)

inductive IRM where
  | reg : RegNum → IRM
  | mem : Nat → Base → Nat → IRM
  | imm32 : Int → IRM

inductive Size where
  | sz8
  | sz64
instance : OfNat Size 8 := ⟨.sz8⟩
instance : OfNat Size 64 := ⟨.sz64⟩

def Size.bytes : Size → Nat
  | .sz8 => 1
  | .sz64 => 8

axiom Inst : Type
axiom Inst.push : IRM → Inst
axiom Inst.pop : RegNum → Inst
axiom Inst.ret : Inst
axiom Inst.sub : Size → RegNum → IRM → Inst
axiom Inst.add : Size → RegNum → IRM → Inst
axiom Inst.jump : Nat → Inst
axiom Inst.mov : Size → IRM → IRM → Inst

axiom Inst.eval : Inst → Nat → List u8 → Nat → Prop

inductive LAsm where
  | nil
  | inst (_ : Inst)
  | at (x : Nat) (A : LAsm)
  | entry (p : Nat) (A : LAsm)
  | seq (A B : LAsm)

inductive LAsm.eval : LAsm → Nat → List u8 → Nat → Prop where
  | nil : eval .nil p [] x
  | inst : I.eval p s x → eval (.inst I) p s x
  | at : eval A p s x → eval (.at x A) p s x
  | entry : eval A p s x → eval (.entry p A) p s x
  | seq : eval A p t₁ x → eval B p t₂ (x + t₁.length) → eval (.seq A B) p (t₁ ++ t₂) x

inductive GAsm where
  | proc (p : Nat) (A : LAsm)
  | seq (A B : GAsm)

inductive GAsm.eval : GAsm → List u8 → Nat → Prop where
  | proc : A.eval p t₁ 0 → t₁ ≠ [] → eval (.proc p A) (t₁ ++ t₂) x
  | seq : eval A t₁ x → eval B t₂ (x + t₁.length) → eval (.seq A B) (t₁ ++ t₂) x

structure GCtx where
  content : List u8
  fileSz : u64
  memSz : u64
  result : Result
  len_eq : content.length = fileSz.toNat
  le : fileSz ≤ memSz
  lt : textStart.toNat + memSz.toNat < UInt64.size

axiom assembled : GCtx → GAsm → Prop

def Valuation := Var → Nat

inductive SProp.toMoved : SProp → SProp → Prop where
  | emp : toMoved .emp .emp
  | false : toMoved .false .false
  | sep : toMoved A A' → toMoved B B' → toMoved (A ∗ B) (A' ∗ B')

def VProp := Valuation → SProp

def StackLayout := (lo sp : Nat) → SProp
def OStackLayout := (off sz : Nat) → StackLayout
def StackLayout.emp : StackLayout := fun _ _ => .emp
def StackLayout.pad : OStackLayout := fun off sz lo sp => (sp + off) ↦[lo] -×sz
def StackLayout.val (off : Nat) (P : List u8 → Prop) : StackLayout :=
  fun lo sp => ∃ₛ l, (lo + 2^12 ≤ sp + off ∧ P l) ∧ₛ ∃ₛ h, ⟨sp + off, h⟩ ↦ l
def StackLayout.and (A B : StackLayout) : StackLayout :=
  fun lo sp => A lo sp ∗ B lo sp

def OStackLayout.val (P : List u8 → Prop) : OStackLayout :=
  fun off sz => .val off fun l => l.length = sz ∧ P l
def OStackLayout.seq (A B : OStackLayout) : OStackLayout :=
  fun off sz lo sp => ∃ₛ sz₁, ∃ₛ sz₂,
    (sz = sz₁ + sz₂) ∧ₛ (A off sz₁).and (B (off + sz₁) sz₂) lo sp

def toBytes (k n : Nat) : List u8 :=
  match k with
  | 0 => []
  | k+1 => n.toUInt8 :: toBytes k (n / 256)

def toIBytes (k : Nat) (n : Int) : List u8 :=
  toBytes k (n % (8 * k)).toNat

def encodeInt : Int → Nat
  | .ofNat n => 2 * n
  | .negSucc n => 2 * n + 1

def decodeInt (n : Nat) : Int :=
  if n % 2 = 0 then .ofNat (n / 2) else .negSucc ((n-1) / 2)

inductive Expr where
  | var (v : Var)
  | int (_ : Int)
  | nil
  | list1 (e : Expr)
  | append (a b : Expr)

def Expr.eval : Expr → Valuation → Nat
  | .var v, vs => vs v
  | .int n, _ => encodeInt n
  | .nil, _ => encodeList []
  | .list1 e, vs => encodeList [e.eval vs]
  | .append a b, vs => encodeList (decodeList (a.eval vs) ++ decodeList (b.eval vs))

def Expr.toList : Expr → Option (List Expr)
  | .nil => some []
  | .list1 e => some [e]
  | .append a b => return (← a.toList) ++ (← b.toList)
  | _ => none

def Expr.toIntLit : Expr → Option Int
  | .int n => some n
  | _ => none

def Expr.toNatLit (e : Expr) : Option Nat := do
  if let .ofNat n ← e.toIntLit then some n else none

inductive PExpr where
  | emp
  | list (e : Expr) (p : PExpr)

inductive ZTy where
  | prop (P : VProp)

def ZTy.eval : ZTy → Nat → VProp
  | .prop P, _ => P

inductive ZTy.toMoved : ZTy → ZTy → Prop where
  | prop : (∀ vs, (P vs).toMoved (P' vs)) → toMoved (.prop P) (.prop P')

inductive Ty where
  | zst (_ : ZTy)
  | u8N (N : Nat)
  | i8N (N : Nat)
  | array (ty : Ty) (N : Expr)

def Ty.sizeof : Ty → Option Nat
  | .zst _ => some 0
  | .u8N N | .i8N N => some N
  | .array ty N => return (← ty.sizeof) * (← N.toNatLit)

def Ty.mem : Ty → Nat → VProp
  | .zst z, n, vs => z.eval n vs
  | .u8N N, n, _ | .i8N N, n, _ => n < 256^N
  | .array ty N, n, vs =>
    ((decodeList n).length = N.eval vs) ∧ₛ Xₛ (i : {i // i ∈ decodeList n}), ty.mem i vs

def Ty.layoutReg : Ty → Nat → u64 → Prop
  | .zst _, _, _ => False
  | .u8N _, n, l => n = l.toNat
  | .i8N _, n, l => encodeInt n = (l + .ofNat (2^63)).toNat - 2^63
  | .array ty N, n, l => N.toNatLit = some 1 ∧ ∃ i, decodeList n = [i] ∧ ty.layoutReg i l

def Ty.layout : Ty → Nat → List u8 → Prop
  | .zst _, _, _ => False
  | .u8N N, n, l => toBytes N n = l
  | .i8N N, n, l => toIBytes N (encodeInt n) = l
  | .array ty _, n, l => ty.sizeof.isSome ∧ ∃ ll, (decodeList n).Forall₂ ty.layout ll ∧ l = ll.join

def PExpr.layout : PExpr → Ty → Valuation → List u8 → Prop
  | .emp, _ => fun _ l => l = []
  | .list e p, .array ty₁ _ => fun vs l =>
    ∃ es l₂ ll, e.toList = some es ∧
      es.Forall₂ (fun e => ty₁.layout (e.eval vs)) ll ∧
      p.layout ty₁ vs l₂ ∧ l = ll.join ++ l₂
  | .list .., _ => fun _ _ => False

def PExpr.sizeof : PExpr → Ty → Option Nat
  | .emp, _ => some 0
  | .list e p, .array ty _ => return (← e.toList).length * (← ty.sizeof) + (← p.sizeof ty)
  | .list .., _ => none

inductive Ty.toMoved : Ty → Ty → Prop where
  | zst : P.toMoved P' → toMoved (.zst P) (.zst P')
  | u8N : toMoved (.u8N N) (.u8N N)
  | i8N : toMoved (.i8N N) (.i8N N)
  | array : toMoved ty moved → toMoved (.array ty sz) (.array moved sz)

def asTy (P : VProp) : Ty := .zst <| .prop P

def Ty.unit : Ty := asTy fun _ => .emp
def Ty.false : Ty := asTy fun _ => .false

def isTyped (e : Expr) (ty : Ty) : VProp := fun vs => ty.mem (e.eval vs) vs

def isHyp (ty : Ty) : VProp := ty.mem 0
def Ty.typed (e : Expr) (ty : Ty) : Ty := asTy (isTyped e ty)

inductive ReturnABI where
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

structure PCtx1 where
  ret : ReturnABI
  epi : Epilogue
  se : Bool

structure PCtx extends GCtx, PCtx1

structure Frame where
  frame : Heap
  retAddr : u64
  pushed : List u64
  lo : Nat
  top : Nat
  le : lo ≤ top
  lt : top < UInt64.size

def Frame.OK (pctx : PCtx) (fr : Frame) : Prop :=
  fr.pushed.length = pctx.epi.regs.length

def Frame.stackBot (fr : Frame) (sp n : Nat) : SProp :=
  (fr.lo + 2^12 + n ≤ sp) ∧ₛ
  fr.lo ↦[fr.lo] -×(sp - fr.lo)

def Frame.stackLayout'
    (fr : Frame) (n sz : Nat) (pushed : List u8) (L : StackLayout) : SProp :=
  let sp := fr.top - pushed.length - sz
  (∃ₛ h, RSP ↦ᵣ ⟨sp, h⟩) ∗ fr.stackBot sp n ∗ L fr.lo sp ∗ (sp + sz).toUInt64 ↦ pushed

def Frame.stackLayout (fr : Frame) (n sz : Nat) (L : StackLayout) : SProp :=
  fr.stackLayout' n sz ((fr.pushed ++ [fr.retAddr]).bind UInt64.bytes) L

def mainLayout (content : List u8) (ip : u64) : SProp :=
  textStart ↦ᶜ content ∗ RIP ↦ ip ∗ SProp.OK ∗ flags ↦ -

def okReturn (pctx : PCtx) (fr : Frame) : Prop :=
  pctx.result.ok <| SProp.heap fr.frame ∗
    (mainLayout pctx.content fr.retAddr ∗
      fr.stackLayout' 8 0 [] .emp ∗
      pctx.ret.returnType)

inductive VCtx where
  | emp
  | var (n : Option Nat) (ty : Ty)
  | and (A B : VCtx)

@[match_pattern] def VCtx.hyp := VCtx.var none

def VCtx.eval : VCtx → VProp
  | .emp => fun _ => .emp
  | .var (some n) ty => isTyped (.var n) ty
  | .hyp ty => isHyp ty
  | .and A B => fun vs => (A.eval vs).sep (B.eval vs)

inductive VCtx.push : VCtx → VCtx → VCtx → Prop where
  | one : VCtx.push .emp A A
  | suc : VCtx.push vctx A (.and vctx A)
  | rot : VCtx.push vctx ty (.and (.and A B) C) → VCtx.push vctx ty (.and A (.and B C))

inductive VCtx.get : VCtx → VCtx → Prop where
  | push : VCtx.push A ty A' → VCtx.get A' ty
  | l : VCtx.get A ty → VCtx.get (.and A B) ty
  | r : VCtx.get B ty → VCtx.get (.and A B) ty
  | rot : VCtx.get (.and (.and A B) C) ty → VCtx.get (.and A (.and B C)) ty

inductive VCtx.take : VCtx → VCtx → VCtx → Prop where
  | move : ty.toMoved moved → VCtx.take (.var n ty) (.var n ty) (.var n moved)
  | ref : ty.toMoved moved → VCtx.take (.var n ty) (.var n moved) (.var n ty)
  | l : VCtx.take A ty A' → VCtx.take (.and A B) ty (.and A' B)
  | r : VCtx.take B ty B' → VCtx.take (.and A B) ty (.and A B')

inductive MExpr where
  | typed (e : Expr) (ty : Ty)
  | part (_ : PExpr) (ty : Ty)

def MExpr.layoutReg : MExpr → Valuation → u64 → Prop
  | .typed e ty, vs => ty.layoutReg (e.eval vs)
  | .part _ _, _ => fun _ => False

def MExpr.layout : MExpr → Nat → Valuation → StackLayout
  | .typed e ty, off, vs => .val off (ty.layout (e.eval vs))
  | .part p ty, off, vs => fun lo sp =>
    ∃ₛ n, (ty.sizeof = some n) ∧ₛ
      let L := OStackLayout.val (p.layout ty vs)
      L.seq .pad off n lo sp

def MExpr.sizeof : MExpr → Option Nat
  | .typed _ ty => ty.sizeof
  | .part p ty => p.sizeof ty

def MExpr.type : MExpr → Ty
  | .typed _ ty | .part _ ty => ty

inductive Expr.reassoc : Expr → Expr → Prop where
  | refl : reassoc e e
  | assoc : reassoc (.append a (.append b c)) e → reassoc (.append (.append a b) c) e

inductive MExpr.inc : MExpr → MExpr → Prop where
  | refl : inc p p
  | trans : inc p₁ p₂ → inc p₂ p₃ → inc p₁ p₁
  | list0 : inc (.part .emp (.array ty n)) (.part (.list .nil .emp) (.array ty n))
  | list_cong : inc (.part p₁ ty) (.part p₂ ty) →
    inc (.part (.list l p₁) (.array ty n)) (.part (.list l p₂) (.array ty n))
  | listS : inc (.part p ty) (.typed e ty) → Expr.reassoc (.append l (.list1 e)) l' →
    inc (.part (.list l p) (.array ty n)) (.part (.list l' .emp) (.array ty n))
  | listC : l.toList = some es → n.toNatLit = some es.length →
    inc (.part (.list l .emp) (.array ty n)) (.typed l (.array ty n))

inductive MExpr.push : MExpr → MExpr → MExpr → Prop where
  | trans_l : inc m₁ m₂ → push m₁ v m₃ → push m₂ v m₃
  | trans_r : push m₁ v m₂ → inc m₁ m₃ → push m₂ v m₃
  | list_cong : push (.part p₁ ty) v (.part p₂ ty) →
    push (.part (.list l p₁) (.array ty n)) v (.part (.list l p₂) (.array ty n))
  | full : push (.part .emp ty) (.typed e ty) (.typed e ty)
  | listS : push (.part p ty) v (.typed e ty) → Expr.reassoc (.append l (.list1 e)) l' →
    push (.part (.list l p) (.array ty n)) v (.part (.list l' .emp) (.array ty n))

inductive MCtxR where
  | emp
  | false
  | free (r : RegNum)
  | reg (reg : RegNum) (val : MExpr)
  | and (A B : MCtxR)

def MCtxR.eval : MCtxR → VProp
  | .emp, _ => .emp
  | .false, _ => .false
  | .free r, _ => ∃ₛ v, r ↦ᵣ v
  | .reg r val, vs => ∃ₛ v, val.layoutReg vs v ∧ₛ r ↦ᵣ v
  | .and A B, vs => A.eval vs ∗ B.eval vs

inductive MCtxR.bdd : MCtxR → RegNum → RegNum → Prop where
  | emp : MCtxR.bdd .emp (0:Fin _) (0:Fin _)
  | free : MCtxR.bdd (.free r) r r
  | reg : MCtxR.bdd (.reg r v) r r
  | and : MCtxR.bdd A a b → b < c → MCtxR.bdd A c d → MCtxR.bdd (A.and B) a d

def MCtxR.OK (m : MCtxR) := ∃ a b, m.bdd a b

inductive MCtxS where
  | free (off n : Nat)
  | val (off : Nat) (e : MExpr)
  | spill (off : Nat) (e : MExpr)
  | and (A B : MCtxS)

inductive MCtx where
  | nostack : MCtxR → MCtx
  | stack : MCtxR → MCtxS → MCtx

def MCtx.R : MCtx → MCtxR
  | .nostack r | .stack r _ => r

def MCtxS.layout : MCtxS → Valuation → StackLayout
  | .free off n, _ => .pad off n
  | .val off e, vs => e.layout off vs
  | .spill off e, vs => .val off fun l => ∃ v, e.layoutReg vs v ∧ toBytes 8 v.toNat = l
  | .and A B, vs => .and (A.layout vs) (B.layout vs)

def MCtx.layout : MCtx → Valuation → StackLayout
  | .nostack _ => fun _ => .emp
  | .stack _ s => s.layout

inductive MCtxR.push : MCtxR → MCtxR → MCtxR → Prop where
  | emp : push .emp A A
  | oneL : push A B (.and B A)
  | oneR : push A B (.and A B)
  | R : push B v B' → push (.and A B) v (.and A B')
  | L : push A v A' → push (.and A B) v (.and A' B)
  | rotL : push M v (.and A (.and B C)) → push M v (.and (.and A B) C)
  | rotR : push M v (.and (.and A B) C) → push M v (.and A (.and B C))

inductive MCtxR.replace : MCtxR → RegNum → MExpr → MCtxR → Prop where
  | free : replace (.free r) r e (.reg r e)
  | reg : replace (.reg r v) r e (.reg r e)
  | R : replace B r e B' → replace (.and A B) r e (.and A B')
  | L : replace A r e A' → replace (.and A B) r e (.and A' B)

inductive MCtxR.get : MCtxR → RegNum → MExpr → Prop where
  | reg : get (.reg r v) r v
  | R : get B r v → get (.and A B) r v
  | L : get A r v → get (.and A B) r v

inductive MCtxS.push : MCtxS → MCtxS → MCtxS → Prop where
  | oneL : push A B (.and B A)
  | oneR : push A B (.and A B)
  | R : push B v B' → push (.and A B) v (.and A B')
  | L : push A v A' → push (.and A B) v (.and A' B)
  | rotL : push M v (.and A (.and B C)) → push M v (.and (.and A B) C)
  | rotR : push M v (.and (.and A B) C) → push M v (.and A (.and B C))

inductive MCtxS.replace : MCtxS → Nat → MExpr → MCtxS → Prop where
  | split : off₂ = off + n₁ → n = n₁ + n₂ →
    replace (.and (.free off n₁) (.free off₂ n₂)) k e A →
    replace (.free off n) k e A
  | startPart : ty.sizeof = some n → MExpr.push (.part .emp ty) e m →
    replace (.free off n) off e (.val off m)
  | push : m.sizeof = some n → off' = off + n → m.push e m' →
    replace (.val off m) off' e (.val off m')
  | spill : replace (.free off 8) off e (.spill off e)
  | respill : replace (.spill off e₁) off e (.spill off e)
  | R : replace B r e B' → replace (.and A B) r e (.and A B')
  | L : replace A r e A' → replace (.and A B) r e (.and A' B)

inductive MCtxS.get : MCtxS → Nat → MExpr → Prop where
  | val : get (.val off v) off v
  | spill : get (.spill off v) off v
  | R : get B off v → get (.and A B) off v
  | L : get A off v → get (.and A B) off v

inductive MCtx.push : MCtx → MCtxR ⊕ MCtxS → MCtx → Prop where
  | reg : MCtxR.push A val A' → MCtx.push (.nostack A) (.inl val) (.nostack A')
  | reg' : MCtxR.push A val A' → MCtx.push (.stack A B) (.inl val) (.stack A' B)
  | stk0 : MCtx.push (.nostack A) (.inr val) (.stack A val)
  | stk : MCtxS.push B val B' → MCtx.push (.stack A B) (.inr val) (.stack A B')

inductive MCtx.replace : MCtx → RegNum ⊕ Nat → MExpr → MCtx → Prop where
  | reg : MCtxR.replace A r e A' → MCtx.replace (.nostack A) (.inl r) e (.nostack A')
  | reg' : MCtxR.replace A r e A' → MCtx.replace (.stack A B) (.inl r) e (.stack A' B)
  | stk : MCtxS.replace B off e B' → MCtx.replace (.stack A B) (.inr off) e (.stack A B')

inductive MCtx.get : MCtx → RegNum ⊕ Nat → MExpr → Prop where
  | reg : MCtxR.get A r v → MCtx.get (.nostack A) (.inl r) v
  | reg' : MCtxR.get A r v → MCtx.get (.stack A B) (.inl r) v
  | stk : MCtxS.get B off v → MCtx.get (.stack A B) (.inr off) v

structure TCtx where
  vctx : VCtx
  vctxSz : Nat
  mctx : MCtx

def TCtx.type (tctx : TCtx) : VProp :=
  fun vs => tctx.vctx.eval vs ∗ tctx.mctx.R.eval vs

def TCtx.layout (tctx : TCtx) : Valuation → StackLayout := tctx.mctx.layout

-- inductive TCtx.pushVar : TCtx → Ty → TCtx → Prop where
--   | mk {vctx mctx} : VCtx.push vctx (.var (some sz) ty) vctx' →
--     TCtx.pushVar ⟨vctx, sz, mctx⟩ ty ⟨vctx', sz + 1, mctx⟩

-- inductive TCtx.pushHyp : TCtx → Ty → TCtx → Prop where
--   | mk {vctx mctx} : VCtx.push vctx (.var none ty) vctx' →
--     TCtx.pushHyp ⟨vctx, sz, mctx⟩ ty ⟨vctx', sz, mctx⟩

-- inductive TCtx.readHyp : TCtx → Ty → Prop where
--   | unit : TCtx.readHyp tctx .unit
--   | var {vctx} : vctx.get (.var n ty) → TCtx.readHyp ⟨vctx, n, tctx⟩ ty

def TCtx.false : TCtx where
  vctx := .hyp .false
  vctxSz := 0
  mctx := .nostack .false

def BlockLoc := Option Nat

def okCodeP (c : List u8) (epi : Epilogue) (tctx : TCtx)
    (fr : Frame) (p : Nat) (ip : BlockLoc) : VProp := fun vs =>
  SProp.heap fr.frame ∗ (
    (match ip with
    | some x => mainLayout c (textStart + p.toUInt64 + x.toUInt64)
    | none => ∃ₛ ip, mainLayout c ip) ∗
    fr.stackLayout 8 epi.sp (tctx.layout vs) ∗ tctx.type vs)

inductive Variant : Type where
def Variant.eval : Variant → Valuation → Nat → Prop
  := nofun

inductive LabelGroup where
  | and : LabelGroup → LabelGroup → LabelGroup
  | one : BlockLoc → Variant → TCtx → LabelGroup

def LabelGroup.eval (lg : LabelGroup) (vs : Valuation) (v : Nat)
    (c : List u8) (epi : Epilogue) (fr : Frame) (p : Nat) : SProp :=
  match lg with
  | .one ip var tctx => var.eval vs v ∗ okCodeP c epi tctx fr p ip vs
  | .and a b => a.eval vs v c epi fr p ∨ₛ b.eval vs v c epi fr p

inductive findLabel : LabelGroup → BlockLoc → Variant → TCtx → Prop where
  | one : findLabel (.one x var tctx) x var tctx
  | l : findLabel A x var tctx → findLabel (.and A B) x var tctx
  | r : findLabel B x var tctx → findLabel (.and A B) x var tctx

def LabelGroups := List (Expr × LabelGroup)

def LabelGroups.eval : LabelGroups → List u8 → Epilogue → Frame → Nat → SProp
  | [], _, _, _, _ => .false
  | (var, ls) :: labs, c, epi, fr, p =>
    (∃ₛ vs, ls.eval vs (var.eval vs) c epi fr p) ∨ₛ eval labs c epi fr p

inductive findLabels : LabelGroups → Expr → LabelGroup → Prop where
  | one : findLabels ((var, ls) :: labs) var ls
  | cons : findLabels labs var ls → findLabels ((var', ls') :: labs) var ls

structure BCtx extends PCtx where
  labelGroups : LabelGroups

def okCodeN (bctx : BCtx) (tctx : TCtx) (fr : Frame) (p : Nat) (ip : BlockLoc) : Prop :=
  bctx.result.ok <| ∃ₛ vs, okCodeP bctx.content bctx.epi tctx fr p ip vs

def okScope (bctx : BCtx) (fr : Frame) (p : Nat) : Prop :=
  okReturn bctx.toPCtx fr ∧ bctx.epi.regs.length = fr.pushed.length ∧
  bctx.result.ok (bctx.labelGroups.eval bctx.content bctx.epi fr p)

def okAsmd (bctx : BCtx) (code : LAsm) (p x y : Nat) : Prop :=
  ∃ s, y = x + s.length ∧ textStart.toNat + p + y < UInt64.size ∧
    sublistAt (p + x) bctx.content s ∧ code.eval p s x

def okCode (bctx : BCtx) (tctx : TCtx) (code : LAsm) (tctx' : TCtx) : Prop :=
  ∀ p x y fr, fr.OK bctx.toPCtx → okAsmd bctx code p x y → okScope bctx fr p →
    okCodeN bctx tctx' fr p (some y) → okCodeN bctx tctx fr p (some x)

axiom okCode.zero {bctx code} : okCode bctx .false code .false

axiom okCode.id {bctx tctx} : okCode bctx tctx .nil tctx

axiom okCode.seq {bctx tctx₁ code₁ tctx₂ code₂ tctx₃} :
  okCode bctx tctx₁ code₁ tctx₂ →
  okCode bctx tctx₂ code₂ tctx₃ →
  okCode bctx tctx₁ (.seq code₁ code₂) tctx₃

axiom okCode.tr {bctx tctx₁ tctx₂ tctx₃} :
  okCode bctx tctx₁ .nil tctx₂ →
  okCode bctx tctx₂ .nil tctx₃ →
  okCode bctx tctx₁ .nil tctx₃

inductive okPrologue :
    (epi : EpilogueR) → (mctx : MCtxR) →
    (code : LAsm) → (epi' : Epilogue) → (mctx' : MCtx) → Prop where
  | push :
    MCtxR.push mctx₁ (.free r) mctx₂ →
    okPrologue (.pop r epi) mctx₂ code epi' mctx₃ →
    okPrologue epi mctx₁ (.seq (.inst (.push (.reg r))) code) epi' mctx₃
  | alloc0 : MCtxR.OK mctx → okPrologue epi mctx .nil (.nostack epi) (.nostack mctx)
  | alloc : MCtxR.OK mctx → n.toNat ≤ 2^12-8 →
    okPrologue epi mctx (.inst (.sub 64 RSP (.imm32 n)))
      (.free n.toNat epi) (.stack mctx (.free 0 n.toNat))

inductive okAssembled : PCtx → LAsm → Prop where
  | mk : assembled pctx.toGCtx (.proc start code) → okAssembled pctx code
  | l : okAssembled pctx (.seq A B) → okAssembled pctx A
  | r : okAssembled pctx (.seq A B) → okAssembled pctx B

inductive Arg where
  | var (ty : Ty)
  | hyp (ty : Ty)

inductive Args where
  | nil
  | snoc (a : Args) (b : Arg)

inductive accumArgs : Args → VCtx → Nat → Prop where
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
inductive accumClob : Clobbers → MCtxR → MCtxR → Prop where
  | nil : accumClob [] mctx mctx
  | cons : MCtxR.push mctx₁ (.free r) mctx₂ →
    accumClob clob mctx₂ mctx₃ → accumClob (r :: clob) mctx₁ mctx₃

inductive okProc : GCtx → Nat → ArgsM → ReturnABI → List RegNum → Bool → Prop where
  | mk :
    okAssembled pctx (.entry start (.seq prol code)) →
    accumArgs args vctx₁ sz₁ →
    accumClob clob mctx₁ mctx₂ →
    okPrologue .ret mctx₂ prol pctx.epi mctx₃ →
    okCode ⟨pctx, []⟩ ⟨vctx₁, sz₁, mctx₃⟩ code .false →
    okProc pctx.toGCtx start ⟨args, mctx₁⟩ pctx.ret clob pctx.se

inductive buildStart : GCtx → PCtx → TCtx → Prop where
  | mk : buildStart gctx ⟨gctx, .noRet, .nostack .ret, true⟩ ⟨.emp, 0, .nostack .emp⟩

inductive okStart : GCtx → Prop where
  | mk :
    okAssembled pctx (.entry start (.seq .nil code)) →
    buildStart gctx pctx tctx →
    okCode ⟨pctx, []⟩ tctx code .false →
    okStart gctx

inductive okPushVariant : Expr → Variant → TCtx → TCtx → Prop where

def variantValue : Variant → Expr
  := nofun

inductive addLabels : BCtx → LabelGroup → LabelGroup → Prop where
  | and : addLabels bctx ls A → addLabels bctx ls B → addLabels bctx ls (.and A B)
  | none :
    variantValue var = val →
    okCode ⟨bctx, (val, ls) :: L⟩ tctx .nil .false →
    addLabels ⟨bctx, L⟩ ls (.one none var tctx)
  | some :
    okAssembled pctx (.at ip code) →
    variantValue var = val →
    okCode ⟨bctx, (val, ls) :: L⟩ tctx code .false →
    addLabels ⟨bctx, L⟩ ls (.one (some ip) var tctx)

inductive okLabels : BCtx → LabelGroup → Prop where
  | l : okLabels bctx (.and A B) → okLabels bctx A
  | r : okLabels bctx (.and A B) → okLabels bctx B
  | mk : addLabels bctx ls ls → okLabels bctx ls

inductive okBlock : BCtx → BlockLoc → TCtx → Prop where
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

inductive checkRet : BCtx → TCtx → ReturnABI → Prop where

def EpilogueR.toCode : EpilogueR → LAsm
  | .ret => .inst .ret
  | .pop r epi => .seq (.inst (.pop r)) epi.toCode

def Epilogue.toCode : Epilogue → LAsm
  | .nostack epi => epi.toCode
  | .free n epi => .seq (.inst (.add 64 RSP (.imm32 n))) epi.toCode

inductive getEpi : BCtx → ReturnABI → LAsm → Prop where
  | mk : getEpi ⟨⟨gctx, ret, epi, se⟩, labs⟩ ret epi.toCode

axiom okCode.epilogue {bctx tctx ret code} :
  getEpi bctx ret code → checkRet bctx tctx ret → okCode bctx tctx code .false

axiom okCode.movRR {bctx vctx sz mctx dst src val mctx'} :
  mctx.get (.inl src) val →
  mctx.replace (.inl dst) val mctx' →
  okCode bctx ⟨vctx, sz, mctx⟩ (.inst (.mov 64 (.reg dst) (.reg src))) ⟨vctx, sz, mctx'⟩

axiom okCode.load {bctx vctx sz mctx n wsz off dst val mctx'} :
  mctx.get (.inr off) val → val.type.sizeof = some n → n ≤ wsz.bytes →
  mctx.replace (.inl dst) val mctx' →
  okCode bctx ⟨vctx, sz, mctx⟩
    (.inst (.mov wsz (.reg dst) (.mem 0 (.reg RSP) off))) ⟨vctx, sz, mctx'⟩

axiom okCode.load64 {bctx vctx sz mctx off dst val mctx'} :
  mctx.get (.inr off) val →
  mctx.replace (.inl dst) val mctx' →
  okCode bctx ⟨vctx, sz, mctx⟩
    (.inst (.mov 64 (.reg dst) (.mem 0 (.reg RSP) off))) ⟨vctx, sz, mctx'⟩

axiom okCode.store {bctx vctx sz mctx n wsz off src val mctx'} :
  mctx.get (.inl src) val → val.type.sizeof = some n → n ≤ wsz.bytes →
  mctx.replace (.inr off) val mctx' →
  okCode bctx ⟨vctx, sz, mctx⟩
    (.inst (.mov wsz (.mem 0 (.reg RSP) off) (.reg src))) ⟨vctx, sz, mctx'⟩

axiom okCode.store64 {bctx vctx sz mctx off src val mctx'} :
  mctx.get (.inl src) val →
  mctx.replace (.inr off) val mctx' →
  okCode bctx ⟨vctx, sz, mctx⟩
    (.inst (.mov 64 (.mem 0 (.reg RSP) off) (.reg src))) ⟨vctx, sz, mctx'⟩

axiom okCode.jump {bctx tctx tgt} :
  okBlock bctx (some tgt) tctx → okCode bctx tctx (.inst (.jump tgt)) .false

inductive okConst : Size → Int → MExpr → Prop where
  | u8N : okConst sz n (.typed (.int (n % 256)) (.u8N sz.bytes))

axiom okCode.loadImm {bctx vctx sz mctx wsz dst n val mctx'} :
  okConst wsz n val → mctx.replace (.inl dst) val mctx' →
  okCode bctx ⟨vctx, sz, mctx⟩ (.inst (.mov wsz (.reg dst) (.imm32 n))) ⟨vctx, sz, mctx'⟩
