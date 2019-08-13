namespace mm0
namespace mm0b

def sortid := ℕ
def termid := ℕ
def thmid := ℕ
def heapid := ℕ
def ptr := ℕ

structure sort_data := (pure strict provable free : bool := ff)

inductive proof_cmd : Type
| save : proof_cmd
| term : termid → proof_cmd
| ref : heapid → proof_cmd
| dummy : sortid → proof_cmd
| thm : thmid → proof_cmd
| hyp : proof_cmd
| conv : proof_cmd
| refl : proof_cmd
| symm : proof_cmd
| cong : proof_cmd
| unfold : proof_cmd
| conv_cut : proof_cmd
| conv_ref : heapid → proof_cmd

inductive type : Type
| bound : sortid → type
| reg : sortid → list bool → type

inductive sexpr : Type
| var : type → heapid → sexpr
| app : type → termid → list ptr → sexpr

inductive stackel
| expr : ptr → stackel
| proof : ptr → stackel
| conv : ptr → ptr → stackel
| co_conv : ptr → ptr → stackel

def type.sort : type → sortid
| (type.bound s) := s
| (type.reg s _) := s

inductive unify_cmd
| save : unify_cmd
| term : termid → unify_cmd
| ref : heapid → unify_cmd
| dummy : sortid → unify_cmd
| thm : unify_cmd
| hyp : unify_cmd

structure termel :=
(bis : list type)
(ret : type)
(defn : option (list unify_cmd))

structure thmel :=
(bis : list type)
(unify : list unify_cmd)

structure env :=
(sorts : list sort_data)
(terms : list termel)
(thms : list thmel)

inductive get_term_args : ℕ → list stackel → list ptr → list stackel → Prop
| zero (S) : get_term_args 0 S [] S
| succ (n S₁ p ps S₂) :
  get_term_args n S₁ ps S₂ →
  get_term_args (n+1) (stackel.expr p :: S₁) (ps ++ [p]) S₂

structure state :=
(stack : list stackel)
(heap : list stackel)
(store : list sexpr)
(unify : list ptr × list unify_cmd)

inductive unify : list sexpr → list ptr × list unify_cmd → list ptr → list stackel → list stackel → Prop
| save (σ H us e K S S') :
  unify σ (H ++ [e], us) (e :: K) S S' →
  unify σ (H, unify_cmd.save :: us) (e :: K) S S'
| term (σ : list sexpr) (H us e t τ es K S S') :
  σ.nth e = some (sexpr.app τ t es) →
  unify σ (H, us) (es ++ K) S S' →
  unify σ (H, unify_cmd.term t :: us) (e :: K) S S'
| ref (σ) (H : list ptr) (us e v K S S') :
  H.nth v = some e →
  unify σ (H, us) K S S' →
  unify σ (H, unify_cmd.ref v :: us) (e :: K) S S'
| dummy (σ : list sexpr) (H us e s v K S S') :
  σ.nth e = some (sexpr.var (type.bound s) v) →
  unify σ (H ++ [e], us) K S S' →
  unify σ (H, unify_cmd.dummy s :: us) (e :: K) S S'
| thm (σ H us e K S S') :
  unify σ (H, us) (e :: K) S S' →
  unify σ (H, unify_cmd.thm :: us) K (stackel.expr e :: S) (stackel.proof e :: S')
| hyp (σ H us e K S S') :
  unify σ (H, us) (e :: K) S S' →
  unify σ (H, unify_cmd.hyp :: us) K (stackel.proof e :: S) S'
| nil (σ H S) : unify σ (H, []) [] S S

inductive partial_unify : list sexpr → list ptr × list unify_cmd → list ptr → list ptr × list unify_cmd → Prop
| save (σ H us e K U') :
  partial_unify σ (H ++ [e], us) (e :: K) U' →
  partial_unify σ (H, unify_cmd.save :: us) (e :: K) U'
| term (σ : list sexpr) (H us e t τ es K U') :
  σ.nth e = some (sexpr.app τ t es) →
  partial_unify σ (H, us) (es ++ K) U' →
  partial_unify σ (H, unify_cmd.term t :: us) (e :: K) U'
| ref (σ) (H : list ptr) (us e v K U') :
  H.nth v = some e →
  partial_unify σ (H, us) K U' →
  partial_unify σ (H, unify_cmd.ref v :: us) (e :: K) U'
| nil (σ U) : partial_unify σ U [] U

inductive step_proof (env : env) : proof_cmd → state → state → Prop
| save (e S H σ U) : step_proof proof_cmd.save ⟨e :: S, H, σ, U⟩ ⟨e :: S, H ++ [e], σ, U⟩
| term (t el S args S' H σ U) :
  env.terms.nth t = some el →
  get_term_args el.bis.length S args S' →
  step_proof (proof_cmd.term t) ⟨S, H, σ, U⟩
    ⟨stackel.expr σ.length :: S', H, σ ++ [sexpr.app el.ret t args], U⟩
| ref (v S) (H : list stackel) (el σ U) :
  H.nth v = some el →
  step_proof (proof_cmd.ref v) ⟨S, H, σ, U⟩ ⟨el :: S, H, σ, U⟩
| dummy (s S H σ U) :
  step_proof (proof_cmd.dummy s) ⟨S, H, σ, U⟩
    ⟨stackel.expr σ.length :: S,
     H ++ [stackel.expr σ.length],
     σ ++ [sexpr.var (type.bound s) H.length], U⟩
| thm (t el S args S₁ S₂ H σ U) :
  env.thms.nth t = some el →
  get_term_args el.bis.length S args S₁ →
  unify σ (args, el.unify) [] S₁ S₂ →
  step_proof (proof_cmd.thm t) ⟨S, H, σ, U⟩ ⟨S₂, H, σ, U⟩
| hyp (e S H σ HU U U') :
  partial_unify σ (HU, U) [e] U' →
  step_proof proof_cmd.hyp
    ⟨stackel.expr e :: S, H, σ, (HU, unify_cmd.hyp :: U)⟩
    ⟨S, H ++ [stackel.proof e], σ, U'⟩
| conv (e1 e2 S H σ U) :
  step_proof proof_cmd.conv
    ⟨stackel.proof e2 :: stackel.expr e1 :: S, H, σ, U⟩
    ⟨stackel.co_conv e1 e2 :: S, H, σ, U⟩
| refl (e S H σ U) :
  step_proof proof_cmd.refl
    ⟨stackel.co_conv e e :: S, H, σ, U⟩ ⟨S, H, σ, U⟩
| symm (e1 e2 S H σ U) :
  step_proof proof_cmd.symm
    ⟨stackel.co_conv e1 e2 :: S, H, σ, U⟩
    ⟨stackel.co_conv e2 e1 :: S, H, σ, U⟩
| cong (e1 e2 t τ1 τ2 es1 es2 S H) (σ : list sexpr) (U) :
  σ.nth e1 = sexpr.app τ1 t es1 →
  σ.nth e2 = sexpr.app τ2 t es2 →
  step_proof proof_cmd.cong
    ⟨stackel.co_conv e1 e2 :: S, H, σ, U⟩
    ⟨list.zip_with stackel.co_conv es1 es2 ++ S, H, σ, U⟩
| unfold (e e' t el us e2 args S H S') (σ : list sexpr) (U) :
  env.terms.nth t = some el → el.defn = some us →
  unify σ (args, us) [e2] S S' →
  step_proof proof_cmd.cong
    ⟨stackel.expr e2 :: stackel.co_conv e e' :: S, H, σ, U⟩
    ⟨stackel.co_conv e2 e' :: S', H, σ, U⟩
| conv_cut (e1 e2 S H) (σ : list sexpr) (U) :
  step_proof proof_cmd.conv_cut
    ⟨stackel.expr e2 :: stackel.expr e1 :: S, H, σ, U⟩
    ⟨stackel.co_conv e1 e2 :: stackel.conv e1 e2 :: S, H, σ, U⟩
| conv_ref (v e1 e2 S) (H : list stackel) (σ U) :
  H.nth v = some (stackel.conv e1 e2) →
  step_proof (proof_cmd.conv_ref v)
    ⟨stackel.co_conv e1 e2 :: S, H, σ, U⟩ ⟨S, H, σ, U⟩

inductive proof (env : env) : list proof_cmd → state → Prop
| cons (p ps st st') :
  step_proof env p st st' →
  proof ps st' → proof (p :: ps) st
| thm (e S H σ HU U U') :
  partial_unify σ (HU, U) [e] U' →
  proof [] ⟨stackel.proof e :: S, H, σ, U'⟩ →
  proof [] ⟨stackel.proof e :: S, H, σ, (HU, unify_cmd.thm :: U)⟩
| nil (H σ HU) : proof [] ⟨[], H, σ, (HU, [])⟩

end mm0b
end mm0
