namespace mm0

@[derive has_reflect]
structure sort_data := (pure strict provable free : bool := ff)

@[reducible] def ident := string
def dep_type := ident × list ident

@[derive has_reflect]
inductive sexpr : Type
| var : ident → sexpr
| const : ident → sexpr
| app : sexpr → sexpr → sexpr

def sexpr.apps' : sexpr → list sexpr → sexpr
| e [] := e
| e (x::l) := (e.app x).apps' l

def sexpr.apps (n : ident) : list sexpr → sexpr := (sexpr.const n).apps'

def sexpr.get_apps' : sexpr → list sexpr → option (ident × list sexpr)
| (sexpr.app e₁ e₂) l := sexpr.get_apps' e₁ (e₂ :: l)
| (sexpr.const x) l := return (x, l)
| _ l := none

def sexpr.get_apps (e : sexpr) : option (ident × list sexpr) := e.get_apps' []

@[derive has_reflect]
inductive binder : Type
| bound : ident → ident → binder
| reg : ident → dep_type → binder
| hyp : ident → sexpr → binder

@[derive has_reflect]
inductive stmt : Type
| sort : ident → sort_data → stmt
| term : bool → ident → list binder → dep_type → option (list binder × sexpr) → stmt
| thm : bool → ident → list binder → sexpr → option (list binder × sexpr) → stmt

def env := list stmt

end mm0
