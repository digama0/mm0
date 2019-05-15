import data.buffer category.basic tactic.core

def name.to_simple : name → string
| (name.mk_string s _) := s
| _ := ""

meta def lean.parser.tk' (n : name) : lean.parser unit :=
do x ← lean.parser.ident, tactic.trace (x, n), guard (x = n)

meta def user_attribute.get_param' {α β : Type} [reflected β] (attr : user_attribute α β) (n : name) : tactic β :=
attr.get_param_untyped n >>= tactic.eval_expr' β

meta def declaration.value_opt : declaration → option expr
| (declaration.defn _ _ _ v _ _) := some v
| (declaration.thm _ _ _ v)      := some v.get
| _                              := none

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
| term : ident → list binder → dep_type → option (list binder × sexpr) → stmt
| thm : ident → list binder → sexpr → option (list binder × sexpr) → stmt

open tactic native

@[derive has_reflect]
inductive mm0_param
| ax : mm0_param
| none : mm0_param
| sd : sort_data → mm0_param

def mm0_param.is_ax : mm0_param → bool
| mm0_param.ax := tt
| _ := ff

meta def mm0_param.to_sd : mm0_param → option sort_data
| mm0_param.none := return {}
| (mm0_param.sd sd) := return sd
| _ := none

meta def list_name_to_sort_data : list name → option sort_data
| [] := return {}
| (a :: l) := do sd ← list_name_to_sort_data l,
  match a with
  | `pure := return {pure := tt, ..sd}
  | `strict := return {strict := tt, ..sd}
  | `provable := return {provable := tt, ..sd}
  | `free := return {free := tt, ..sd}
  | _ := none
  end

meta def parse_mm0_param : lean.parser mm0_param :=
do x ← lean.parser.many lean.parser.ident,
match x with
| [] := return mm0_param.none
| [`ax] := return mm0_param.ax
| l := mm0_param.sd <$> list_name_to_sort_data l
end

@[user_attribute]
meta def mm0 : user_attribute unit mm0_param :=
{ name := `mm0,
  parser := parse_mm0_param,
  after_set := some (λ n _ _, do
    tac ← tactic.eval_expr (name → tactic unit) (expr.const `mm0.after_set []),
    tac n),
  descr := "Metamath Zero declaration" }

@[user_attribute]
meta def mm0_alias : user_attribute unit string :=
{ name := `mm0_alias,
  parser := name.to_simple <$> lean.parser.ident,
  descr := "Metamath Zero alias" }

meta def get_stmt (n : name) : tactic stmt :=
eval_expr _ (expr.const (n <.> "_stmt") [])

meta def get_term (n : name) : tactic (list binder × dep_type) :=
(do s ← get_stmt n, match s with
| (stmt.term _ bs t _) := return (bs, t)
| _ := failed
end) <|> fail ("term" ++ n.to_string ++ " is not a mm0 term")

meta def binder_tac (α) := reader_t (buffer ident) (state_t (buffer binder × rb_set ident) tactic) α

meta instance : monad binder_tac := reader_t.monad
meta instance : alternative binder_tac := reader_t.alternative
meta instance binder_tac.monad_state : monad_state (buffer binder × rb_set ident) binder_tac :=
⟨λ α m, reader_t.lift (monad_state.lift m)⟩
meta instance : monad_reader (buffer ident) binder_tac := reader_t.monad_reader
meta instance : has_monad_lift tactic binder_tac :=
⟨λ α m, reader_t.lift (state_t.lift m)⟩

meta def binder_tac.run {α} (m : binder_tac α) :
  tactic (α × buffer binder × rb_set ident) :=
state_t.run (reader_t.run m mk_buffer) (mk_buffer, mk_rb_set)

meta def get_var_name (n : ℕ) : binder_tac ident :=
do ns ← read,
if n < ns.size then
  return (ns.read' (ns.size - 1 - n))
else monad_lift $ fail "get_var_name"

meta def push_bound {α} (n : name) (s : ident) (m : binder_tac α) : binder_tac α :=
do (bs, vs) ← get,
  let x := n.to_string,
  monad.unlessb (vs.contains x) $
    put (bs.push_back (binder.bound x s), vs.insert x),
  reader_t.adapt (λ ctx, ctx.push_back x) m

meta def parse_binders1_aux (x : string) : expr → buffer ident →
  binder_tac unit
| (expr.pi n _ (expr.const s []) e) l :=
  push_bound n s.to_simple $
    parse_binders1_aux e (l.push_back n.to_string)
| (expr.const s []) l :=
  modify $ λ ⟨bs, vs⟩, (bs.push_back (binder.reg x (s.to_simple, l.to_list)), vs)
| x e := monad_lift $ do f ← pp e,
  fail $ "parse_binders1_aux " ++ x.to_string ++ " " ++ f.to_string

meta def parse_binders1 (x : string) (e : expr) : binder_tac unit :=
parse_binders1_aux x e mk_buffer

meta def parse_term_aux : expr → binder_tac dep_type
| (expr.pi n _ t e) := parse_binders1 n.to_string t >> parse_term_aux e
| (expr.const s []) := return (s.to_simple, [])
| e := monad_lift $ do f ← pp e, fail $ "parse_term_aux " ++ f.to_string

meta def parse_term (e : expr) : tactic (list binder × dep_type) :=
do (d, bs, _) ← binder_tac.run (parse_term_aux e),
  return (bs.to_list, d)

meta def as_sort : expr → tactic ident
| (expr.const s []) := do stmt.sort _ _ ← get_stmt s, return s.to_simple
| e := do f ← pp e, fail $ f.to_string ++ " is not a sort"

meta def try_bind {α β} (t : tactic α) (f : tactic β) (g : α → tactic β) : tactic β :=
do o ← try_core t, option.cases_on o f g

meta mutual def parse_sexpr, parse_sexpr_list, parse_sexpr_list1
with parse_sexpr : expr → binder_tac sexpr
| e := match e.get_app_fn with
  | (expr.const fn []) := do
    fn' ← monad_lift $ mcond (succeeds (has_attribute `mm0 fn))
      (return fn.to_simple) (mm0_alias.get_param' fn),
    sexpr.apps fn.to_simple <$>
      parse_sexpr_list e.get_app_args (mk_name_set, mk_buffer)
  | (expr.var n) := sexpr.var <$> get_var_name n
  | (expr.pi n i d e) := parse_sexpr $ (expr.const `al []).app (expr.lam n i d e)
  | e := monad_lift $ fail $ "unrecognized head expr " ++ e.to_string
  end
with parse_sexpr_list : list expr → name_set × buffer sexpr → binder_tac (list sexpr)
| []        (_, buf) := return buf.to_list
| (e :: es) (m, buf) := parse_sexpr_list1 e m buf >>= parse_sexpr_list es
with parse_sexpr_list1 : expr → name_set → buffer sexpr → binder_tac (name_set × buffer sexpr)
| (expr.lam n _ (expr.const s []) e) m es :=
  push_bound n s.to_simple $
  let n' := n.to_string in
  if m.contains n then
    parse_sexpr_list1 e m es
  else
    parse_sexpr_list1 e (m.insert n) (es.push_back (sexpr.var n'))
| e m es := do
  e' ← parse_sexpr e,
  return (m, es.push_back e')

meta def parse_hyp_aux : expr → binder_tac sexpr
| e'@(expr.pi n _ t e) := do
  o ← monad_lift $ try_core (as_sort t),
  match o with
  | some s := push_bound n s (parse_hyp_aux e)
  | none := parse_sexpr e'
  end
| e := parse_sexpr e

meta def parse_hyp (x : string) (e : expr) : binder_tac unit :=
do e' ← parse_hyp_aux e,
  modify $ λ ⟨bs, vs⟩, (bs.push_back (binder.hyp x e'), vs)

meta def parse_thm_aux : expr → binder_tac sexpr
| (expr.pi n binder_info.strict_implicit (expr.const t []) e) :=
  push_bound n t.to_simple (parse_thm_aux e)
| (expr.pi n _ t e) := do
  let n' := n.to_string,
  parse_binders1 n' t <|> parse_hyp n' t,
  reader_t.adapt (λ ctx, ctx.push_back n') (parse_thm_aux e)
| e := parse_sexpr e

meta def parse_thm (e : expr) : tactic (list binder × sexpr) :=
do (d, bs, _) ← binder_tac.run (parse_thm_aux e),
  return (bs.to_list, d)

meta def parse_def_aux : expr → binder_tac sexpr
| (expr.lam n _ t e) := do
  let n' := n.to_string,
  parse_binders1 n.to_string t,
  reader_t.adapt (λ ctx, ctx.push_back n') (parse_def_aux e)
| e := do
  (bs, _) ← get,
  let n := bs.size,
  e' ← parse_sexpr e,
  (bs, _) ← get,
  modify $ λ ⟨bs, vs⟩, (bs.drop n, vs),
  return e'

meta def parse_def (e : expr) : tactic (list binder × sexpr) :=
do (d, bs, _) ← binder_tac.run (parse_def_aux e),
  return (bs.to_list, d)

meta def parse_proof_aux : expr → binder_tac sexpr
| (expr.lam n binder_info.strict_implicit (expr.const t []) e) :=
  push_bound n t.to_simple (parse_proof_aux e)
| (expr.lam n _ t e) := do
  let n' := n.to_string,
  parse_binders1 n.to_string t <|> parse_hyp n' t,
  reader_t.adapt (λ ctx, ctx.push_back n') (parse_proof_aux e)
| e := do
  (bs, _) ← get,
  let n := bs.size,
  e' ← parse_sexpr e,
  (bs, _) ← get,
  modify $ λ ⟨bs, vs⟩, (bs.drop n, vs),
  return e'

meta def parse_proof (e : expr) : tactic (list binder × sexpr) :=
do (d, bs, _) ← binder_tac.run (parse_proof_aux e),
  return (bs.to_list, d)

meta def to_stmt (n : name) : tactic stmt :=
do d ← get_decl n,
  p ← mm0.get_param' n,
  match d.type with
  | `(Type) := stmt.sort n.to_simple <$> p.to_sd
  | e := do
    pt ← (sum.inl <$> parse_term e) <|> (sum.inr <$> parse_thm e),
    match pt, d.value_opt.filter (λ a:expr, ¬ p.is_ax) with
    | sum.inl (ls, d), e := stmt.term n.to_simple ls d <$> option.traverse parse_def e
    | sum.inr (ls, d), e := stmt.thm n.to_simple ls d <$> option.traverse parse_proof e
    end
  end

meta def after_set (n : name) : tactic unit :=
do s ← to_stmt n,
  add_decl (mk_definition (n <.> "_stmt") [] `(stmt) (reflect s))

end mm0
