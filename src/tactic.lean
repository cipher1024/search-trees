
import tactic.default

universes u v
-- #check @option.elim
-- def option.elim {α β} (x : β) (f : α → β) : option α → β
-- | none := x
-- | (some y) := f y
-- #exit
namespace list

def mfilter_map {m} [applicative m] {α β} (f : α → m (option β)) : list α → m (list.{v} β)
| [] := pure []
| (x :: xs) :=
  (λ a, option.elim a id (::)) <$> f x <*> mfilter_map xs

def mfilter_map' {m} [applicative m] [alternative m] {α β} (f : α → m β) : list α → m (list.{v} β)
| [] := pure []
| (x :: xs) :=
  ((::) <$> f x <|> pure id) <*> mfilter_map' xs

end list


namespace tactic

open native

meta def rename_many' (renames : name_map name) (strict := tt) (use_unique_names := ff)
: tactic (list (name × expr)) :=
do let hyp_name : expr → name :=
     if use_unique_names then expr.local_uniq_name else expr.local_pp_name,
   ctx ← revertible_local_context,
   -- The part of the context after (but including) the first hypthesis that
   -- must be renamed.
   let ctx_suffix := ctx.drop_while (λ h, (renames.find $ hyp_name h).is_none),
   when strict $ do {
     let ctx_names := rb_map.set_of_list (ctx_suffix.map hyp_name),
     let invalid_renames :=
       (renames.to_list.map prod.fst).filter (λ h, ¬ ctx_names.contains h),
     when ¬ invalid_renames.empty $ fail $ format.join
       [ "Cannot rename these hypotheses:\n"
       , format.join $ (invalid_renames.map to_fmt).intersperse ", "
       , format.line
       , "This is because these hypotheses either do not occur in the\n"
       , "context or they occur before a frozen local instance.\n"
       , "In the latter case, try `tactic.unfreeze_local_instances`."
       ]
   },
   -- The new names for all hypotheses in ctx_suffix.
   let new_names :=
     ctx_suffix.map $ λ h,
       (renames.find $ hyp_name h).get_or_else h.local_pp_name,
   revert_lst ctx_suffix,
   -- trace_state,
   xs ← intro_lst new_names,
   xs' ← xs.mmap infer_type,
   -- trace $ ctx_suffix.zip $ xs.zip xs',
   pure $ (ctx_suffix.map expr.local_uniq_name).zip xs

meta def find_hyp (pat : pexpr) (f : expr → tactic unit) : tactic unit := do
ls ← local_context,
pat ← pexpr_to_pattern pat,
ls.mfirst $ λ h, do
  t ← infer_type h,
  match_pattern pat t,
  f h

meta def find_all_hyps (pat : pexpr) (f : expr → tactic unit) : tactic unit := do
ls ← local_context,
pat ← pexpr_to_pattern pat,
ls.mmap' $ λ h, try $ do
  t ← infer_type h,
  match_pattern pat t,
  f h

namespace interactive
setup_tactic_parser

meta def find_hyp (id : parse ident) (_ : parse (tk ":=")) (pat : parse texpr)
  (_ : parse (tk "then")) (tac : itactic) : tactic unit := do
ls ← local_context,
pat ← pexpr_to_pattern pat,
ls.mfirst $ λ h, do
  t ← infer_type h,
  match_pattern pat t,
  rename_many (native.rb_map.of_list [(h.local_uniq_name, id)]) tt tt,
  tac,
  rename_many $ native.rb_map.of_list [(id, h.local_pp_name)]
-- #exit

meta def find_all_hyps (id : parse ident) (_ : parse (tk ":=")) (pat : parse texpr)
  (_ : parse (tk "then")) (tac : itactic) : tactic unit := do
ls ← local_context,
pat ← pexpr_to_pattern pat,
ls.reverse.mmap' (λ h,
  -- trace σ,
  -- let h := h.instantiate_locals $ list.reverse σ,
  try_or_report_error $ do {
    t ← infer_type h,
    match_pattern pat t,
    -- trace!"{h} : {t}",
    n ← tactic.revert h,
    intro id,
    intron $ n-1,
    -- xs ← rename_many' (native.rb_map.of_list [(h.local_uniq_name, id)]) tt tt,
    tac,
    h' ← get_local id,
    n ← tactic.revert h',
    intro h.local_pp_name,
    intron $ n-1,
    skip }),
skip

meta def match_le_or_lt : expr → option (expr × expr)
| `(%%x < %%y) := pure (x, y)
| `(%%x ≤ %%y) := pure (x, y)
| `(%%x > %%y) := pure (y, x)
| `(%%x ≥ %%y) := pure (y, x)
| _ := none

meta def match_le : expr → option (expr × expr)
| `(%%x ≤ %%y) := pure (x, y)
| `(%%x ≥ %%y) := pure (y, x)
| _ := none

meta def match_lt : expr → option (expr × expr)
| `(%%x < %%y) := pure (x, y)
| `(%%x > %%y) := pure (y, x)
| _ := none

#print list.filter_map

inductive edge
| lt | le

instance : has_to_string edge :=
⟨ λ e, match e with
      | edge.lt := "lt"
      | edge.le := "le"
      end ⟩

meta instance edge.has_to_format : has_to_format edge :=
⟨ λ e, to_fmt $ to_string e ⟩

meta instance rb_lmap.has_to_format {α β} [has_to_tactic_format α] [has_to_tactic_format β] : has_to_tactic_format (native.rb_lmap α β) :=
by delta native.rb_lmap; apply_instance

open native

meta def graph := (native.rb_lmap expr (expr × edge × expr))

meta instance graph.has_to_format : has_to_tactic_format graph :=
by delta graph; apply_instance

meta def dfs_trans' (g : graph) (r : ref expr_set) (v : expr) : edge → expr → expr → tactic expr
| e x h := do
  x ← instantiate_mvars x,
  -- trace!"visit {x}, going to {v}",
  vs ← read_ref r,
  -- trace!"seen: {vs}",
  if vs.contains x then failed
  else if v = x then pure h
  else do
    write_ref r $ vs.insert x,
    -- trace (g.find x),
    (g.find x).mfirst $ λ ⟨h',e',y⟩, do
      -- trace!"try: {x}, {y}",
      (e,h) ← match e, e' with
              | edge.lt, edge.lt := prod.mk edge.lt <$> mk_app ``lt_trans [h, h']
              | edge.lt, edge.le := prod.mk edge.lt <$> mk_app ``lt_of_lt_of_le [h, h']
              | edge.le, edge.lt := prod.mk edge.lt <$> mk_app ``lt_of_le_of_lt [h, h']
              | edge.le, edge.le := prod.mk edge.le <$> mk_app ``le_trans [h, h']
              end,
      -- trace"ok",
      dfs_trans' e y h

meta def dfs_trans (g : graph) (v v' : expr) : tactic expr :=
using_new_ref mk_expr_set $ λ r, do
  h ← mk_mapp ``le_refl [none, none, v],
  dfs_trans' g r v' edge.le v h

#check cc_state

lemma lt_of_eq_of_lt_of_eq {α} {R : α → α → Prop} {x x' y' y : α} (h₀ : x = x') (h₁ : R x' y') (h₂ : y' = y) :
  R x y := by subst_vars; exact h₁

-- lemma t_of_eq_of_lt_of_eq {α} [has_lt α] {x x' y' y : α} (h₀ : x = x') (h₁ : x' < y') (h₂ : y' = y) :
--   x < y := by subst_vars; exact h₁

meta def chain_trans : tactic unit := do
tgt ← target,
(x, y) ← match_le_or_lt tgt,
α ← infer_type x,
s ← cc_state.mk_using_hs,
ls ← local_context >>= list.mfilter_map'
  (λ h, do t ← infer_type h,
           do { (e, x, y) ← prod.mk edge.le <$> match_le t <|>
                    prod.mk edge.lt <$> match_lt t,
                let x' := s.root x,
                let y' := s.root y,
                x_pr ← s.eqv_proof x' x,
                y_pr ← s.eqv_proof y y',
                h' ← mk_app ``lt_of_eq_of_lt_of_eq [x_pr, h, y_pr],
                -- trace!"h  : {infer_type h}",
                -- trace!"h' : {infer_type h'}",
                infer_type x >>= is_def_eq α,
                pure [(h', e, x', y')] }),
 -- <|>
 --           do { (x, y) ← match_eq t,
 --                infer_type x >>= is_def_eq α,
 --                h₀ ← mk_eq_symm h >>= mk_app ``le_of_eq ∘ list.ret,
 --                h₁ ← mk_app ``le_of_eq [h],
 --                pure [(h₀, edge.le, y, x), (h₁, edge.le, x, y)] }),
let m := list.foldl  (λ (m : graph) (e : _ × _ × _ × _),
  let ⟨pr,e,x,y⟩ := e in
  m.insert x (pr,e,y)) (native.rb_lmap.mk expr (expr × edge × expr)) ls.join,
pr ← dfs_trans m x y,
tactic.apply pr <|>
  mk_app ``le_of_lt [pr] >>= tactic.apply,
skip

end interactive

setup_tactic_parser
precedence `=?`:0

import_private set_cases_tags
import_private cases_postprocess

meta def interactive.trichotomy (x : parse texpr) (_ : parse $ tk "=?") (y : parse texpr) (hyp : parse $ tk "with" *> ident <|> pure `h) : tactic unit := do
x ← to_expr x,
y ← to_expr y,
α ← infer_type x,
inst ← mk_app ``linear_order [α] >>= mk_instance,
h' ← mk_mapp ``cmp_compares [α, inst, x, y] >>= note hyp none,

e ← mk_app ``cmp [x, y],
n ← revert_kdependencies e,
x ← get_unused_name,
tactic.generalize e x,

h ← tactic.intro1,
s ← simp_lemmas.mk.add_simp ``ordering.compares,
in_tag ← get_main_tag,
focus1 $ do
  hs ← cases_core h,
  set_cases_tags in_tag $ cases_postprocess hs,
  gs ← get_goals,
  gs ← (gs.zip hs).mmap $ λ ⟨g,h,_,σ⟩, do
  { set_goals [g],
    interactive.propagate_tags $ do
    { dsimp_target (some s) [] { fail_if_unchanged := ff },
      intron_no_renames (n) },
    get_goals },
  set_goals gs.join

end tactic

example {x y : ℤ} (h : x ≤ y) (h : x < y) : true :=
begin
  find_hyp hh := x ≤ _ then { replace hh : x = y, admit },
  trivial
end

example {x y z w u v : ℕ} {a b : ℤ} (h₀ : x ≤ y) (h₁ : y < z) (h : y < u) (h₂ : z < w) (h₃ : w = u) (h₄ : u < v) : x ≤ u :=
begin
  chain_trans,
end
