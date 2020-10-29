
import control.monad.cont

open tactic

namespace tactic

-- this should probably be PR-ed
meta def bt_tac (α : Type) :=
∀ r, cont_t r tactic α

meta instance : monad bt_tac :=
{ pure := λ α x r, pure x,
  bind := λ α β x f r, x r >>= λ a, f a r }

meta instance bt_tac.alternative : alternative bt_tac :=
{ failure := λ α r _, failure,
  orelse  := λ α x y r f, x _ f <|> y _ f }

meta def run_bt {α} (x : bt_tac α) : tactic α :=
x _ pure

meta def bt_lift {α} (x : tactic α) : bt_tac α :=
λ r f, x >>= f

meta def var : bt_tac expr :=
bt_lift mk_mvar

meta def hyp (p : pexpr) : bt_tac expr := do
p ← bt_lift $ to_expr p,
ls ← bt_lift local_context,
ls.mfirst $ λ h, bt_lift $ do
  t ← infer_type h,
  h <$ unify t p

meta def hyp_with (p : pexpr) : bt_tac (expr × expr) := do
p ← bt_lift $ to_expr p,
ls ← bt_lift local_context,
ls.mfirst $ λ h, bt_lift $ do
  t ← infer_type h,
  e ← kabstract t p,
  guard $ e.has_var,
  pure (h, e)

end tactic
