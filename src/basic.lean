
import tactic.default .tactic
universes u v w

namespace two_three

variables (α : Type u) (β : Type v) {γ : Type w}

inductive tree
| leaf (k : α) (v : β)
| node2 (t₀ : tree) (x : α) (t₁ : tree)
| node3 (t₀ : tree) (x : α) (t₁ : tree) (y : α) (t₂ : tree)

open tree nat

variables {α β}

def first : tree α β → α
| (tree.leaf x _) := x
| (tree.node2 t₀ x _) := first t₀
| (tree.node3 t₀ x _ _ _) := first t₀

def last : tree α β → α
| (tree.leaf x _) := x
| (tree.node2 _ x t₁) := last t₁
| (tree.node3 t₀ x _ _ t₂) := last t₂

section defs
variables [has_le α] [has_lt α]

open tree nat

inductive below : option α → α → Prop
| nil {x} : below none x
| eq {x} : below (some x) x

inductive above : α → option α → Prop
| nil {x} : above x none
| le {x y} : x < y → above x (some y)

inductive sorted' : tree α β → Prop
| leaf {k v} : sorted' (tree.leaf k v)
| node2 {x t₀ t₁} :
  last t₀ < x →
  x = first t₁ →
  sorted' t₀ →
  sorted' t₁ →
  sorted' (tree.node2 t₀ x t₁)
| node3 {x y t₀ t₁ t₂} :
  last t₀ < x →
  x = first t₁ →
  last t₁ < y →
  y = first t₂ →
  sorted' t₀ →
  sorted' t₁ →
  sorted' t₂ →
  sorted' (tree.node3 t₀ x t₁ y t₂)

inductive with_height : ℕ → tree α β → Prop
| leaf {k v} : with_height 0 (tree.leaf k v)
| node2 {n x t₀ t₁} :
  with_height n t₀ →
  with_height n t₁ →
  with_height (succ n) (tree.node2 t₀ x t₁)
| node3 {n x y t₀ t₁ t₂} :
  with_height n t₀ →
  with_height n t₁ →
  with_height n t₂ →
  with_height (succ n) (tree.node3 t₀ x t₁ y t₂)

end defs

local attribute [simp] first last

variables [linear_order α]

lemma first_le_last_of_sorted {t : tree α β} (h : sorted' t) :
  first t ≤ last t :=
begin
  induction h; subst_vars; dsimp [first, last],
  { refl },
  repeat { solve_by_elim [le_of_lt] <|> transitivity },
end

lemma eq_of_below {x : option α} {y : α} (h : below x y) : x.get_or_else y = y :=
by cases h; refl

lemma above_of_above_of_le {x y : α} {k}
  (h : x ≤ y) (h' : above y k) : above x k :=
by cases h'; constructor; solve_by_elim [lt_of_le_of_lt]

@[interactive]
meta def interactive.saturate : tactic unit := do
tactic.interactive.casesm (some ()) [``(above _ (some _)), ``(below (some _) _)],
tactic.find_all_hyps ``(sorted' _) $ λ h, do
{ n ← tactic.get_unused_name `h,
  tactic.mk_app ``first_le_last_of_sorted [h] >>= tactic.note n none,
  tactic.skip },
tactic.find_all_hyps ``(below _ _) $ λ h, do
{ n ← tactic.get_unused_name `h,
  tactic.mk_app ``eq_of_below [h] >>= tactic.note n none,
  tactic.skip },
tactic.find_all_hyps ``(¬ _ < _) $ λ h, do
{ tactic.mk_app ``le_of_not_gt [h] >>= tactic.note h.local_pp_name none,
  tactic.clear h,
  tactic.skip }

@[interactive]
meta def interactive.above : tactic unit := do
tactic.find_hyp ``(above _ _) $ λ h, do
  tactic.refine ``(above_of_above_of_le _ %%h),
  tactic.interactive.chain_trans

end two_three
