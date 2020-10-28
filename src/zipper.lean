
import .two_tree

-- namespace tactic
-- open environment

-- meta def foo (n : name) (e t : expr) (vs : list expr) : tactic (list intro_rule) := _

-- @[user_attribute]
-- meta def mk_zipper_attr : user_attribute :=
-- { name := `zipper,
--   descr := "Make zippers for inductive types",
--   after_set := some $ λ n _ _, do
--     env ← get_env,
--     d ← get_decl n,
--     let ls := d.univ_levels,
--     let e : expr := expr.const n ls,
--     (vs, t) ← infer_type e >>= mk_local_pis,
--     let xs := env.constructors_of n,
--     let n' := n <.> "zipper",
--     xs.mmap $ λ h, do {
--       trace h,
--       let c : expr := expr.const h ls,
--       infer_type (c.mk_app vs) >>= trace },
--     opt ← get_options,
--     updateex_env $ λ e, e.add_ginductive opt d.univ_params vs [((n', t), _)] ff

--  }

-- end tactic
universes u v
variables (α : Type u) (β : Type v)
-- attribute [zipper] tree
#check two_three.tree
namespace two_three.tree
open two_three

inductive zipper
| nil : zipper
| node2_0 : zipper → α → tree α β → zipper
| node2_1 : tree α β → α → zipper → zipper
| node3_0 : zipper → α → tree α β → α → tree α β → zipper
| node3_1 : tree α β → α → zipper → α → tree α β → zipper
| node3_2 : tree α β → α → tree α β → α → zipper → zipper

variables {α β}

namespace zipper

def close : zipper α β → tree α β → tree α β
| nil t := t
| (node2_0 z  x t₁) t := close z $ node2 t  x t₁
| (node2_1 t₀ x z)  t := close z $ node2 t₀ x t
| (node3_0 z  x t₁ y t₂) t := close z $ node3 t  x t₁ y t₂
| (node3_1 t₀ x z  y t₂) t := close z $ node3 t₀ x t  y t₂
| (node3_2 t₀ x t₁ y z)  t := close z $ node3 t₀ x t₁ y t
.
def split : zipper α β → tree α β → α → tree α β → tree α β
| nil ta a tb := node2 ta a tb
| (node2_0 z  x t₁) ta a tb := close z $ node3 ta a tb x t₁
| (node2_1 t₀ x z)  ta a tb := close z $ node3 t₀ x ta a tb
| (node3_0 z  x t₁ y t₂) ta a tb := split z (node2 ta a tb) x (node2 t₁ y t₂)
| (node3_1 t₀ x z  y t₂) ta a tb := split z (node2 t₀ x ta) a (node2 tb y t₂)
| (node3_2 t₀ x t₁ y z)  ta a tb := split z (node2 t₀ x t₁) y (node2 ta a tb)

section eqv

variables [has_lt α] [@decidable_rel α has_lt.lt]

def insert (k : α) (v : β) : zipper α β → tree α β → tree α β
| xs (leaf k' v') :=
  match cmp k k' with
  | ordering.lt := split xs (tree.leaf k v) k' (tree.leaf k' v')
  | ordering.eq := close xs (tree.leaf k' v)
  | ordering.gt := split xs (tree.leaf k' v') k (tree.leaf k v)
  end
| xs (node2 t₀ x t₁) :=
  if k < x
    then insert (node2_0 xs x t₁) t₀
    else insert (node2_1 t₀ x xs) t₁
| xs (node3 t₀ x t₁ y t₂) :=
  if k < x
    then insert (node3_0 xs x t₁ y t₂) t₀
  else if k < y
    then insert (node3_1 t₀ x xs y t₂) t₁
    else insert (node3_2 t₀ x t₁ y xs) t₂

variables [has_le α]
variables {k : α} {v : β} {t : tree α β} {z : zipper α β}

local attribute [simp] insert insert'

example : insert k v z t = insert' k v t (close z) (split z) :=
begin
  induction t generalizing z; dsimp,
  { cases cmp k t_k; dsimp; refl, },
  { split_ifs; simp *; refl },
  { split_ifs; simp *; refl },
end

end eqv
open nat

variables {n m : ℕ} {t t₀ t₁ : tree α β} (x : α) {z : zipper α β}

section defns

variables [has_lt α] [has_le α]

inductive zipper_height (m : ℕ) : ℕ → zipper α β → Prop
| nil : zipper_height m zipper.nil
| node2_0 {n} {z} {x t₁} :
  zipper_height (succ n) z →
  with_height n t₁ →
  zipper_height n (zipper.node2_0 z x t₁)
| node2_1 {n} {z} {t₀ x} :
  zipper_height (succ n) z →
  with_height n t₀ →
  zipper_height n (zipper.node2_1 t₀ x z)
| node3_0 {n} {z} {x t₁ y t₂} :
  zipper_height (succ n) z →
  with_height n t₁ →
  with_height n t₂ →
  zipper_height n (zipper.node3_0 z x t₁ y t₂)
| node3_1 {n} {z} {t₀ x y t₂} :
  zipper_height (succ n) z →
  with_height n t₀ →
  with_height n t₂ →
  zipper_height n (zipper.node3_1 t₀ x z y t₂)
| node3_2 {n} {z} {t₀ x t₁ y} :
  zipper_height (succ n) z →
  with_height n t₀ →
  with_height n t₁ →
  zipper_height n (zipper.node3_2 t₀ x t₁ y z)

lemma with_height_close
  (h : with_height n t)
  (h' : zipper_height m n z) :
  with_height m (close z t) ∨ with_height (succ m) (close z t) :=
begin
  left,
  induction h' generalizing t; dsimp [close],
  repeat { assumption <|> constructor <|> apply h'_ih },
end

lemma with_height_split
  (h₀ : with_height n t₀)
  (h₁ : with_height n t₁)
  (h' : zipper_height m n z) :
  with_height m (split z t₀ x t₁) ∨ with_height (succ m) (split z t₀ x t₁) :=
begin
  induction h' generalizing t₀ x t₁; dsimp [split],
  { right, constructor; assumption },
  repeat
  { apply with_height_close, constructor; assumption, assumption },
  repeat
  { apply h'_ih, repeat { constructor; assumption } },
end

end defns

section insert_height

variables [decidable_linear_order α]
variables {k : α} {v : β}
variables
  (h : zipper_height m n z)
  (h' : with_height n t)
include h h'

example : with_height m (insert k v z t) ∨ with_height (succ m) (insert k v z t) :=
begin
  induction h' generalizing z,
  case two_three.with_height.leaf : k' v' z h
  { dsimp [insert], trichotomy k =? k',
    repeat
    { assumption <|> apply with_height_close <|> apply with_height_split <|> constructor } },
  case two_three.with_height.node2 : h'_n h'_x h'_t₀ h'_t₁ h'_a h'_a_1 h'_ih_a h'_ih_a_1 z h
  { dsimp [insert], split_ifs,
    repeat
    { assumption <|> apply h'_ih_a <|> apply h'_ih_a_1 <|> constructor }, },
  case two_three.with_height.node3 : h'_n h'_x h'_y h'_t₀ h'_t₁ h'_t₂ h'_a h'_a_1 h'_a_2 h'_ih_a h'_ih_a_1 h'_ih_a_2 z h
  { dsimp [insert], split_ifs,
    repeat
    { assumption <|> apply h'_ih_a <|> apply h'_ih_a_1 <|> apply h'_ih_a_2 <|> constructor }, },
end

end insert_height

-- def last : zipper α β → α
-- | nil := _
-- | (node2_0 a a_1 a_2) := last a
-- | (node2_1 a a_1 a_2) := two_three.last a
-- | (node3_0 a a_1 a_2 a_3 a_4) := last a
-- | (node3_1 a a_1 a_2 a_3 a_4) := two_three.last a
-- | (node3_2 a a_1 a_2 a_3 a_4) := two_three.last a

section defns

variables [has_lt α] [has_le α]

inductive above' : option α → α → Prop
| nil {x} : above' none x
| le {x y} : x < y → above' (some x) y

inductive zipper_sorted : option α → zipper α β → option α → Prop
| nil {a b} : zipper_sorted a zipper.nil b
| node2_0 {a b x t₀ t₁} :
  zipper_sorted a t₀ b →
  x = first t₁ →
  sorted' t₁ →
  above (last t₁) b →
  zipper_sorted a (node2_0 t₀ x t₁) (some x)
| node2_1 {a b x t₀ t₁} :
  below a (first t₀) →
  sorted' t₀ →
  last t₀ < x →
  zipper_sorted a t₁ b →
  zipper_sorted (some x) (node2_1 t₀ x t₁) b

| node3_0 {a b x y t₀ t₁ t₂} :
  zipper_sorted a t₀ b →
  x = first t₁ →
  sorted' t₁ →
  last t₁ < y →
  y = first t₂ →
  sorted' t₂ →
  above (last t₂) b →
  zipper_sorted a (node3_0 t₀ x t₁ y t₂) (some x)
| node3_1 {a b x y t₀ t₁ t₂} :
  below a (first t₀) →
  sorted' t₀ →
  last t₀ < x →
  zipper_sorted a t₁ b →
  y = first t₂ →
  sorted' t₂ →
  above (last t₂) b →
  zipper_sorted (some x) (node3_1 t₀ x t₁ y t₂) (some y)
| node3_2 {a b x y t₀ t₁ t₂} :
  below a (first t₀) →
  sorted' t₀ →
  last t₀ < x →
  x = first t₁ →
  sorted' t₁ →
  last t₁ < y →
  zipper_sorted a t₂ b →
  zipper_sorted (some y) (node3_2 t₀ x t₁ y t₂) b

-- | node3 {x y t₀ t₁ t₂} :
--   last t₀ < x →
--   x = first t₁ →
--   last t₁ < y →
--   y = first t₂ →
--   sorted' t₀ →
--   sorted' t₁ →
--   sorted' t₂ →
--   sorted' (tree.node3 t₀ x t₁ y t₂)

end defns

section insert_sorted
variables  [decidable_linear_order α]
open two_three

lemma sorted_close {a b}
  (h₀ : below a (first t))
  (h₁ : sorted' t)
  (h₂ : above (last t) b)
  (h' : zipper_sorted a z b)
  : sorted' (close z t) :=
begin
  induction h' generalizing t,
  all_goals
  { dsimp [close],
    saturate, subst_vars,
    repeat
    { assumption <|> refl <|>
      apply h'_ih <|> constructor }, },
end

lemma sorted_split {a x b}
  (h₀ : below a (first t₀))
  (h₁ : sorted' t₀)
  (h₂ : last t₀ < x)
  (h₃ : first t₁ = x)
  (h₃ : sorted' t₁)
  (h₄ : above (last t₁) b)
  (h' : zipper_sorted a z b)
  : sorted' (split z t₀ x t₁) :=
begin
  induction h' generalizing t₀ x t₁,
  all_goals
  { dsimp [split],
    saturate, subst_vars,
    repeat
    { assumption <|> refl <|>
      apply sorted_close <|>
      apply h'_ih <|> constructor }, },
end

lemma zipper_sorted_none : zipper_sorted none z none :=
begin
  induction z,
  all_goals
  { try { constructor,  } },
end
lemma zipper_sorted_none_of_zipper_sorted {a b} (h : zipper_sorted a z b) :
  zipper_sorted a z none :=
begin
  induction h,
  all_goals
  { subst_vars, constructor }
end
lemma zipper_sorted_none_of_zipper_sorted' {a b} (h : zipper_sorted a z b) :
  zipper_sorted none z b := sorry

variables {k : α} {v : β} {a b : option α}
variables (h : zipper_sorted a z b)
  (h' : sorted' t)
  (h₀ : below a (first t))
  (h₁ : above (last t) b)
include h h' h₀ h₁

example : sorted' (insert k v z t) :=
begin
  induction h' generalizing z a b,
  case two_three.sorted'.leaf : k' v' z h
  { dsimp [insert], trichotomy k =? k',
    repeat
    { assumption <|> apply sorted_close <|> apply sorted_split <|>
      apply zipper_sorted_none <|> constructor },

 },
  case two_three.sorted'.node2 : h'_n h'_x h'_t₀ h'_t₁ _ h'_a h'_a_1 h'_ih_a h'_ih_a_1 z h a b
  { dsimp [insert], subst_vars, split_ifs,
    repeat
    { assumption <|> apply h'_ih_a <|> apply h'_ih_a_1 <|> constructor },
    saturate,

 },
  case two_three.sorted'.node3 : h'_n h'_x h'_y h'_t₀ h'_t₁ h'_t₂ h'_a h'_a_1 h'_a_2 h'_ih_a h'_ih_a_1 h'_ih_a_2 z h
  { dsimp [insert], split_ifs,
    repeat
    { assumption <|> apply h'_ih_a <|> apply h'_ih_a_1 <|> apply h'_ih_a_2 <|> constructor }, },
end

end insert_sorted

end zipper

end two_three.tree
