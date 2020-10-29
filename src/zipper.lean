
import .basic .backtrack

universes u v
variables (α : Type u) (β : Type v)

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

@[pp_nodot]
def close : zipper α β → option α → tree α β → tree α β
| nil k t := t
| (node2_0 z  x t₁) k t := close z k $ node2 t  x t₁
| (node2_1 t₀ x z)  k t := close z none $ node2 t₀ (k.get_or_else x) t
| (node3_0 z  x t₁ y t₂) k t := close z k $ node3 t  x t₁ y t₂
| (node3_1 t₀ x z  y t₂) k t := close z none $ node3 t₀ (k.get_or_else x) t  y t₂
| (node3_2 t₀ x t₁ y z)  k t := close z none $ node3 t₀ x t₁ (k.get_or_else y) t

@[pp_nodot]
def split : zipper α β → option α → tree α β → α → tree α β → tree α β
| nil k ta a tb := node2 ta a tb
| (node2_0 z  x t₁) k ta a tb := close z k $ node3 ta a tb x t₁
| (node2_1 t₀ x z)  k ta a tb := close z none $ node3 t₀ (k.get_or_else x) ta a tb
| (node3_0 z  x t₁ y t₂) k ta a tb := split z k (node2 ta a tb) x (node2 t₁ y t₂)
| (node3_1 t₀ x z  y t₂) k ta a tb := split z none (node2 t₀ (k.get_or_else x) ta) a (node2 tb y t₂)
| (node3_2 t₀ x t₁ y z)  k ta a tb := split z none (node2 t₀ x t₁) (k.get_or_else y) (node2 ta a tb)

section eqv

variables [has_lt α] [@decidable_rel α has_lt.lt]

def insert (k : α) (v : β) : zipper α β → tree α β → tree α β
| xs (leaf k' v') :=
  match cmp k k' with
  | ordering.lt := split xs (some k) (tree.leaf k v) k' (tree.leaf k' v')
  | ordering.eq := close xs (some k') (tree.leaf k' v)
  | ordering.gt := split xs (some k') (tree.leaf k' v') k (tree.leaf k v)
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

def insert' (k : α) (v : β) : tree α β → tree α β :=
insert k v zipper.nil

end eqv
open nat

variables {n m : ℕ} {pk : option α} {t t₀ t₁ : tree α β} (x : α) {z : zipper α β}

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
  with_height m (close z pk t) ∨ with_height (succ m) (close z pk t) :=
begin
  left,
  induction h' generalizing t pk; dsimp [close] at *,
  repeat { apply h'_ih <|> assumption <|> constructor },
end

lemma with_height_split
  (h₀ : with_height n t₀)
  (h₁ : with_height n t₁)
  (h' : zipper_height m n z) :
  with_height m (split z pk t₀ x t₁) ∨ with_height (succ m) (split z pk t₀ x t₁) :=
begin
  induction h' generalizing t₀ x t₁ pk; dsimp [split],
  { right, constructor; assumption },
  repeat
  { apply with_height_close, constructor; assumption, assumption },
  repeat
  { apply h'_ih, repeat { constructor; assumption } },
end

end defns

section insert_height

variables [linear_order α]
variables {k : α} {v : β}
variables
  (h : zipper_height m n z)
  (h' : with_height n t)
include h h'

lemma with_height_insert : with_height m (insert k v z t) ∨ with_height (succ m) (insert k v z t) :=
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

lemma with_height_insert' (h' : with_height m t) : with_height m (insert' k v t) ∨ with_height (succ m) (insert' k v t) :=
with_height_insert (by constructor) h'

end insert_height

section defns

variables [has_lt α] [has_le α]

inductive zipper_sorted : option α → zipper α β → option α → Prop
| nil {a b} : zipper_sorted a zipper.nil b
| node2_0 {a b x t₀ t₁} :
  zipper_sorted a t₀ b →
  x = first t₁ →
  sorted' t₁ →
  above (last t₁) b →
  zipper_sorted a (node2_0 t₀ x t₁) (some x)
| node2_1 {a b x t₀ t₁} :
  zipper_sorted a t₁ b →
  below a (first t₀) →
  sorted' t₀ →
  last t₀ < x →
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
  zipper_sorted a t₁ b →
  below a (first t₀) →
  sorted' t₀ →
  last t₀ < x →
  y = first t₂ →
  sorted' t₂ →
  above (last t₂) b →
  zipper_sorted (some x) (node3_1 t₀ x t₁ y t₂) (some y)
| node3_2 {a b x y t₀ t₁ t₂} :
  zipper_sorted a t₂ b →
  below a (first t₀) →
  sorted' t₀ →
  last t₀ < x →
  x = first t₁ →
  sorted' t₁ →
  last t₁ < y →
  zipper_sorted (some y) (node3_2 t₀ x t₁ y t₂) b

attribute [pp_nodot]
  zipper_sorted.nil
  zipper_sorted.node2_0
  zipper_sorted.node2_1
  zipper_sorted.node3_0
  zipper_sorted.node3_1
  zipper_sorted.node3_2
  zipper.nil
  zipper.node2_0
  zipper.node2_1
  zipper.node3_0
  zipper.node3_1
  zipper.node3_2

end defns

section insert_sorted
-- variables {pk : option α}
variables  [linear_order α]
open two_three

lemma sorted_close {a b}
  (h' : zipper_sorted a z b)
  (h₀ : below a (first t))
  (h₃ : below pk (first t))
  (h₁ : sorted' t)
  (h₂ : above (last t) b)
  : sorted' (close z pk t) :=
begin
  induction h' generalizing t pk,
  all_goals
  { dsimp [close],
    saturate, subst_vars,
    simp only * { fail_if_unchanged := ff },
    repeat
    { assumption <|> refl <|>
      apply h'_ih <|> constructor <|> cc }, },
end

lemma sorted_split {a x b}
  (h' : zipper_sorted a z b)
  (h₀ : below a (first t₀))
  (h₀ : below pk (first t₀))
  (h₁ : sorted' t₀)
  (h₂ : last t₀ < x)
  (h₃ : first t₁ = x)
  (h₃ : sorted' t₁)
  (h₄ : above (last t₁) b)
  : sorted' (split z pk t₀ x t₁) :=
begin
  induction h' generalizing t₀ x t₁ pk,
  all_goals
  { dsimp [split],
    saturate, subst_vars,
    simp only * { fail_if_unchanged := ff },
    repeat
    { assumption <|> refl <|>
      apply sorted_close <|>
      apply h'_ih <|> constructor }, },
end

section tac
open tactic

@[interactive]
meta def simp_min : tactic unit :=
run_bt $ do
  x ← var,
  y ← var,
  (h, _) ← hyp_with ``(min %%x %%y),
  bt_lift $ do
  (pr, h) ← mcond (succeeds (is_def_eq x y))
  (do p₀ ← to_expr ``(min %%x %%y = %%x),
      n ← get_unused_name `h,
      (h, _) ← local_proof n p₀ (applyc ``min_self),
      pure (h, h))
  (do p₀ ← to_expr ``(%%x ≤ %%y),
      p₁ ← to_expr ``(%%y ≤ %%x),
      n ← get_unused_name `h,
      do { (h, _) ← local_proof n p₀ (assumption <|> applyc ``le_of_lt >> assumption),
           pr ← mk_app ``min_eq_left [h],
           pure (pr, h) } <|>
        do { (h, _) ← local_proof n p₁ (assumption <|> applyc ``le_of_lt >> assumption),
             pr ← mk_app ``min_eq_right [h],
             pure (pr, h) }),
   interactive.loc.apply
     (λ h', try $ rewrite_hyp pr h' >> skip)
     (try $ rewrite_target pr)
     interactive.loc.wildcard,
  skip

end tac

variables {k : α} {v : β} (a b : option α)
variables (h : zipper_sorted a z b)
  (h' : sorted' t)
  (h₀ : below a (min k (first t)))
  (h₁ : above (last t) b)
  (h₂ : above k b)
include h h' h₀ h₁ h₂

lemma sorted_insert : sorted' (insert k v z t) :=
begin
  induction h' generalizing z a b,
  case two_three.sorted'.leaf : k' v' z a b h
  { dsimp [insert], trichotomy k =? k' with h₂,
    all_goals
    { dsimp [first, last] at *,
      subst_vars, simp_min, saturate,
      apply sorted_split <|> apply sorted_close,
      repeat
      { assumption <|>
        constructor <|>
        simp_min <|> above } },  },
  case two_three.sorted'.node2 : h'_x h'_t₀ h'_t₁ h'_a h'_a_1 h'_a_2 h'_a_3 h'_ih_a h'_ih_a_1 z a b h h₀ h₁ h₂
  { dsimp [insert], subst_vars, split_ifs,
    all_goals
    { dsimp [first] at *,
      saturate, simp_min,
      try { have : first h'_t₀ ≤ k, { chain_trans } },
      apply h'_ih_a <|> apply h'_ih_a_1,
      repeat
      { assumption <|>
        constructor <|>
        simp_min <|> above, } } },
  case two_three.sorted'.node3 : h'_x h'_y h'_t₀ h'_t₁ h'_t₂ h'_a h'_a_1 h'_a_2 h'_a_3 h'_a_4 h'_a_5 h'_a_6 h'_ih_a h'_ih_a_1 h'_ih_a_2 z a b h h₀ h₁ h₂
  { dsimp [insert], subst_vars, split_ifs,
    all_goals
    { dsimp [first] at *,
      saturate, simp_min,
      try { have : first h'_t₀ ≤ k, { chain_trans } },
      apply h'_ih_a <|> apply h'_ih_a_1 <|> apply h'_ih_a_2,
      repeat
      { assumption <|>
        constructor <|>
        simp_min <|> above, } } },
end

lemma sorted_insert' : sorted' (insert' k v t) :=
by apply sorted_insert none none _ h'; constructor

end insert_sorted

end zipper

end two_three.tree
