import tactic.default .tactic .basic
universes u v w

namespace two_three

variables (α : Type u) (β : Type v) {γ : Type w}

open tree nat

variables {α β}

inductive liftp (p : α → Prop) : tree α β → Prop
| leaf {k v} : p k → liftp (tree.leaf k v)
| node2 {x} {t₀ t₁} : p x → liftp t₀ → liftp t₁ → liftp (tree.node2 t₀ x t₁)
| node3 {x y} {t₀ t₁ t₂} : p x → p y → liftp t₀ → liftp t₁ → liftp t₂ → liftp (tree.node3 t₀ x t₁ y t₂)
-- | node4 {x y z} {t₀ t₁ t₂ t₃} :
--   p x → p y → p z →
--   liftp t₀ → liftp t₁ →
--   liftp t₂ → liftp t₃ →
--   liftp (tree.node4 t₀ x t₁ y t₂ z t₃)

lemma liftp_true {t : tree α β} : liftp (λ _, true) t :=
begin
  induction t; repeat { trivial <|> assumption <|> constructor },
end

lemma liftp_map {p q : α → Prop} {t : tree α β} (f : ∀ x, p x → q x) (h : liftp p t) :
  liftp q t :=
begin
  induction h; constructor; solve_by_elim
end

lemma liftp_and {p q : α → Prop} {t : tree α β} (h : liftp p t) (h' : liftp q t) :
  liftp (λ x, p x ∧ q x) t :=
begin
  induction h; cases h'; constructor;
  solve_by_elim [and.intro]
end

lemma exists_of_liftp {p : α → Prop} {t : tree α β} (h : liftp p t) :
  ∃ x, p x :=
begin
  cases h; split; assumption
end

section defs
variables [has_le α] [has_lt α]

open tree nat

variables [@decidable_rel α (<)]

def insert' (x : α) (v' : β) :
  tree α β →
  (tree α β → γ) →
  (tree α β → α → tree α β → γ) → γ
| (tree.leaf y v) ret_one inc_two :=
  match cmp x y with
  | ordering.lt := inc_two (tree.leaf x v') y (tree.leaf y v)
  | ordering.eq := ret_one (tree.leaf y v')
  | ordering.gt := inc_two (tree.leaf y v) x (tree.leaf x v')
  end
| (tree.node2 t₀ y t₁) ret_one inc_two :=
  if x < y then
    insert' t₀
      (λ t',      ret_one $ tree.node2 t' y t₁)
      (λ ta k tb, ret_one $ tree.node3 ta k tb y t₁)
  else
    insert' t₁
      (λ t',      ret_one $ tree.node2 t₀ y t')
      (λ ta k tb, ret_one $ tree.node3 t₀ y ta k tb)
| (tree.node3 t₀ y t₁ z t₂) ret_one inc_two :=
  if x < y
    then insert' t₀
      (λ t',      ret_one $ tree.node3 t' y t₁ z t₂)
      (λ ta k tb, inc_two (tree.node2 ta k tb) y (tree.node2 t₁ z t₂))
  else if x < z
    then insert' t₁
      (λ t',      ret_one $ tree.node3 t₀ y t' z t₂)
      (λ ta k tb, inc_two (tree.node2 t₀ y ta) k (tree.node2 tb z t₂))
    else insert' t₂
      (λ t',      ret_one $ tree.node3 t₀ y t₁ z t')
      (λ ta k tb, inc_two (tree.node2 t₀ y t₁) z (tree.node2 ta k tb))

def insert (x : α) (v' : β) (t : tree α β) : tree α β :=
insert' x v' t id tree.node2

-- inductive shrunk (α : Type u) : ℕ
section add_

variables (ret shr : tree α β → γ)

def add_left : tree α β → α → tree α β → γ
| t₀ x t@(tree.leaf _ _) := ret t₀
| t₀ x (tree.node2 t₁ y t₂) := shr (tree.node3 t₀ x t₁ y t₂)
| t₀ x (tree.node3 t₁ y t₂ z t₃) := ret (tree.node2 (tree.node2 t₀ x t₁) y (tree.node2 t₂ z t₃))

def add_right : tree α β → α → tree α β → γ
| t@(tree.leaf _ _) x t₀ := ret t
| (tree.node2 t₀ x t₁) y t₂ := shr (tree.node3 t₀ x t₁ y t₂)
| (tree.node3 t₀ x t₁ y t₂) z t₃ := ret (tree.node2 (tree.node2 t₀ x t₁) y (tree.node2 t₂ z t₃))

variables (t₀ : tree α β) (x : α) (t₁ : tree α β) (y : α) (t₂ : tree α β)

def add_left_left : Π (t₀ : tree α β) (x : α) (t₁ : tree α β) (y : α) (t₂ : tree α β), γ
| t₀ x (tree.leaf k v)           z t₂ := ret t₀
| t₀ x (tree.node2 t₁ y t₂)      z t₃ := ret (tree.node2 (tree.node3 t₀ x t₁ y t₂) z t₃)
| t₀ w (tree.node3 t₁ x t₂ y t₃) z t₄ := ret (tree.node3 (tree.node2 t₀ w t₁) x (tree.node2 t₂ y t₃) z t₄)

def add_middle : Π (t₀ : tree α β) (x : α) (t₁ : tree α β) (y : α) (t₂ : tree α β), γ
| t@(tree.leaf k v)           y t₁ z t₂ := ret t
| (tree.node2 t₀ x t₁)      y t₂ z t₃ := ret (tree.node2 (tree.node3 t₀ x t₁ y t₂) z t₃)
| (tree.node3 t₀ w t₁ x t₂) y t₃ z t₄ := ret (tree.node3 (tree.node2 t₀ w t₁) x (tree.node2 t₂ y t₃) z t₄)

def add_right_right : Π (t₀ : tree α β) (x : α) (t₁ : tree α β) (y : α) (t₂ : tree α β), γ
| t₀ x (tree.leaf k v)           z t₂ := ret t₀
| t₀ x (tree.node2 t₁ y t₂)      z t₃ := ret (tree.node2 t₀ x (tree.node3 t₁ y t₂ z t₃))
| t₀ w (tree.node3 t₁ x t₂ y t₃) z t₄ := ret (tree.node3 t₀ w (tree.node2 t₁ x t₂) y (tree.node2 t₃ z t₄))

end add_

def delete' [decidable_eq α] (x : α) :
  tree α β →
  (option α → tree α β → γ) →
  (option α → tree α β → γ) →
  (unit → γ) → γ
| (tree.leaf y v) ret shr del :=
  if x = y then del () else ret (some y) (tree.leaf y v)
| (tree.node2 t₀ y t₁) ret shr del :=
  if x < y
    then delete' t₀ (λ a t', ret a $ tree.node2 t' y t₁)
                    (λ a t', add_left (ret a) (shr a) t' y t₁)
                    (λ _, shr (some y) t₁)
    else delete' t₁ (λ y' t', ret none $ tree.node2 t₀ (y'.get_or_else y) t')
                    (λ y' t', add_right (ret none) (shr none) t₀ (y'.get_or_else y) t')
                    (λ _, shr none t₀)
| (tree.node3 t₀ y t₁ z t₂) ret shr del :=
  if x < y
    then delete' t₀ (λ a t', ret a $ tree.node3 t' y t₁ z t₂)
                    (λ a t', add_left_left (ret a) t' y t₁ z t₂)
                    (λ _, ret (some y) $ tree.node2 t₁ z t₂)
  else if x < z
    then delete' t₁ (λ a t', ret none $ tree.node3 t₀ (a.get_or_else y) t' z t₂)
                    (λ a t', add_middle (ret none) t₀ y t' z t₂)
                    (λ _, ret none $ tree.node2 t₀ z t₂)
    else delete' t₂ (λ a t', ret none $ tree.node3 t₀ y t₁ (a.get_or_else z) t')
                    (λ a t', add_right_right (ret none) t₀ y t₁ z t')
                    (λ _, ret none $ tree.node2 t₀ y t₁)

def delete [decidable_eq α] (x : α) (t : tree α β) : option (tree α β) :=
delete' x t (λ _, some) (λ _, some) (λ _, none)

end defs

local attribute [simp] add_left add_right add_left_left add_middle add_right_right first last

variables [linear_order α]

-- #check @above_of_above_of_forall_le_of_le

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
tactic.interactive.casesm (some ()) [``(above _ (some _)), ``(below (some _) _), ``(below' (some _) _)],
tactic.find_all_hyps ``(sorted' _) $ λ h, do
{ n ← tactic.get_unused_name `h,
  tactic.mk_app ``first_le_last_of_sorted [h] >>= tactic.note n none,
  tactic.skip },
tactic.find_all_hyps ``(below _ _) $ λ h, do
{ n ← tactic.get_unused_name `h,
  tactic.mk_app ``eq_of_below [h] >>= tactic.note n none,
  tactic.skip },
tactic.find_all_hyps ``(¬ _ < _) $ λ h, do
{ -- n ← tactic.get_unused_name `h,
  tactic.mk_app ``le_of_not_gt [h] >>= tactic.note h.local_pp_name none,
  tactic.clear h,
  tactic.skip }

@[interactive]
meta def interactive.above : tactic unit := do
-- tactic.interactive.saturate,
tactic.find_hyp ``(above _ _) $ λ h, do
  tactic.refine ``(above_of_above_of_le _ %%h),
  tactic.interactive.chain_trans

section sorted_insert

variables (lb ub : option α)
  (P : γ → Prop)
  (ret : tree α β → γ)
  -- (ret' : tree α β → tree α β)
  (mk : tree α β → α → tree α β → γ)
  (h₀ : ∀ t,
      below lb (first t) →
      above (last t) ub →
    sorted' t → P (ret t))
  (h₂ : ∀ t₀ x t₁,
      below lb (first t₀) →
      above (last t₀) (some x) →
      below (some x) (first t₁) →
      above (last t₁) ub →
      sorted' t₀ → sorted' t₁ → P (mk t₀ x t₁))

include h₀ h₂

lemma sorted_insert_aux' {k : α} {v : β} {t}
  (h : sorted' t)
  (h' : below lb (min k (first t)))
  (h'' : above k ub)
  (h''' : above (last t) ub) :
    P (insert' k v t ret mk) :=
begin
  -- generalize_hyp hlb : none = k₀ at h,
  induction h generalizing lb ub ret mk,
  case two_three.sorted'.leaf : k' v'  lb ub ret mk h₀ h₂ h' h''
  { dsimp [insert'],
    trichotomy k =? k'; dsimp [insert']; apply h₀ <|> apply h₂,
    all_goals
    { try { have h := le_of_lt h },
      simp [first, h, min_eq_left, min_eq_right, min_self] at h', },
    repeat { assumption <|> constructor <|> refl } },
  case two_three.sorted'.node2 : x t₀ t₁ h h' h_a h_a_1
    h_ih₀ h_ih₁ lb ub ret mk h₀ h₂
  { dsimp [insert'],
    split_ifs; [apply @h_ih₀ lb (some x), apply @h_ih₁ (some x) ub]; clear h_ih₀ h_ih₁,
    all_goals
    { try { intros, apply h₀ <|> apply h₂ },
      clear h₀ h₂, },
    all_goals
    { casesm* [above _ (some _), below (some _) _],
      dsimp [first, last] at * { fail_if_unchanged := ff },
      repeat { assumption <|> constructor } },
    all_goals
    { find_all_hyps foo := ¬ (_ < _) then { replace foo := le_of_not_gt foo },
      find_all_hyps ht := sorted' _ then { have hh := first_le_last_of_sorted ht } },
    { rw min_eq_right at h'_1, assumption, chain_trans, },
    { have h : first t₀ ≤ k, chain_trans,
      have hh' := min_eq_right h, cc, },
    { subst x,
      rw min_eq_right h_1, constructor } },
  case two_three.sorted'.node3 : x y t₀ t₁ t₂ h_a h_a_1 h_a_2 h_a_3 h_a_4 h_a_5 h_a_6
    h_ih₀ h_ih₁ h_ih₂ lb ub ret mk h₀ h₂ h' h'' h'''
  { dsimp [insert'],
    split_ifs; [apply @h_ih₀ lb (some x), apply @h_ih₁ (some x) (some y), apply @h_ih₂ (some y) ub];
      clear h_ih₀ h_ih₁ h_ih₂,
    all_goals
    { try { intros, apply h₀ <|> apply h₂ },
      clear h₀ h₂, },
    all_goals
    { casesm* [above _ (some _), below (some _) _],
      subst_vars,
      dsimp [first, last] at * { fail_if_unchanged := ff },
      repeat { assumption <|> constructor } },
    all_goals
    { find_all_hyps foo := ¬ (_ < _) then { replace foo := le_of_not_gt foo },
      find_all_hyps ht := sorted' _ then { have hh := first_le_last_of_sorted ht },
      have h₀ : first t₀ ≤ k; [chain_trans, skip],
      try { have h₁ : first t₁ ≤ k; [chain_trans, skip] },
      try { have h₂ : first t₂ ≤ k; [chain_trans, skip] } },
    { have hh' := min_eq_right h₀, cc, },
    { have hh' := min_eq_right h₀, cc, },
    { rw min_eq_right h₁, constructor, },
    { have hh' := min_eq_right h₀, cc, },
    { have hh' := min_eq_right h₀, cc, },
    { rw min_eq_right h₂, constructor, } },
end

end sorted_insert

lemma sorted_insert {k : α} {v : β} {t : tree α β}
  (h : sorted' t) :
   sorted' (insert k v t) :=
sorted_insert_aux' none none _ _ _
  (λ t _ _ h, h)
  (λ t₀ x t₁ h₀ h₁ h₂ h₃ ht₀ ht₁, sorted'.node2 (by cases h₁; assumption) (by cases h₂; refl) ht₀ ht₁)
  h (by constructor) (by constructor) (by constructor)

section with_height_insert

variables (n : ℕ) (P : γ → Prop)
  (ret : tree α β → γ)
  (mk : tree α β → α → tree α β → γ)
  (h₀ : ∀ t, with_height n t → P (ret t))
  (h₂ : ∀ t₀ x t₁,
      with_height n t₀ → with_height n t₁ → P (mk t₀ x t₁))

include h₀ h₂

lemma with_height_insert_aux {k : α} {v : β} {t}
  (h : with_height n t) :
  P (insert' k v t ret mk) :=
begin
  induction h generalizing ret mk,
  case two_three.with_height.leaf : k' v'
  { dsimp [insert'],
    trichotomy k =? k',
    all_goals
    { dsimp [insert'], subst_vars, apply h₂ <|> apply h₀, repeat { constructor }, }, },
  case two_three.with_height.node2 : h_n h_x h_t₀ h_t₁ h_a h_a_1 h_ih₀ h_ih₁
  { dsimp [insert'], split_ifs,
    repeat { intro <|> apply h_ih₀ <|> apply h_ih₁ <|>
             apply h₀ <|> apply h₂ <|> assumption <|> constructor }, },
  case two_three.with_height.node3 : h_n h_x h_y h_t₀ h_t₁ h_t₂ h_a h_a_1 h_a_2 h_ih₀ h_ih₁ h_ih₂
  { dsimp [insert'], split_ifs,
    repeat { intro <|> apply h_ih₀ <|> apply h_ih₁ <|> apply h_ih₂ <|>
             apply h₀ <|> apply h₂ <|> assumption <|> constructor }, },
end

end with_height_insert

lemma with_height_insert {k : α} {v : β} {n t}
  (h : with_height n t) :
  with_height n (insert k v t) ∨
  with_height (succ n) (insert k v t) :=
begin
  apply with_height_insert_aux _ (λ t' : tree α β, with_height n t' ∨ with_height (succ n) t') _ _ _ _ h,
  { introv h', left, apply h' },
  { introv h₀ h₁, right, constructor; assumption }
end

section with_height_add_left

variables (n : ℕ) (P : γ → Prop)
  (ret shr : tree α β → γ)

variables
  (h₀ : ∀ t, with_height (succ (succ n)) t → P (ret t))
  (h₁ : ∀ t, with_height (succ n) t → P (shr t))

include h₀ h₁

lemma with_height_add_left {k : α} {t₀ t₁}
  (h : with_height n t₀)
  (h' : with_height (succ n) t₁) :
  P (add_left ret shr t₀ k t₁) :=
begin
  cases h'; dsimp [add_left],
  { apply h₁, repeat { assumption <|> constructor}, },
  { apply h₀, repeat { assumption <|> constructor}, },
end

lemma with_height_add_right {k : α} {t₀ t₁}
  (h : with_height (succ n) t₀)
  (h' : with_height n t₁) :
  P (add_right ret shr t₀ k t₁) :=
begin
  cases h; dsimp [add_right],
  { apply h₁, repeat { assumption <|> constructor}, },
  { apply h₀, repeat { assumption <|> constructor}, },
end

omit h₁

lemma with_height_add_left_left {k k' : α} {t₀ t₁ t₂}
  (hh₀ : with_height n t₀)
  (hh₁ : with_height (succ n) t₁)
  (hh₂ : with_height (succ n) t₂) :
  P (add_left_left ret t₀ k t₁ k' t₂) :=
begin
  cases hh₁; clear hh₁; dsimp; apply h₀,
  repeat { assumption <|> constructor },
end

lemma with_height_add_middle {k k' : α} {t₀ t₁ t₂}
  (hh₀ : with_height (succ n) t₀)
  (hh₁ : with_height n t₁)
  (hh₂ : with_height (succ n) t₂) :
  P (add_middle ret t₀ k t₁ k' t₂) :=
begin
  cases hh₀; clear hh₀; dsimp; apply h₀,
  repeat { assumption <|> constructor },
end

lemma with_height_add_right_right {k k' : α} {t₀ t₁ t₂}
  (hh₀ : with_height (succ n) t₀)
  (hh₁ : with_height (succ n) t₁)
  (hh₂ : with_height n t₂) :
  P (add_right_right ret t₀ k t₁ k' t₂) :=
begin
  cases hh₁; clear hh₁; dsimp; apply h₀,
  repeat { assumption <|> constructor },
end

end with_height_add_left


section with_height_delete

variables (n : ℕ) (P : γ → Prop)
  (ret shr : option α → tree α β → γ)
  (del : unit → γ)
  (h₀ : ∀ a t, with_height n t → P (ret a t))
  (h₁ : ∀ a t n', succ n' = n → with_height n' t → P (shr a t))
  (h₂ : ∀ u, n = 0 → P (del u))

include h₀ h₁ h₂

lemma with_height_delete_aux {k : α} {t}
  (h : with_height n t) :
  P (delete' k t ret shr del) :=
begin
  induction h generalizing ret shr del,
  case two_three.with_height.leaf : k' v'
  { dsimp [delete'],
    split_ifs,
    all_goals
    { subst_vars, apply h₂ <|> apply h₀ <|> apply h₁, repeat { constructor }, }, },
  case two_three.with_height.node2 : n h_x h_t₀ h_t₁ h_a h_a_1 h_ih₀ h_ih₁
  { dsimp [delete'], split_ifs,
    repeat { intro <|> apply h_ih₀ <|> apply h_ih₁ <|>
             apply h₀ <|> apply h₁ <|> apply with_height_add_left <|>
             apply with_height_add_right <|> assumption <|> constructor, try { subst_vars } } },
  case two_three.with_height.node3 : h_n h_x h_y h_t₀ h_t₁ h_t₂ h_a h_a_1 h_a_2 h_ih₀ h_ih₁ h_ih₂
  { dsimp [delete'], split_ifs,
    repeat { intro <|> apply h_ih₀ <|> apply h_ih₁ <|> apply h_ih₂ },
    all_goals
    { repeat { intro <|> apply h₀ <|> apply h₁ <|> apply h₂ <|>
               apply with_height_add_left <|>
               apply with_height_add_right <|>
               apply with_height_add_left_left <|>
               apply with_height_add_middle <|>
               apply with_height_add_right_right,  },
      repeat
      { subst_vars,
        assumption <|> constructor } }, },
end

end with_height_delete

lemma with_height_delete {n} {k : α} {t : tree α β}
  (h : with_height n t) :
  option.elim (delete k t) false (with_height n) ∨ option.elim (delete k t) (n = 0) (with_height n.pred) :=
with_height_delete_aux n (λ x : option (tree α β), option.elim x false (with_height n) ∨ option.elim x (n = 0) (with_height n.pred))
  (λ _, some) (λ _, some) _
  (by { dsimp, tauto })
  (by { dsimp, intros, subst n, tauto })
  (by { dsimp, tauto })
  h

section sorted_add_left

variables (P : γ → Prop)
  (lb ub : option α)
  (ret shr : tree α β → γ)

variables
  (h₀ : ∀ t, below lb (first t) → above (last t) ub → sorted' t → P (ret t))
  (h₁ : ∀ t, below lb (first t) → above (last t) ub → sorted' t → P (shr t))

include h₀ h₁

lemma sorted_add_left {k : α} {t₀ t₁}
  (hhₐ : below lb (first t₀))
  (hh₀ : sorted' t₀)
  (hh₁ : last t₀ < k)
  (hh₂ : k = first t₁)
  (hh₃ : sorted' t₁)
  (hh₄ : above (last t₁) ub) :
  P (add_left ret shr t₀ k t₁) :=
begin
  cases hh₃; clear hh₃; dsimp [add_left],
  all_goals
  { apply h₁ <|> apply h₀, clear h₀ h₁,
    repeat { assumption <|> constructor } },
  dsimp at *, subst_vars,
  cases hh₄; constructor,
  chain_trans
end

lemma sorted_add_right {k : α} {t₀ t₁}
  (hhₐ : below lb (first t₀))
  (hh₀ : sorted' t₀)
  (hh₁ : last t₀ < k)
  (hh₂ : k = first t₁)
  (hh₃ : sorted' t₁)
  (hh₄ : above (last t₁) ub) :
  P (add_right ret shr t₀ k t₁) :=
begin
  cases hh₀; clear hh₀; dsimp [add_left],
  all_goals
  { apply h₁ <|> apply h₀, clear h₀ h₁,
    repeat { assumption <|> constructor } },
  dsimp at *, subst_vars,
  cases hh₄; constructor,
  have := first_le_last_of_sorted hh₃,
  chain_trans
end

omit h₁

lemma sorted_add_left_left {k k' : α} {t₀ t₁ t₂}
  (hhₐ : below lb (first t₀))
  (hh₀ : sorted' t₀)
  (hh₁ : last t₀ < k)
  (hh₂ : k = first t₁)
  (hh₃ : sorted' t₁)
  (hh₄ : last t₁ < k')
  (hh₅ : k' = first t₂)
  (hh₆ : sorted' t₂)
  (hh₇ : above (last t₂) ub) :
  P (add_left_left ret t₀ k t₁ k' t₂) :=
begin
  cases hh₃; clear hh₃; dsimp at *,
  all_goals
  { saturate,
    subst_vars, apply h₀,
    repeat { assumption <|> constructor <|> above }, },
end

lemma sorted_add_middle {k k' : α} {t₀ t₁ t₂}
  (hhₐ : below lb (first t₀))
  (hh₀ : sorted' t₀)
  (hh₁ : last t₀ < k)
  (hh₂ : k = first t₁)
  (hh₃ : sorted' t₁)
  (hh₄ : last t₁ < k')
  (hh₅ : k' = first t₂)
  (hh₆ : sorted' t₂)
  (hh₇ : above (last t₂) ub) :
  P (add_middle ret t₀ k t₁ k' t₂) :=
begin
  cases hh₀; clear hh₀; dsimp; apply h₀; clear h₀,
  repeat { assumption <|> constructor <|> above },
end

lemma sorted_add_right_right {k k' : α} {t₀ t₁ t₂}
  (hhₐ : below lb (first t₀))
  (hh₀ : sorted' t₀)
  (hh₁ : last t₀ < k)
  (hh₂ : k = first t₁)
  (hh₃ : sorted' t₁)
  (hh₄ : last t₁ < k')
  (hh₅ : k' = first t₂)
  (hh₆ : sorted' t₂)
  (hh₇ : above (last t₂) ub) :
  P (add_right_right ret t₀ k t₁ k' t₂) :=
begin
  cases hh₃; clear hh₃; dsimp at *; apply h₀; clear h₀,
  repeat { assumption <|> constructor <|> above },
end

end sorted_add_left


section sorted_delete

variables
  (lb ub : option α)
  (P : γ → Prop)
  (ret shr : option α → tree α β → γ)
  (del : unit → γ)
  -- (h₀ : ∀ a t, sorted' t → P (ret a t))
  -- (h₁ : ∀ a t, sorted' t → P (shr a t))
  -- (h₀ : ∀ a t, below lb (first t) → below a (first t) → above (last t) ub → sorted' t → P (ret a t))
  -- (h₁ : ∀ a t, below lb (first t) → below a (first t) → above (last t) ub → sorted' t → P (shr a t))
  (h₀ : ∀ a t, below lb (first t) → above (last t) ub → sorted' t → P (ret a t))
  (h₁ : ∀ a t, below lb (first t) → above (last t) ub → sorted' t → P (shr a t))
  (h₂ : ∀ u, P (del u))

include h₀ h₁ h₂

lemma sorted_delete_aux {k : α} {t}
  (hh₀ : below lb (first t))
  (hh₁ : sorted' t)
  (hh₂ : above (last t) ub) :
  P (delete' k t ret shr del) :=
begin
  induction hh₁ generalizing lb ub ret shr del,
  case two_three.sorted'.leaf : k' v'
  { dsimp [delete'],
    split_ifs,
    all_goals
    { subst_vars, apply h₂ <|> apply h₀ <|> apply h₁,
      repeat { assumption <|> constructor <|> dsimp at * }, }, },
  case two_three.sorted'.node2 : n h_x h_t₀ h_t₁ hh₀ hh₁ hh₂ h_ih₀ h_ih₁
  { dsimp [delete'],
    find_all_hyps hh := sorted' _ then { have h := first_le_last_of_sorted hh },
    split_ifs,
    all_goals {
    try {
    repeat
    { repeat { intro h, try { have := first_le_last_of_sorted h } },
      apply h_ih₀ lb (some n) <|> apply h_ih₁ (some n) ub <|>
      casesm [above _ (some _)] <|>
      apply h₀ <|> apply h₁ <|> apply h₂ <|>
      apply sorted_add_left <|>
      apply sorted_add_right <|>
      apply sorted_add_left_left <|>
      apply sorted_add_middle <|>
      apply sorted_add_right_right <|>
      assumption <|> constructor,
      try { subst_vars } },
      done }
    },

    { apply h_ih₀ lb (some n); clear h_ih₀ h_ih₁,
      { intros, casesm* [above _ (some _)],
        apply h₀,
        repeat { assumption <|> constructor } },
      { intros, apply sorted_add_left,
        intros, apply h₀,
        repeat { assumption <|> constructor },
    all_goals
    { casesm* [above _ (some _)],
      repeat { intro <|> apply h₀ <|> apply h₁ <|> apply h₂ <|>
               apply with_height_add_left <|>
               apply with_height_add_right <|>
               apply with_height_add_left_left <|>
               apply with_height_add_middle <|>
               apply with_height_add_right_right,  } },
      repeat
      { subst_vars,
        intro <|> assumption <|> constructor } },

admit,
admit,
admit,
 },
admit
 },
admit,
  -- case two_three.sorted'.node3 : h_n h_x h_y h_t₀ h_t₁ h_t₂ h_a h_a_1 h_a_2 h_ih₀ h_ih₁ h_ih₂
  -- { dsimp [delete'], split_ifs,
  --   repeat { intro <|> apply h_ih₀ <|> apply h_ih₁ <|> apply h_ih₂ },
  --   all_goals
  --   { repeat { intro <|> apply h₀ <|> apply h₁ <|> apply h₂ <|>
  --              apply with_height_add_left <|>
  --              apply with_height_add_right <|>
  --              apply with_height_add_left_left <|>
  --              apply with_height_add_middle <|>
  --              apply with_height_add_right_right,  },
  --     repeat
  --     { subst_vars,
  --       assumption <|> constructor } }, },
end

end sorted_delete

end two_three
