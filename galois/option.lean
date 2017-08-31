/- This module defines lemmas for option -/

universe variables u v

run_cmd mk_simp_attr `simp_option

namespace option

variables {α : Type u} {β : Type u}

@[simp_option]
theorem is_some_none  : is_some (none : option α) = ff := rfl

@[simp_option]
theorem is_some_some {α : Type} (x : α) : option.is_some (some x) = tt := rfl

@[simp_option]
theorem is_some_ff_to_none (x : option α) : is_some x = ff ↔ (x = none) :=
begin
  cases x,
  { simp with simp_option, },
  { simp [is_some], contradiction, },
end

@[simp_option]
theorem has_map_none (f : α → β) : f <$> none = none := rfl

@[simp_option]
theorem has_map_some (f : α → β) (x : α) : f <$> some x = some (f x) := rfl

@[simp_option]
theorem none_orelse (x : option α) : (none <|> x) = x :=
begin
  cases x,
  all_goals { refl },
end

@[simp_option]
theorem some_orelse (x : α) (y : option α) : (some x <|> y) = some x := rfl

@[simp_option]
theorem orelse_none (x : option α) : (x <|> none) = x :=
begin
  cases x,
  all_goals { refl },
end

@[simp_option]
theorem option_is_some_plus (x y : option α)
: is_some (x <|> y) = is_some x || is_some y := do
begin
  cases x; simp [is_some] with simp_option,
end

@[simp_option]
theorem option_is_some_map (f : α → β) (x : option α)
: is_some (f <$> x) = is_some x := do
begin
  cases x; simp [is_some] with simp_option,
end

lemma bind_some {A B} {ma : option A} {f : A → option B}
  {b : B} (H : option_bind ma f = some b)
  : ∃ a : A, ma = some a ∧ f a = some b
:= begin
cases ma,
contradiction,
existsi a, split, reflexivity, assumption
end

lemma map_some {A B} {ma : option A} {f : A → B}
  {b : B} (H : option_map f ma = some b)
  : ∃ a : A, ma = some a ∧ f a = b
:= begin
cases ma,
contradiction,
existsi a, split, reflexivity,
dsimp [option_map, function.comp, option_bind] at H,
injection H with H',
end

def filter {A : Type u}
   (P : A → Prop) [decidable_pred P] : option A → option A
| (some x) := if P x then some x else none
| none := none

lemma filter_some {A : Type u}
  {P : A → Prop} [decP : decidable_pred P] {mx : option A} {x : A}
  (H : mx.filter P = some x)
  : mx = some x ∧ P x
:= begin
cases mx; simp [option.filter] at H,
contradiction,
have H' := decP a, induction H' with H' H',
{ rw (if_neg H') at H, contradiction, },
{ rw (if_pos H') at H, injection H with H'', clear H,
  subst x, constructor, reflexivity, assumption }
end

def guard_filter {A : Type}
  {P : Prop} [decP : decidable P] (mx : option A) :
  (do guard P, mx) = mx.filter (λ _, P)
:= begin
induction mx; induction decP; try { reflexivity }
end

lemma filter_true {A : Type u}
  {P : A → Prop} [decP : decidable_pred P] {x : A}
  (H : P x)
  : (some x).filter P = some x
:= begin
unfold option.filter, rw (if_pos H),
end

def precondition (P : Prop) [decP : decidable P] : option (plift P) :=
  match decP with
  | decidable.is_true H := some (plift.up H)
  | decidable.is_false contra := none
  end

lemma precondition_true {P : Prop} {A : Type u} [decP : decidable P]
  {f : plift P → option A}
  (H : P)
  : option_bind (precondition P) f = f (plift.up H)
:= begin
unfold precondition,
induction decP; dsimp [precondition],
{ contradiction },
{ simp [option_bind],
}
end

lemma precondition_false {P : Prop} [decP : decidable P]
  (H : ¬ P)
  : precondition P = none
:= begin
unfold precondition,
induction decP; dsimp [precondition],
{ simp [option_bind], },
{ contradiction
}
end

lemma precondition_true_bind {P : Prop} {A : Type} [decP : decidable P]
  {f : plift P → option A}
  (H : P)
  : precondition P >>= f = f (plift.up H)
:= precondition_true H

lemma map_compose {A B C} (f : A → B) (g : B → C)
  : option_map (g ∘ f) = option_map g ∘ option_map f
:= begin
apply funext; intros x, induction x; reflexivity,
end

inductive Issome {A} : option A -> Prop
  | MkIsSome : forall a : A, Issome (some a)

lemma not_Issome_none {A : Type} : ¬ Issome (@none A) :=
begin
generalize b : (@none A) = a,
intros contra,
induction contra,
contradiction
end

end option
