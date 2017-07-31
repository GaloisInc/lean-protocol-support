/- This module defines lemmas for option -/

universe variables u v

namespace option

variables {α : Type u} {β : Type u}

@[simp]
theorem is_some_none  : is_some (none : option α) = ff := rfl

@[simp]
theorem is_some_some {α : Type} (x : α) : option.is_some (some x) = tt := rfl

@[simp]
theorem is_some_ff_to_none (x : option α) : is_some x = ff ↔ (x = none) :=
begin
  cases x,
  { simp, },
  { simp [is_some], contradiction, },
end

@[simp]
theorem has_map_none (f : α → β) : f <$> none = none := rfl

@[simp]
theorem has_map_some (f : α → β) (x : α) : f <$> some x = some (f x) := rfl

@[simp]
theorem none_orelse (x : option α) : (none <|> x) = x :=
begin
  cases x,
  all_goals { refl },
end

@[simp]
theorem some_orelse (x : α) (y : option α) : (some x <|> y) = some x := rfl

@[simp]
theorem orelse_none (x : option α) : (x <|> none) = x :=
begin
  cases x,
  all_goals { refl },
end

@[simp]
theorem option_is_some_plus (x y : option α)
: is_some (x <|> y) = is_some x || is_some y := do
begin
  cases x,
  all_goals { simp [is_some] },
end

@[simp]
theorem option_is_some_map (f : α → β) (x : option α)
: is_some (f <$> x) = is_some x := do
begin
  cases x,
  all_goals { simp [is_some] },
end

end option
