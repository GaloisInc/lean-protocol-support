import galois.nat.simplify_eq

universe variable u

namespace list

variable { α : Type u}

theorem map_accumr₂_append1
  {α β γ φ : Type}
  (f : α → β → γ → γ × φ)
  (x : list α)
  (y : list β)
  (pr : length x = length y)
  (a : α)
  (b : β)
  (c : γ)
: map_accumr₂ f (x ++ [a]) (y ++ [b]) c =
  let r := f a b c in
  let z := map_accumr₂ f x y (r^.fst) in
  ⟨ z^.fst, z^.snd ++ [r^.snd]⟩ :=
begin
  revert y,
  induction x with xh xr ind,
  -- Base case with x = nil
  { intros y pr,
    cases y with yh yr,
    { simp [map_accumr₂] },
    { contradiction },
  },
  -- Inductive case with x = xh :: xr
  {
    intros y pr,
    cases y with yh yr,
    { contradiction },
    { simp [nat.succ_add] at pr,
      simp [map_accumr₂, ind yr pr]
    },
  }
end

end list
