import galois.list.map_accum_lemmas
import galois.vector.zero_length_lemmas

universe variables u

namespace vector

variable {α : Type u}
variable {n : ℕ}

local infix `++`:65 := vector.append

-- Simplify map_accumr₂ over empty lists
@[simp]
theorem map_accumr₂_nil
  {α β γ φ : Type}
  (f : α → β → γ → γ × φ)
  (x : vector α 0)
  (y : vector β 0)
  (i₀ : γ)
: map_accumr₂ f x y i₀ = (i₀, nil) :=
begin
  simp [length_zero_vector_is_nil x, length_zero_vector_is_nil y
       , nil, map_accumr₂, list.map_accumr₂],
  apply congr_arg,
  apply vector.eq,
  simp,
end

-- Simplify map_accumr₂ over appending single element to end of lists
@[simp]
theorem map_accumr₂_append1
  {n : ℕ}
  {α β γ φ : Type}
  (f : α → β → γ → γ × φ)
  (x : vector α n) (a : α)
  (y : vector β n) (b : β)
  (c : γ)
: map_accumr₂ f (x ++ cons a nil) (y ++ cons b nil) c =
  let r := f a b c in
  let z := map_accumr₂ f x y (r.fst) in
  ⟨ z.fst, z.snd ++ cons r.snd nil⟩ :=
begin
  -- Reduce to proof about list.map_accumr₂ and use corresponding theorem
  cases x with xv xp,
  cases y with yv yp,
  have len_pr : xv^.length = yv^.length, { simp [xp, yp] },
  simp [vector.cons, vector.nil, vector.append, map_accumr₂],
  simp [list.map_accumr₂_append1 f _ _ len_pr],
end

end vector
