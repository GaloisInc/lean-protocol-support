/- Lemmas for simplify terms involving zero-length vectors. -/
import data.vector

universe variables u

namespace vector

variable {α : Type u}
variable {n : ℕ}

local infix `++`:65 := vector.append

theorem length_zero_vector_is_nil (x : vector α 0) : x = nil :=
begin
  apply vector.eq,
  cases x with v p,
  cases v,
  simp,
  contradiction
end

-- Simplify 0-length vector equality to true.
@[simp]
theorem zero_vec_always_eq (x y : vector α 0) : x = y ↔ true :=
begin
  simp [length_zero_vector_is_nil x, length_zero_vector_is_nil y],
end

@[simp]
theorem to_list_empty (x : vector α 0) : to_list x = list.nil :=
begin
  simp [length_zero_vector_is_nil x],
end

end vector
