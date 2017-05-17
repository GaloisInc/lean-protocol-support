/- Lemmas for tail, and a total tail function. -/
import data.vector
import galois.list.tail

universe variables u

namespace vector

variable {α : Type u}
variable {n : ℕ}

@[simp]
theorem to_list_tail (v : vector α (nat.succ n)) : to_list (tail v) = list.tail (to_list v) :=
begin
  cases v,
  cases val,
  contradiction,
  simp [ tail ],
end

-- Extends tail to work over total functions
def total_tail : vector α n → vector α (n - 1)
| ⟨ v, h ⟩ := ⟨ list.tail v, eq.trans (list.length_tail v) (congr_arg (λ x, x - 1) h) ⟩

@[simp]
theorem to_list_total_tail (v : vector α n) : to_list (total_tail v) = list.tail (to_list v) :=
begin
  cases v,
  simp [ total_tail ],
end

end vector
