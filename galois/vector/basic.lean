/- Defines very basic lemmas for vector -/
import data.vector

universe variables u

namespace vector

variable {α : Type u}
variable {n : ℕ}

@[simp]
theorem length_to_list : ∀ (x : vector α n), x.to_list.length = n
| ⟨ l, p ⟩ := p

end vector
