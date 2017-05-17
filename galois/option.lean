/- This module defines lemmas for option -/

universe variable u

namespace option

@[simp]
theorem is_some_none {α : Type u} : is_some (none : option α) = ff := rfl

end option
