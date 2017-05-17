/- This defines subtype lemmas -/

universe variable u

namespace subtype

variable {α : Type u}
variable {P : α → Prop}

@[simp]
theorem mk_eq_mk (x : α) (p : P x) (y : α) (q : P y) : mk x p = mk y q ↔ x = y :=
begin
  apply iff.intro,
  {
    intro g,
    injection g with h,
    exact h
  },
  {
    intro p,
    simp [p],
  }
end

end subtype
