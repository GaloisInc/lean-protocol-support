/-
This module defines operations for simplifying equalities between lists.

-/

universe variable u

namespace list

variable { α : Type u}

@[simp]
theorem nil_eq_cons (a : α) (l : list α) : nil = (a :: l) ↔ false :=
begin
  simp,
  contradiction,
end

@[simp]
theorem cons_eq_nil (a : α) (l : list α) : (a :: l) = nil ↔ false :=
begin
  simp,
  contradiction,
end

@[simp]
theorem cons_eq_cons (a : α) (x : list α)  (b : α) (y : list α) : (a :: x) = (b :: y) ↔ a = b ∧ x = y :=
begin
  apply iff.intro,
  {
    intro p,
    injection p with p_a p_b,
    apply and.intro p_a p_b,
  },
  {
    intro h,
    exact congr (congr_arg _ (and.left h)) (and.right h),
  },
end

end list
