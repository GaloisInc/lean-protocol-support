/-
Defines an additional theorem over orders.
-/

/-- Show that for linear orders le is equivalent to not_gt.

N.B. This is the inverse of lt_iff_not_ge.
-/
protected lemma le_iff_not_gt  {α : Type} [linear_order α] (x y : α)
: (x ≤ y) ↔ ¬(x > y) :=
  iff.intro not_lt_of_ge le_of_not_gt
