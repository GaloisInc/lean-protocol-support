/-
Copyright (c) 2017 Galois Inc.  All rights reserved.
Author: Joe Hendrix

This module defines operations for simplifying comparisons between natural numbers.
-/

namespace nat

@[simp]
theorem succ_le_succ_iff (x y : ℕ) : succ x ≤ succ y ↔ x ≤ y :=
begin
  apply iff.intro,
  exact nat.le_of_succ_le_succ,
  exact succ_le_succ,
end

theorem lt_is_succ_le (x y : ℕ) : x < y ↔ succ x ≤ y := by trivial

end nat
