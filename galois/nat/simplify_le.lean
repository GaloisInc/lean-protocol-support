/-
Copyright (c) 2017 Galois Inc.  All rights reserved.
Author: Joe Hendrix

This module defines operations for simplifying comparisons between
natural numbers.
-/

import data.nat.basic

namespace nat

------------------------------------------------------------------------
-- le theorems

protected lemma le_zero_iff_eq_zero (n : nat) : n ≤ 0 ↔ n = 0 :=
begin
  cases n,
  simp,
  { apply iff.intro,
    { intro h,
      have pr := not_succ_le_zero _ h,
      contradiction,
    },
    { contradiction, },
  },
end

------------------------------------------------------------------------
-- lt theorems

-- Reduce x < y to theorem with addition
protected theorem lt_is_succ_le (x y : ℕ) : x < y ↔ x + 1 ≤ y := by trivial

-- Reduce succ x < succ y
protected lemma succ_lt_succ_iff : ∀{m n : ℕ}, succ n < succ m ↔ n < m :=
begin
  intros m n,
  simp [nat.lt_is_succ_le, nat.succ_le_succ_iff],
end

-- This rewrites a subtraction on left-hand-side of inequality into an
-- addition, and one of two additional checks.
protected lemma sub_lt_iff (a m n : ℕ) : a - n < m ↔ (a < m + n ∧ (n ≤ a ∨ 0 < m)) :=
begin
  revert a m,
  induction n,
  case nat.zero {
    intros a m,
    simp [zero_le],
  },
  case nat.succ n ind {
    intros a m,
    cases a,
    case nat.zero { 
      simp [nat.zero_sub, zero_lt_succ, not_succ_le_zero],
    },
    case nat.succ { 
      simp [add_succ, nat.succ_lt_succ_iff, nat.succ_le_succ_iff, ind], 
    },
  },
end

-- This rewrites a subtraction on right-hand side of inequality into an addition.
protected lemma lt_sub_iff (a m n : ℕ) : a < m - n ↔ a + n < m :=
begin
  revert n,
  induction m with m ind,
  { simp [nat.lt_is_succ_le, add_succ, nat.not_succ_le_zero, nat.zero_sub],
  },
  { intro n,
    cases n with n,
    { simp, },
    { simp [nat.succ_lt_succ_iff, ind],
    },
  },
end

------------------------------------------------------------------------
-- Negation

-- This rewrites a negation of a le into a lt.
protected lemma lt_of_not_le : ∀(m n : ℕ),  ¬(n ≤ m) ↔ m < n :=
begin
  intros m n,
  apply iff.intro,
  { intro pr,
    cases (lt_trichotomy n m) with n_lt_m or_pr,
    { have n_le_m := pr (nat.le_of_lt n_lt_m),
      contradiction,
    },
    cases or_pr with n_eq_m m_lt_n,
    {
      simp [n_eq_m, nat.le_refl] at pr,
      contradiction,
    },
    { exact m_lt_n, },
  },
  { intros m_lt_n n_le_m,
    apply le_lt_antisymm n_le_m m_lt_n,
  },
end

------------------------------------------------------------------------
-- Specialized lemmas

-- Specialized lemma to prove theorem about subtracting then adding.
--
-- Note: We should see if we can eliminate this once arithmetic is done.
protected lemma sub_add_lt : ∀{m n p : ℕ}, p < n → p < m → m - n + p < m :=
begin
  intro m,
  induction m with m ind,
  { intros n p p_lt_n p_lt_zero,
    simp [nat.lt_is_succ_le, not_succ_le_zero] at p_lt_zero,
    contradiction,
  },
  {
    intros n p p_lt_n p_lt_succ_m,
    by_cases n ≤ m with pr,
    { rw [succ_sub pr, succ_add, nat.succ_lt_succ_iff],
      have p_lt_m : p < m := nat.lt_of_lt_of_le p_lt_n pr,
      apply ind p_lt_n p_lt_m,
    },
    { simp [nat.lt_of_not_le, nat.lt_is_succ_le] at pr,
      simp [sub_eq_zero_of_le pr, p_lt_succ_m],
    },
  },
end

end nat
