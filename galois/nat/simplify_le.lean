/-
Copyright (c) 2017 Galois Inc.  All rights reserved.
Author: Joe Hendrix

This module defines operations for simplifying comparisons between
natural numbers.
-/
import data.nat.basic
import .simplify_eq

namespace nat

-- Reduce x < y to theorem with addition
protected theorem lt_is_succ_le (x y : ℕ) : x < y ↔ x + 1 ≤ y := by trivial

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

-- Reduce proof that product is greater than one to constraints
-- on variables.
lemma one_le_mul (m n : ℕ) : 1 ≤ m * n ↔ 1 ≤ m ∧ 1 ≤ n :=
begin
  cases n,
  case zero {
    simp [nat.le_zero_iff_eq_zero],
   },
  case succ n {
    simp [nat.mul_succ],
    cases (nat.eq_zero_or_pos m) with h h,
    {
      simp [h, le_zero_iff],
    },
    {
      have g : 1 ≤ m := h,
      simp [g, succ_le_succ_iff, nat.zero_le],
      transitivity,
      exact g,
      apply nat.le_add_right,
    },
  },
end

-- Reduce proof that power is greater than one to constraints
-- on variables.
lemma one_le_pow (m n : ℕ) : 1 ≤ m^n ↔ n = 0 ∨ 1 ≤ m :=
begin
  induction n,
  case zero { simp, },
  case succ n ind {
    simp [nat.pow, one_le_mul, ind],
    by_cases (1 ≤ m) with h,
    all_goals {
      simp [nat.lt_is_succ_le] at h,
      simp [h, not_succ_eq_zero],
    },
  },
end

------------------------------------------------------------------------
-- lt theorems

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
-- Specialized lemmas

protected lemma sub_add_iff : ∀(m n p : ℕ),
   (m - n) + p = if n ≤ m then (m + p) - n else p :=
begin
  intros m n p,
  revert n,
  induction m,
  case zero {
    intro n,
    simp,
    cases n,
    case zero { simp, },
    case succ { simp [nat.not_succ_le_zero], },
  },
  case succ m ind {
    intro n,
    cases n,
    case zero {
      simp [nat.zero_le],
    },
    case succ n {
      simp only [nat.succ_sub_succ],
      by_cases (n ≤ m) with h,
      {
        simp only [succ_le_succ_iff, h, ind, if_pos, succ_add, succ_sub_succ],
      },
      {
        simp [ind, if_neg, succ_le_succ_iff, h],
      }
    }
  }
 end

lemma le_add (a b : ℕ) : a ≤ a + b :=
begin
  induction b,
  case zero {
    exact less_than_or_equal.refl a,
  },
  case succ b ind {
    exact less_than_or_equal.step ind,
  },
end

end nat
