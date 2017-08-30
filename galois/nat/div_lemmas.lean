import .simplify_le

namespace nat

theorem step_induction_on {C : ℕ → Prop} {c:ℕ} (c_pos:0 < c)
(base : ∀(m:ℕ), m < c → C m)
(step : ∀(m:ℕ), C m → C (m + c))
: ∀ (n:ℕ), C n :=
begin
  intro n,
  induction n using nat.strong_induction_on with n ind,
  by_cases (n < c),
  {
    exact base n h,
  },
  {
    have n_ge_c : n ≥ c := le_of_not_gt h,
    have n_pos : n > 0 := lt_of_lt_of_le c_pos n_ge_c,
    have cong : (n-c)+c = n := nat.sub_add_cancel n_ge_c,
    have lt : n-c < n := nat.sub_lt n_pos c_pos,
    rw [cong.symm],
    apply step,
    exact ind (n-c) lt,
  }
end

theorem mul_eq_add_mod (x y n : ℕ) : (x * n + y) % n = y % n :=
begin
  induction x,
  all_goals { simp, }
end

theorem mod_add_right_mod (x y n : ℕ) : (x + (y % n)) % n = (x + y) % n :=
begin
  by_cases 0 < n with h,
  {
    induction y using nat.step_induction_on with y y_lt_n y ind,
    exact n,
    exact h,
    -- base case
    { simp [mod_eq_of_lt, *],},
    -- inductive case
    { -- Simplify left-hand side
      simp only [mod_eq_sub_mod, add_sub_cancel, ge, le_add_left,
                 nat.add_sub_cancel, ind],
      -- Simplify right-hand side
      simp only [eq.symm (nat.add_assoc x y n),
                mod_eq_sub_mod (nat.le_add_left n (x+y))],
      simp only [nat.add_sub_cancel],
    },
  },
  {
    have n_eq_zero := eq_zero_or_pos n,
    simp [gt, h] at n_eq_zero,
    simp [n_eq_zero],
  }
end

theorem mod_mul_right_mod (x y n : ℕ) : x * (y % n) % n = (x * y) % n :=
begin
  by_cases 0 < n with h,
  {
    induction y using nat.step_induction_on with y y_lt_n y ind,
    exact n,
    exact h,
    { simp [mod_eq_of_lt, *],},
    { simp [mul_add, mul_eq_add_mod, ind], }
  },
  { have e := eq_zero_or_pos n,
    -- Simplify e to n = 0
    simp only [gt,h,or_false] at e,
    -- Replace n with 0 and simplify
    simp only [e,mod_zero],
  }
end

theorem mod_mul_left_mod (x y n : ℕ) : ((x % n) * y) % n = (x * y) % n :=
begin
  rw [nat.mul_comm],
  transitivity,
  apply mod_mul_right_mod,
  rw [nat.mul_comm],
end

-- Dividing a positive number by a number greater than one results in a
-- a smaller number.
protected lemma div_lt_self : ∀{m n : ℕ}, 0 < m → 1 < n → m / n < m :=
begin
  intros m0,
  apply nat.strong_induction_on m0 _,
  intros m rec n zero_lt_m n_gt_1,
  rw [nat.div_def_aux],
  have n_gt_0 : n > 0 := lt_of_succ_lt n_gt_1,
  by_cases n ≤ m with n_le_m,
  { have m_gt_1 : 1 < m := nat.lt_of_lt_of_le n_gt_1 n_le_m,
    rw dif_pos (and.intro n_gt_0 n_le_m),
    by_cases n = m with n_eq_m,
    { simp [n_eq_m] at n_gt_1,
      simp [n_eq_m, nat.sub_self],
      exact n_gt_1,
    },

    { rename n_eq_m n_ne_m, transitivity,
      { apply nat.add_lt_add_right,
        { apply rec,
          { exact sub_lt zero_lt_m n_gt_0, },
          { have n_lt_m : n < m := nat.lt_of_le_and_ne n_le_m n_ne_m,
            simp [gt, nat.lt_sub_iff, n_lt_m],
          },
          { exact n_gt_1, },
        },
      },
      { simp [nat.sub_add_iff, n_le_m, nat.sub_lt_iff, zero_lt_m],
        apply add_lt_add_left,
        exact n_gt_1,
      },
    },
  },
  { rename n_le_m n_gt_m,
    rw [dif_neg],
    { exact zero_lt_m, },
    { simp [n_gt_m], },
  }
end

end nat
