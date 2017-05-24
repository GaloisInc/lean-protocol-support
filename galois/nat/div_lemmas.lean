import .simplify_le

namespace nat

-- Dividing a positive number by a number greater than one results in a
-- a smaller number.
protected lemma div_lt_self : ∀{m n : ℕ}, m > 0 → n > 1 → m / n < m :=
begin
  intros m0,
  apply nat.strong_induction_on m0 _,
  intros m rec n m_gt_0 n_gt_1,
  rw [nat.div_def_aux],
  note n_gt_0 : n > 0 := lt_of_succ_lt n_gt_1,
  by_cases n ≤ m,
  { intro n_le_m,
    note m_gt_1 : 1 < m := nat.lt_of_lt_of_le n_gt_1 n_le_m,
    rw dif_pos (and.intro n_gt_0 n_le_m),
    by_cases n = m,
    { intro n_eq_m,
      simp [n_eq_m] at n_gt_1,
      simp [n_eq_m, nat.sub_self],
      exact n_gt_1,
    },

    { intro n_ne_m,
      transitivity,
      { apply nat.add_lt_add_right,
        { apply rec,
          { exact sub_lt m_gt_0 n_gt_0, },
          { note n_lt_m : n < m := nat.lt_of_le_and_ne n_le_m n_ne_m,
            simp [gt, nat.lt_sub, n_lt_m],
          },
          { exact n_gt_1, },
        },
      },
      { apply nat.sub_add_lt n_gt_1 m_gt_1,
      },
    },
  },
  { intro n_gt_m,
    rw [dif_neg],
    { exact m_gt_0, },
    { simp [n_gt_m], },
  }
end

end nat
