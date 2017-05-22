/- This file contains lemmas for taken and dropn -/
import galois.nat.simplify_le

universe variable u

namespace list

variable {α : Type u}

/- Taken theorems -/

@[simp]
theorem taken_zero (xs : list α) : taken 0 xs = [] := rfl

@[simp]
theorem taken_nil : ∀ (n : ℕ), taken n list.nil = @list.nil α
| 0 := by refl
| (nat.succ n) := by refl

@[simp]
theorem taken_succ_cons (n : ℕ) (x : α) (xs : list α) : taken (nat.succ n) (x :: xs) = x :: taken n xs := rfl

theorem taken_ge {n : ℕ} {l : list α} (pr : length l ≤ n): taken n l = l :=
begin
  revert l,
  induction n with n ind,
  {
    intros l pr,
    cases l with a l,
    { simp },
    { simp [nat.add_succ, nat.succ_le_zero_iff_false] at pr,
      contradiction,
    }
  },
  { intros l pr,
    cases l with v l,
    { simp },
    { simp [nat.add_succ, nat.succ_le_succ_iff] at pr,
      simp [ind pr]
    }
  },
end

@[simp]
theorem taken_length_self (l : list α) : taken (length l) l = l := taken_ge (nat.le_refl _)

@[simp]
theorem taken_append : ∀(n : ℕ) (xs ys : list α), taken n (xs ++ ys) = taken n xs ++ taken (n - length xs) ys
| 0 xs ys := by simp [nat.zero_sub, taken_zero]
| (nat.succ n) nil ys :=
begin
  simp [nil_append, taken_nil]
 end
| (nat.succ n) (x :: xs) ys :=
begin
  simp [cons_append, taken_succ_cons],
  simp [taken_append, cons_append, nat.succ_add],
 end

/- dropn theorems -/

@[simp]
theorem dropn_zero (l : list α)
: dropn 0 l = l := rfl

@[simp]
theorem dropn_nil
: ∀ (n : ℕ), dropn n nil = (nil : list α)
| 0 := rfl
| (nat.succ n) := rfl

@[simp]
theorem dropn_succ_cons (n : ℕ) (e : α) (l : list α)
: dropn (nat.succ n) (e :: l) = dropn n l := rfl

@[simp]
theorem dropn_length_self : ∀ (xs : list α), dropn (length xs) xs = []
| nil := by refl
| (cons x xs) := by simp [nat.add_succ, dropn_succ_cons, dropn_length_self]

@[simp]
theorem dropn_append : ∀(n : ℕ) (xs ys : list α), dropn n (xs ++ ys) = dropn n xs ++ dropn (n - length xs) ys
| 0 xs ys := by simp [nat.zero_sub, dropn_zero]
| (nat.succ n) nil ys :=
begin
  simp [nil_append, dropn_nil]
 end
| (nat.succ n) (x :: xs) ys :=
begin
  simp [cons_append, dropn_succ_cons],
  simp [dropn_append, nat.succ_add],
end

/- Combination -/

theorem taken_append_dropn_self : ∀ (n : ℕ) (l : list α), taken n l ++ dropn n l = l
| 0            l          := rfl
| (nat.succ n) nil        := rfl
| (nat.succ n) (cons a l) := congr_arg (cons a) (taken_append_dropn_self n l)

theorem append_taken_dropn : ∀ (n : ℕ) (l : list α), taken n l ++ dropn n l = l
| 0            l          := rfl
| (nat.succ n) nil        := rfl
| (nat.succ n) (cons a l) := congr_arg (cons a) (append_taken_dropn n l)

theorem append_eq_taken_dropn (a x y : list α)
: a ++ x = y ↔ a = taken (length a) y ∧ x = dropn (length a) y :=
begin
  apply iff.intro,
  {
    intro h,
    simp [eq.symm h, nat.sub_self]
  },
  {
    intro h,
    rw [and.right h, and.left h, length_taken],
    apply dite (length a ≤ length y),
    { intro le_pr,
      simp [min_eq_left le_pr, taken_append_dropn_self (length a) y ],
    },
    { intro lt_pr,
      note le_pr := le_of_not_le lt_pr,
      simp [min_eq_right le_pr, taken_ge le_pr],
    }
  }
end

end list
