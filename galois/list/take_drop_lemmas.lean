/- This file contains lemmas for take and drop -/
import galois.nat.simplify_eq
import galois.nat.simplify_le
import data.list.basic

universe variable u

namespace list

variable {α : Type u}

/- take theorems -/
@[simp]
theorem take_succ_cons (n : ℕ) (x : α) (xs : list α) : take (nat.succ n) (x :: xs) = x :: take n xs := rfl

theorem take_cons_ite (n : ℕ) (e : α) (l : list α)
: take n (e :: l) = if n = 0 then [] else e :: take (n-1) l :=
begin
  cases n; simp,
end

theorem take_ge {n : ℕ} {l : list α} (pr : length l ≤ n): take n l = l :=
begin
  revert l,
  induction n with n ind,
  {
    intros l pr,
    cases l with a l,
    { simp },
    { simp [nat.add_succ, nat.not_succ_le_zero] at pr,
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
theorem take_length_self (l : list α) : take (length l) l = l := take_ge (nat.le_refl _)

@[simp]
theorem take_append : ∀(n : ℕ) (xs ys : list α), take n (xs ++ ys) = take n xs ++ take (n - length xs) ys
| 0 xs ys := by simp [nat.zero_sub, take_zero]
| (nat.succ n) nil ys :=
begin
  simp [nil_append, take_nil]
 end
| (nat.succ n) (x :: xs) ys :=
begin
  simp [cons_append, take_succ_cons],
  simp [take_append, cons_append, nat.succ_add],
 end

lemma take_bound {α : Type} {m n : ℕ} {l : list α}
(pr : l.length ≤ m)
(m_le_n : m ≤ n)
: l.take n = l.take m :=
begin
  revert m n,
  induction l,
  case nil { simp, },
  case cons e r ind {
    intros m n le_m le_n,
    cases m,
    case nat.zero {
      simp [nat.succ_add, nat.not_succ_le_zero] at le_m,
      contradiction,
    },
    case nat.succ m {
      cases n,
      case nat.zero {
        simp [nat.not_succ_le_zero] at le_n,
        contradiction,
      },
      case nat.succ n {
        simp [list.length, nat.succ_add, nat.succ_le_succ_iff] at le_m,
        simp [nat.succ_le_succ_iff] at le_n,
        simp [list.take],
        apply congr_arg,
        exact ind le_m le_n,
      }
    },
  }
end

/- drop theorems -/

@[simp]
theorem drop_zero (l : list α)
: drop 0 l = l := rfl

@[simp]
theorem drop_nil
: ∀ (n : ℕ), drop n nil = (nil : list α)
| 0 := rfl
| (nat.succ n) := rfl

@[simp]
theorem drop_cons (n : ℕ) (e : α) (l : list α)
: drop n (e :: l) = if n = 0 then (e :: l) else drop (n-1) l :=
begin
  cases n,
  simp,
  simp,
end

@[simp]
theorem drop_succ_cons (n : ℕ) (e : α) (l : list α)
: drop (nat.succ n) (e :: l) = drop n l := rfl

@[simp]
theorem drop_length_self : ∀ (xs : list α), drop (length xs) xs = []
| nil := by refl
| (cons x xs) := by simp [nat.add_succ, drop_succ_cons, drop_length_self]

@[simp]
theorem drop_append : ∀(n : ℕ) (xs ys : list α), drop n (xs ++ ys) = drop n xs ++ drop (n - length xs) ys
| 0 xs ys := by simp [nat.zero_sub, drop_zero]
| (nat.succ n) nil ys :=
begin
  simp [nil_append, drop_nil]
 end
| (nat.succ n) (x :: xs) ys :=
begin
  simp [cons_append, drop_succ_cons],
  simp [drop_append, nat.succ_add],
end

theorem drop_add {α : Type u} (l : list α) (i j : ℕ)
: l.drop (i + j) = (l.drop i).drop j :=
begin
  revert l j,
  induction i,
  case nat.zero { simp, },
  case nat.succ i ind {
    intros l j,
    cases l,
    case list.nil { simp only [list.drop_nil], },
    case list.cons e l {
      simp only [nat.succ_add, list.drop_succ_cons, ind],
    }
  }
end

/- Combination -/

theorem take_append_drop_self : ∀ (n : ℕ) (l : list α), take n l ++ drop n l = l
| 0            l          := rfl
| (nat.succ n) nil        := rfl
| (nat.succ n) (cons a l) := congr_arg (cons a) (take_append_drop_self n l)

theorem append_take_drop : ∀ (n : ℕ) (l : list α), take n l ++ drop n l = l
| 0            l          := rfl
| (nat.succ n) nil        := rfl
| (nat.succ n) (cons a l) := congr_arg (cons a) (append_take_drop n l)

theorem append_eq_take_drop (a x y : list α)
: a ++ x = y ↔ a = take (length a) y ∧ x = drop (length a) y :=
begin
  apply iff.intro,
  {
    intro h,
    simp [eq.symm h, nat.sub_self]
  },
  {
    intro h,
    rw [and.right h, and.left h, length_take],
    apply dite (length a ≤ length y),
    { intro le_pr,
      simp [min_eq_left le_pr, take_append_drop_self (length a) y ],
    },
    { intro lt_pr,
      have le_pr := le_of_not_le lt_pr,
      simp [min_eq_right le_pr, take_ge le_pr],
    }
  }
end

end list
