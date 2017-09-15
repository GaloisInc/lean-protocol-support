/-
This module defines an exponentiation function where the exponent
is a natural number, and the base is a monoid.

It uses an efficient sum of squares method to support large exponents.
-/

import .simplify_eq

universe u

namespace nat

section exp

parameter {α : Type u}
parameter [inst : monoid α]

include inst

def exp.f (x : α) (b:bool) (n : ℕ) (r:α) : α :=
  if b then
    x * r * r
  else
    r * r

def exp (x : α) (n : ℕ) : α := nat.binary_rec 1 (exp.f x) n

theorem exp_zero : ∀ (x : α) , exp x 0 = 1 :=
begin
  intro x,
  unfold exp,
  unfold binary_rec,
  simp [eq.mpr],
end

theorem exp_one (x : α) : exp x 1 = x :=
begin
  unfold exp,
  unfold binary_rec,
  simp [exp.f, eq.mpr],
  dsimp [div2_one],
  unfold binary_rec,
  simp [eq.mpr],
  rw if_pos, constructor,
end

theorem exp_bit (x : α) (b:bool) (n:ℕ)
: exp x (bit b n) = (if b then x else 1) * exp x n * exp x n :=
begin
  transitivity,
  unfold1 exp,
  rw binary_rec_eq,
  simp [exp.f],
  cases b; simp [exp],
  rw if_neg, rw if_neg, simp, contradiction, contradiction,
  rw if_pos, rw if_pos, constructor, constructor,
  dsimp [exp.f], rw if_neg, simp,
  contradiction,
end

theorem exp_bit0 (x : α) (n:ℕ)
: exp x (bit0 n) = exp x n * exp x n :=
begin
  have p := exp_bit x ff n,
  simp [bit] at p,
  rw if_neg at p, simp at p,
  exact p, contradiction,
end

theorem exp_bit1 (x : α) (n:ℕ)
: exp x (bit1 n) = x * (exp x n * exp x n) :=
begin
  have p := exp_bit x tt n,
  simp [bit, mul_assoc] at p,
  exact p,
end

theorem exp_succ_identities
: ∀(x:α)(n:ℕ),
      x * exp x n = exp x (succ n)
    ∧ exp x n * x = exp x (succ n) :=
begin
  intros x n,
  revert x,
  revert n,

  apply @nat.binary_rec
    (λ(n:ℕ), (∀(x : α),
       x * exp x n = exp x (succ n)
     ∧ exp x n * x = exp x (succ n))),
  {
    simp [exp_one, exp_zero],
  },
  {
    intros b n ind x,
    have ind_left := λx, (ind x).left,
    have ind_right := λx, (ind x).right,
    cases b,

    case tt {
      simp only [ bit, cond ],
      rw [ nat.succ_bit1, exp_bit0, exp_bit1 ],

      apply and.intro,
      { transitivity,
        rw [← mul_assoc x (exp x n), ind_left, ← ind_right],
        -- Collect first successor
        rw [mul_assoc, ind_left],
        -- Collect second
        rw [← mul_assoc, ind_left],
      },
      {
        rw [mul_assoc, mul_assoc, ind_right],
        rw [← mul_assoc, ind_left],
      }
    },
    case ff {
      simp only [bit, cond],
      rw [← nat.bit1_eq_succ_bit0, exp_bit0, exp_bit1],
      apply and.intro,
      { trivial, },
      {
        -- Move extra x from right to left.
        rw [mul_assoc, ind_right],
        rw [← ind_left, ← mul_assoc, ind_right, ← ind_left],
        rw [mul_assoc],
      }
    }
  }
end

end exp

end nat
