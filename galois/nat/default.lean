import .simplify_eq .simplify_le .div_lemmas .lemmas


namespace nat

lemma pow_add' (b m n : ℕ): b^(m+n) = b^m * b^n :=
begin
  induction n,
  case zero {
    simp,
  },
  case succ n ind {
    simp [add_succ, pow_succ, ind],
  }
end

theorem add_mod_self : ∀ m n : ℕ, (m + n) % n = m % n :=
begin
  intros m n,
  cases n,
  case nat.zero { trivial, },
  case nat.succ n { simp, },
end

/-- Congruence rule for `le` and `add`. -/
def add_le_add_both {a b x y : ℕ} (p : a ≤ b) (q : x ≤ y) : a + x ≤ b + y :=
begin
  transitivity,
  apply nat.add_le_add_right p,
  apply nat.add_le_add_left q
end

/-- Congruence rule for `le` and `mul`. -/
def mul_le_mul_both {a b x y : ℕ} (p : a ≤ b) (q : x ≤ y) : a * x ≤ b * y :=
begin
  transitivity,
  apply nat.mul_le_mul_right x p,
  apply nat.mul_le_mul_left b q
end

end nat
