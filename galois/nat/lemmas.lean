import galois.tactic

lemma nat.lt_succ_ne_lt (a b : ℕ) :
  a < nat.succ b →  a ≠ b → a < b :=
begin
intros lt ne,
cases lt with x succ_lt,
{ contradiction, },
{ exact succ_lt, }
end


theorem nat.pow_not_zero2 (b e : ℕ) : b ^ e = 0 → b = 0
:= begin
induction e; simp [nat.pow], intros H,
apply_in H nat.eq_zero_of_mul_eq_zero,
induction H with H H,
{ assumption },
{ apply ih_1, assumption }
end

theorem nat.pow_not_zero2_contrapos (b e : ℕ) : b ≠ 0 → b ^ e ≠ 0
:= begin
intros H contra, apply H, 
apply nat.pow_not_zero2; assumption
end

@[simp]
theorem nat.pow_not_zero (b e : ℕ) : b ^ e.succ = 0 ↔ b = 0
:= begin
split; intros H,
{ apply nat.pow_not_zero2, assumption
},
{ rw nat.pow_succ, subst b, rw mul_zero }
end