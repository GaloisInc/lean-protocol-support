-- Mostly lemmas about arithmetic?
import data.rat

lemma add_neg_le_r {A} [linear_ordered_comm_ring A] (x y : A)
  : x + y ≥ 0 ↔ x ≥ - y
:= begin
dsimp [ge],
split; intros H,
{ apply (@le_of_add_le_add_left _ _ y),
  rw add_comm y,
  rw neg_add_self, rw add_comm, assumption, },
{ apply @le_of_add_le_add_left _ _ (-y),
  rw add_zero, rw add_comm, rw add_assoc,
  rw add_comm y, rw neg_add_self,
  rw add_zero, assumption,
}
end

lemma add_neg_le_l {A} [linear_ordered_comm_ring A] (x y : A)
  : x + y ≤ 0 ↔ x ≤ - y
:= begin
split; intros H,
{ apply (@le_of_add_le_add_left _ _ y),
  rw add_comm _ (-y),
  rw neg_add_self, rw add_comm, assumption, },
{ apply @le_of_add_le_add_left _ _ (-y),
  rw add_zero, rw add_comm, rw add_assoc,
  rw add_comm y, rw neg_add_self,
  rw add_zero, assumption,
}
end

lemma add_le_zero1 {A} [linear_ordered_comm_ring A] (x y : A)
  : 0 ≤ y - x ↔ x ≤ y
:= begin
split; intros H,
{ rw ← (add_zero x), apply le_trans,
  apply add_le_add_left, assumption,
  rw ← add_sub_assoc, rw add_comm,
  rw add_sub_cancel, },
{ apply le_trans, tactic.swap, apply add_le_add_right,
  assumption, rw add_comm, rw neg_add_self }
end



lemma mul_le_zero_pos (c x : ℚ) (Hc : 0 < c)
  : x ≤ 0 ↔ c * x ≤ 0
:= begin
split; intros H,
{ apply mul_nonpos_of_nonneg_of_nonpos,
  apply le_of_lt, assumption, assumption, },
{ apply nonpos_of_mul_nonpos_left; assumption, }
end

lemma lt_zero_neg (c : ℚ)
  : c < 0 ↔ - c > 0
:= begin
split; intros H,
{ rw ← neg_zero,
  apply neg_lt_neg _, assumption, },
{ rw ← neg_zero,
  rw ← (neg_neg c),
  apply neg_lt_neg _, assumption }
end

lemma mul_le_zero_neg (c x : ℚ) (Hc : c < 0)
  : x ≤ 0 ↔ c * x ≥ 0
:= begin
split; intros H,
{ apply mul_nonneg_of_nonpos_of_nonpos,
  apply le_of_lt, assumption, assumption, },
{ apply nonpos_of_mul_nonpos_left, tactic.swap,
  rw lt_zero_neg at Hc, apply Hc,
  rw ← neg_mul_eq_neg_mul,
  apply neg_le_of_neg_le, rw neg_zero, assumption,
 }
end

lemma mul_le_zero_neg_le (c x : ℚ) (Hc : c < 0)
  : x ≤ 0 ↔ 0 ≤ c * x
:= mul_le_zero_neg c x Hc

lemma neg_le_neg_opp (x y : ℚ)
  : - y ≤ - x → x ≤ y
:= begin
intros H, rw ← (neg_neg x), rw ← (neg_neg y),
apply neg_le_neg, assumption,
end

lemma add_zero_l (n : ℚ) : 0 + n = n
:= by simp

lemma add_le_zero2 (x y : ℚ)
  : x - y ≤ 0 ↔ x ≤ y
:= begin
rw ← add_le_zero1,
rw sub_eq_add_neg,
rw neg_sub, rw add_zero_l,
rw add_le_zero1,
end

lemma mul_le_mono_neg (c x y : ℚ) (Hc : c < 0)
  (H : x ≤ y) : c * y ≤ c * x
:= begin
rw ← add_le_zero1, rw ← mul_sub,
rw ← mul_le_zero_neg_le, rw add_le_zero2, assumption,
assumption,
end

lemma mul_le_mono_pos (c x y : ℚ) (Hc : c > 0)
  (H : x ≤ y) : c * x ≤ c * y
:= begin
rw ← add_le_zero1, rw ← mul_sub,
apply mul_nonneg, apply le_of_lt, assumption,
unfold ge, rw add_le_zero1, assumption,
end

lemma gt_of_not_eq_lt
  {x : ℚ}
  (Heq : x ≠ 0) (Hlt : ¬ x < 0)
  : x > 0
:= begin
unfold gt,
rw lt_iff_not_ge,
intros contra,
apply Hlt,
intros contra, apply Heq,
rw le_antisymm_iff, split; assumption,
end

lemma rat.inv_pos (x : ℚ) (Hx : 0 < x) : 0 < x⁻¹
:= begin
have H : 0 < x * x⁻¹,
rw mul_inv_cancel, exact_dec_trivial,
apply ne_of_gt, assumption,
have H' := pos_and_pos_or_neg_and_neg_of_mul_pos H,
induction H' with H' H'; induction H' with H1 H2, assumption,
exfalso, clear H H2,
rw lt_iff_not_ge at Hx, apply Hx,
apply le_of_lt, assumption,
end