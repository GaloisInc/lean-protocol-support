lemma nat.lt_succ_ne_lt : forall a b,
a < nat.succ b ->
a ≠ b ->
a < b :=
begin
intros,
have H := nat.le_of_lt_succ a_1, clear a_1,
have H' := nat.lt_or_eq_of_le H, clear H,
induction H' with H H, assumption, contradiction,
end