import init.data.vector

lemma fin_0_empty (x : fin 0) : false :=
begin
induction x,
apply nat.lt_irrefl,
apply lt_of_le_of_lt, tactic.swap,
assumption, apply nat.zero_le,
end

lemma vector.nth_0 {A : Type _} {n : ℕ} (x : A) (xs : vector A n)
  {i : fin n.succ} (Hi : i.val = 0)
  : vector.nth (x :: xs) i = x
:= begin
induction i, dsimp at Hi,
subst val, induction xs,
dsimp [vector.nth, vector.cons], reflexivity
end