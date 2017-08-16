lemma nat.lt_succ_ne_lt (a b : ℕ) :
  a < nat.succ b →  a ≠ b → a < b :=
begin
intros lt ne,
cases lt with x succ_lt,
{ contradiction, },
{ exact succ_lt, }
end