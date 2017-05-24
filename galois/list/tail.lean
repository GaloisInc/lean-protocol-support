import galois.nat.simplify_eq

universe variable u


namespace list

variable { α : Type u}

theorem tail_repeat (x : α) (n : ℕ) : tail (repeat x n) = repeat x (n - 1) :=
begin
  cases n,
  all_goals { simp },
end

theorem tail_append (x y : list α) : tail (x ++ y) = (if length x = 0 then tail y else tail x ++ y) :=
begin
  cases x,
  { simp },
  { simp [nat.succ_add], }
end

end list
