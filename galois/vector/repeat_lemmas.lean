universe variables u

namespace vector

variable {α : Type u}
variable {n : ℕ}

local infix `++`:65 := vector.append

@[simp]
theorem to_list_repeat (x : α) : to_list (repeat x n) = list.repeat x n :=
begin
  induction n,
  all_goals { simp [repeat] }
end

theorem repeat_succ_to_append {α : Type} (x : α) (n : ℕ)
  : repeat x (nat.succ n) = repeat x n ++ cons x nil :=
begin
  induction n with n ind,
  { apply vector.eq,
    simp [repeat]
  },
  {
    have h := congr_arg to_list ind,
    simp [vector.repeat] at h,
    apply vector.eq,
    simp [vector.repeat],
    rw h,
  },
end

end vector
