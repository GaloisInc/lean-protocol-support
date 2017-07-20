/- Defines init and supporting function -/
import galois.list.simplify_eq

universe variable u

namespace list

variable {α : Type u}

theorem length_init : ∀ (l : list α), length (init l) = length l - 1
| nil := by simp [init]
| (x::l)   :=
begin
  have p := length_init l,
  cases l with b r,
  -- Case where l = nil
  { simp [init] },
  -- Case where l = b :: r
  {  simp [init, p, nat.add_sub_cancel, nat.add_sub_cancel_left], }
end

-- Maps a list with length 0 to nil
theorem length_0_implies_nil {l : list α} (h : length l = 0) : l = nil :=
begin
  cases l,
  simp,
  contradiction
end

-- Maps a non-empty list to the initial part and last part.
theorem init_append_last_self (l : list α) (pr : l ≠ nil) : init l ++ [last l pr] = l :=
begin
  revert pr,
  induction l with x l ind,
  { contradiction },
  { intros pr,
    cases l with y l,
    { simp [init] },
    { simp [init, last, ind (last._main._proof_2 y l)] }
  },
end

end list
