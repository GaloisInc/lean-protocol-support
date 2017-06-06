/-
This defines an operation fin_nth which gets the nth item on a list when the
index is guaranteed to reference a valid element.
-/
import galois.nat.simplify_le

universe variable u

namespace list

/--
Return the element in the list at the given index.

This is a total version of nth.
-/
def fin_nth {α : Type u} : Π (l : list α), fin (length l) →  α
| [] ⟨x, pr⟩ :=
begin
  simp [nat.lt_zero_iff_false] at pr,
  contradiction
end
| (h::r) ⟨0, pr⟩ := h
| (h::r) ⟨nat.succ i, p⟩ :=
  let q : i < length r :=
        begin
          simp [nat.succ_lt_succ_iff, nat.succ_add] at p,
          exact p,
        end in
  fin_nth r ⟨i,q⟩
end list
