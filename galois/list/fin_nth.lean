/-
This defines an operation fin_nth which gets the nth item on a list when the
index is guaranteed to reference a valid element.
-/
import galois.nat.simplify_le
import init.data.fin.ops

universe variable u

namespace list

/--
Return the element in the list at the given index.

This is a total version of nth.
-/
def fin_nth {α : Type u} : Π (l : list α), fin l.length →  α
| [] ⟨x, pr⟩ :=
begin
  simp [nat.lt_is_succ_le, nat.add_succ, nat.not_succ_le_zero] at pr,
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

structure found_member {α : Type u} (x : α) (xs : list α) : Type :=
  (idx : fin xs.length)
  (lookup_eq : fin_nth _ idx = x)

lemma no_member_nil {α : Type u} (H : fin (@nil α).length) : false := 
begin
  cases H,
  simp [length] at is_lt,
  simp [nat.lt_is_succ_le, nat.add_succ, nat.not_succ_le_zero] at is_lt,
  contradiction
end

namespace fin
-- This is now in the standard library
-- https://github.com/leanprover/lean/blob/master/library/init/data/fin/ops.lean#L13-L14
protected def succ {n : ℕ } : fin n → fin (nat.succ n)
| ⟨a, h⟩ := ⟨nat.succ a, nat.succ_lt_succ h⟩
end fin

end list