/- This defines init and last on vectors. -/
import galois.list.init
import .simplify_eq

universe variables u

namespace vector

variable {α : Type u}
variable {n : ℕ}

local infix `++`:65 := vector.append

-- Generate proof list non-null from proof length is sucessor some number
private
lemma eq_succ_implies_non_nil {l : list α} {n : ℕ} (pr : l^.length = nat.succ n) : l ≠ list.nil :=
begin
   cases l,
   all_goals {contradiction}
end

-- Return all but the last element of a vector
def init : vector α n → vector α (n-1)
| ⟨l,p⟩ := ⟨list.init l, eq.trans (list.length_init l) (congr_arg (λx, x - 1) p)⟩

-- Return last element in a non-empty vector.
def last : vector α (nat.succ n) → α
| ⟨l,p⟩ := list.last l (eq_succ_implies_non_nil p)

theorem init_append_last_self {n : ℕ} (x : vector α (nat.succ n)) 
: init x ++ vector.cons (last x) vector.nil = x :=
begin
  cases x with v p,
  simp [init, last, cons, nil, append, list.init_append_last_self v (eq_succ_implies_non_nil p)],
end

end vector
