import .simplify_eq

namespace bitvec

-- Unsigned extension
def uext {m :ℕ } (x:bitvec m) (n:ℕ) (pr : m ≤ n) : bitvec n :=
  let q : n - m + m = n := nat.sub_add_cancel pr in
  bitvec.cong q (bitvec.append (bitvec.zero (n-m)) x)

-- Return all bitvectors with a given size.
def all : Π(k:ℕ), list (bitvec k)
| 0 := [bitvec.zero 0]
| (nat.succ k)
   := list.map (vector.cons ff) (all k)
   ++ list.map (vector.cons tt) (all k)

protected def to_string {n : nat} (x : bitvec n) : string := has_to_string.to_string x.to_nat

instance (n : nat) : has_to_string (bitvec n) := ⟨bitvec.to_string⟩

end bitvec
