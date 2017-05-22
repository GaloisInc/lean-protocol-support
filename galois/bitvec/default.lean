import .simplify_eq

namespace bitvec

-- Return all bitvectors with a given size.
def all : Π(k:ℕ), list (bitvec k)
| 0 := [bitvec.zero 0]
| (nat.succ k)
   := list.map (vector.cons ff) (all k)
   ++ list.map (vector.cons tt) (all k)

end bitvec
