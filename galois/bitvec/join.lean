import data.bitvec
import galois.vector.join

namespace bitvec

definition join : Π {m n : ℕ}, vector (bitvec m) n → bitvec (m * n) := @vector.join bool
definition split : Π (m : ℕ) {n : ℕ}, bitvec (m * n) → vector (bitvec m) n := @vector.split bool
@[reducible]
definition join_list : Π {m : ℕ}, list (bitvec m) → list bool := @vector.join_list bool
@[reducible]
definition split_vector : Π {m : ℕ} (n : ℕ), bitvec (m * n) → list (bitvec m) := @vector.split_vector bool

end bitvec
