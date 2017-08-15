import galois.vector.rotate

namespace bitvec
  variables {n : ℕ}

  definition rol : bitvec n → ℕ → bitvec n := vector.rol
  definition ror : bitvec n → ℕ → bitvec n := vector.ror

end bitvec
