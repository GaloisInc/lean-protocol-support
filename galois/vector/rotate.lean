import data.vector
import galois.list.rotate

namespace vector

  variables {T : Type} {k : ℕ}

  definition rol : vector T k → ℕ → vector T k
  | ⟨ l, h ⟩ n := ⟨ list.rol l n, show list.length (list.rol l n) = k, from eq.trans (list.length_rol _ _) h ⟩

  definition ror : vector T k → ℕ → vector T k
  | ⟨ l, h ⟩ n := ⟨ list.ror l n, show list.length (list.ror l n) = k, from eq.trans (list.length_ror _ _) h ⟩

end vector
