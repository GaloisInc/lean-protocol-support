import .basic .simplify_eq  .init_last .map_accum_lemmas .repeat_lemmas .rotate .tail_lemmas .zero_length_lemmas

universe variables u

namespace vector

variable {α : Type u}

section ind

open nat

parameter {α' : Type u}

variables {P : ∀ {n : ℕ}, vector α' n → Prop}
variables {n : ℕ} (v : vector α' n)
variables h₀ : P nil
variables hn : ∀ {n : ℕ} (x : α') (v : vector α' n), P v → P (x :: v)

include hn

lemma induction : ∀ {n : ℕ} (v : vector α' n), P v
 | 0 ⟨[],P⟩ := h₀
 | (succ n) ⟨x :: xs, P⟩ :=
 begin
   apply hn x ⟨xs,_⟩ (induction ⟨xs, _⟩),
   have P' : succ (list.length xs) = succ n, { apply P },
   injection P',
 end

lemma induction_on : P v := induction h₀ @hn v

end ind

end vector
