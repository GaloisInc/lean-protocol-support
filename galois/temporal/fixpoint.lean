import .temporal

open temporal

universes u

def iterate {A : Type u} (f : A → A) (x : A) : ℕ → A
| 0 := x
| (nat.succ n) := f (iterate n)

def least_fixpoint {T : Type u} (F : tProp T → tProp T) : tProp T
  := λ tr, ∃ (n : ℕ), iterate F ff n tr

def greatest_fixpoint {T : Type u} (F : tProp T → tProp T) : tProp T
  := λ tr, ∀ (n : ℕ), iterate F tt n tr

lemma prove_greatest_fixpoint {T : Type u} (F : tProp T → tProp T)
  (H : ∀ P, ⊩ P => F P)
  : ⊩ greatest_fixpoint F
:= begin
intros tr n, induction n; simp [iterate],
apply H, assumption
end