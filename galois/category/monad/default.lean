/- Provides simplification lemmas for monad laws. -/
universe variables u

@[simp]
lemma pure_bind {m : Type u → Type u} [hm : monad m] {α β : Type u} (x : α) (f : α → m β) : pure x >>= f = f x :=
  monad.pure_bind x f

lemma bind_assoc {m : Type u → Type u} [hm : monad m] {α β γ : Type u} (x : m α) (f : α → m β) (g : β → m γ) :
  x >>= f >>= g = x >>= λ x, f x >>= g := monad.bind_assoc x f g
