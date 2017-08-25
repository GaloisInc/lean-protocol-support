/- Provides simplification lemmas for monad laws. -/
universe variables u

@[simp]
lemma pure_bind {m : Type u → Type u} [hm : monad m] {α β : Type u} (x : α) (f : α → m β) : pure x >>= f = f x :=
  monad.pure_bind x f

lemma bind_assoc {m : Type u → Type u} [hm : monad m] {α β γ : Type u} (x : m α) (f : α → m β) (g : β → m γ) :
  x >>= f >>= g = x >>= λ x, f x >>= g := monad.bind_assoc x f g

lemma when_false_unit {m : Type → Type} [monad m] {c : Prop} [h : decidable c]
  {t : m unit} (H : ¬ c) : when c t = pure ()
:= begin
unfold when, rw (if_neg H)
end

lemma when_false {m : Type → Type} [monad m] {c : Prop} [h : decidable c]
  {t : m unit} {A : Type} {f : m A} (H : ¬ c) : when c t >>= (λ _, f) = f
:= begin
rw (when_false_unit H), rw pure_bind
end

lemma when_false_trans {m : Type → Type} [monad m] {c : Prop} [h : decidable c]
  {t : m unit} {A : Type} {f g : m A} (H : ¬ c)
  (H' : f = g) : when c t >>= (λ _, f) = g
:= begin
rw (when_false H), assumption
end