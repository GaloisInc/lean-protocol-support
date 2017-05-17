universe variables u v

meta def lens.get_set_tactic : tactic unit := do
  tactic.intro `v,
  tactic.intro `s,
  tactic.interactive.cases `(s) [],
  tactic.interactive.refl

meta def lens.set_get_tactic : tactic unit := do
  tactic.intro `s,
  tactic.interactive.cases `(s) [],
  tactic.interactive.refl

meta def lens.set_set_tactic : tactic unit := do
  tactic.intro `u,
  tactic.intro `v,
  tactic.intro `s,
  tactic.interactive.cases `(s) [],
  tactic.interactive.refl

structure lens (S : Type u) (α : Type v) :=
  (get : S → α)
  (set : α → S → S)
  (get_set :  ∀ (v : α) (s : S), get (set v s) = v . lens.get_set_tactic)
  (set_get :  ∀ (s : S), set (get s) s = s         . lens.set_get_tactic)
  (set_set :  ∀ (u v : α) (s : S), set u (set v s) = set u s . lens.set_set_tactic)

namespace lens

variables { s t : Type u }
variables { a b : Type v }

def over (l : lens s a) (f : a → a) (x : s) : s := lens.set l (f (lens.get l x)) x

end lens

infixr ` .~ `:4 := lens.set

infixr ` %~ `:4 := lens.over

@[reducible]
def call {a b} : a → (a → b) → b := λx f, f x

infixl ` & `:2 := call

@[simp]
theorem call_elim {α : Type u} {β : Type v} (f : α → β) (x : α) : (x & f) = f x :=  by simp [call]
