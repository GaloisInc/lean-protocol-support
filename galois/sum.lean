def sum.left {a b} : a ⊕ b → option a
| (sum.inl a) := option.some a
| (sum.inr b) := option.none

def sum.right {a b} : a ⊕ b → option b
| (sum.inl a) := option.none
| (sum.inr b) := option.some b

-- Monad instance for sum
def sum.fmap {c a b} : (a → b) → c ⊕ a → c ⊕ b
| f (sum.inl e) := sum.inl e
| f (sum.inr v) := sum.inr (f v)

def sum.bind {c a b} : c ⊕ a → (a → c ⊕ b) → c ⊕ b
| (sum.inl e) f := sum.inl e
| (sum.inr a) f := f a

instance sum_is_monad {e} : monad (sum e) :=
{ pure := @sum.inr  e
, bind := @sum.bind e
, id_map := λα x,
  begin
    -- Split on x having form(inl y) or (inr y)
    cases x,
    -- Simplify each goal after exposing definitions
    all_goals { simp [monad.map._default, sum.bind, function.comp], },
  end
, pure_bind := λα β x f, by simp [sum.bind]
, bind_assoc :=
  begin
   intros α β γ x f g,
   cases x,
   all_goals { simp [sum.bind] },
  end
}

namespace sum

  universe variable u

  variables {α β e γ : Type u}

  def orelse : α ⊕ β → α ⊕ β → α ⊕ β
    | (sum.inl _) y := y
    | (sum.inr x) _ := sum.inr x

  variables (x : e) (f : α → sum e β)

  def left_zero : (sum.inl x >>= f) = sum.inl x := rfl

  @[simp] lemma inr_bind (x : α) (f : α → e ⊕ β) : (sum.inr x >>= f) = f x := rfl

  lemma inr_bind_helper {x : e ⊕ α} {y : α} {z : e ⊕ β} {f : α → e ⊕ β}
    (h₀ : x = sum.inr y)
    (h₁ : f y = z)
  : (x >>= f) = z :=
  by rw [h₀,inr_bind,h₁]

  lemma bind_assoc (x : e ⊕ α) (f : α → e ⊕ β) (g : β → e ⊕ γ)
  : ((x >>= f) >>= g) = ( x >>= (λ i, f i >>= g) ) :=
  begin
    cases x, simp [left_zero],
    rw [inr_bind,inr_bind]
  end

end sum
