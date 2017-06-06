def sum.left {a b} : a ⊕ b → option a
| (sum.inl a) := option.some a
| (sum.inr b) := option.none

def sum.right {a b} : a ⊕ b → option b
| (sum.inl a) := option.none
| (sum.inr b) := option.some b

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

  @[simp]
  theorem map_inl (f : α → β) (x : e) : f <$> (@sum.inl e α x) = sum.inl x := rfl

  @[simp]
  theorem map_inr (f : α → β) (x : α) : f <$> (@sum.inr e α x) = sum.inr (f x) := rfl

  @[simp]
  theorem inl_bind (x : e) (h : α → sum e β)  : (@sum.inl e α x) >>= h = sum.inl x := rfl

  @[simp]
  theorem inr_bind (x : α) (f : α → e ⊕ β) : (sum.inr x >>= f) = f x := rfl

  def orelse : e ⊕ β → α ⊕ β → α ⊕ β
    | (sum.inl _) y := y
    | (sum.inr x) _ := sum.inr x
end sum
