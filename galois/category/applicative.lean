/- Provides simplification lemmas for applicative laws. -/

universe variables u

@[simp]
lemma fmap_pure {m : Type u → Type u} [hm : applicative m] {α β : Type u} (f : α → β) (v : α) :
  f <$> (pure v : m α) = pure (f v) := applicative.map_pure m f v
