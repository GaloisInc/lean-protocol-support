/- Lemmas for basic logic -/

lemma contrapos {p q : Prop} (h : p → q) (g : ¬ q) : ¬ p := g ∘ h
