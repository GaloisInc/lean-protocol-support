/- Lemmas for basic logic -/

lemma contrapos {p q : Prop} (h : p → q) (g : ¬ q) : ¬ p := g ∘ h

lemma ite_iff {P Q : Prop}
  [decP : decidable P] [decQ : decidable Q]
  (H : P ↔ Q) {A}
  : @ite P _ A = ite Q
:= begin
apply funext, intros x, apply funext, intros y,
have decP' := decP,
cases decP' with HP HP, rw (if_neg HP),
rw if_neg, rw ← H, assumption,
rw (if_pos HP), rw if_pos, rw ← H, assumption,
end
