/- Lemmas allowing for finding the first time that something eventual happens, when the thing is decidable -/
import .temporal
import galois.list
import galois.nat

universes u v w

private
def decide (P : Prop) [decidable P] : decidable P := by apply_instance

lemma first_seq (P : ℕ → Prop) [decidable_pred P] (n : ℕ) (Pn : P n)
  : ∃ n' : ℕ, P n' ∧ (∀ k : ℕ, k < n' → ¬ (P k))
:= begin
revert P,
induction n; intros,
{ existsi 0, split, assumption,
  intros, intros contra, rw <- nat.lt_zero_iff_false,
  assumption },
{ have H := ih_1 (λ i, P i.succ) _,
  { cases (decide (P 0)),
    { induction H with z Pz,
      induction Pz with Pz Pz',
      existsi (nat.succ z), split, assumption,
      intros, simp at Pz', cases k, assumption,
      apply Pz', apply nat.lt_of_succ_lt_succ, assumption,
    },
    { existsi 0, split, assumption,
     intros, intros contra, rw <- nat.lt_zero_iff_false,
     assumption },
  },
  { assumption }
}
end

namespace temporal
open list
/-- If P is decidable we can find all of the times it is true until N-/

lemma eventually_first_dec {T: Type u} (P : tProp T) [decidable_pred P] :
⊩ ◇ P => first P :=
begin
intros tr evP, induction evP with k Pk,
apply (first_seq (λ n, nextn n P tr) k Pk),
end

lemma not_weakuntil_yes {T : Type u}
  (P : tProp T) [decidable_pred P]
  : ⊩ tNot P 𝓦 P
:= begin
apply eventually_first_dec
end

lemma fair_first_dec {T: Type u} (P : tProp T) [decidable_pred P] :
⊩ fair P => □ (first P)
:= begin
unfold fair, apply always_tImp,
apply (always_tautology (◇ P=>first P)),
apply eventually_first_dec
end

/-- This is probably true, but I can't prove it yet... --/
lemma always_or_until {T : Type} (P Q : tProp T) [decidable_pred Q] :
  ⊩ □ (tOr P Q) => ◇ Q => P 𝓤 Q
:= begin
intros tr PQ evQ,
fapply until_always_mono, 
{ exact (tNot Q) },
{ intros n negQ, cases (PQ n),
  { assumption },
  { exfalso, apply negQ, assumption },
},
{ apply not_weakuntil_yes, assumption }
end

end temporal