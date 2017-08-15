/- Lemmas allowing for finding the first time that something eventual happens, when the thing is decidable -/
import .temporal
import galois.list
import galois.nat

universes u v w

protected
def decide (P : Prop) [decidable P] : decidable P := by apply_instance

lemma first_seq (P : ℕ → Prop) [decidable_pred P] (n : ℕ) (Pn : P n)
  : ∃ n' : ℕ, P n' ∧ (∀ k : ℕ, k < n' → ¬ (P k))
:= begin
revert P,
induction n; intros,
{ existsi 0, split, assumption,
  intros, intros contra, 
  exact nat.not_lt_zero k a,
},
{ have H := ih_1 (λ i, P i.succ) _,
  { cases (decide (P 0)),
    { induction H with z Pz,
      induction Pz with Pz Pz',
      existsi (nat.succ z), split, assumption,
      intros, simp at Pz', cases k, assumption,
      apply Pz', apply nat.lt_of_succ_lt_succ, assumption,
    },
    { existsi 0, split, assumption,
      intros, intros contra,
      exact nat.not_lt_zero k a_2,
    },
  },
  { assumption }
}
end

namespace temporal
open list

/-- If P is decidable and eventually holds, we can find the first time
    that it holds.
-/
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

lemma always_weak_until {T : Type u} (P Q : tProp T) [decidable_pred Q] :
  ⊩ □ (tOr P Q) => P 𝓦 Q
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

/-- An anologue of `temporal_induction`. If we can prove
    `P` holds now, and if, assuming `Q` doesn't hold,
    `P` implies `◯ P`, then `◯ P` holds weak-until `Q`.
-/
lemma weak_until_induction {T : Type u} (P Q : tProp T)
  [decidable_pred Q]
  : ⊩ (P => □ (tNot Q => P => (◯ P)) => ◯ P 𝓦 Q) :=
begin
intros tr H0 HS evQ,
have firstQ := eventually_first_dec _ _ evQ, clear evQ,
induction firstQ with k Hk, induction Hk with H H',
constructor, split, assumption,
intros n H, revert k,
induction n; intros,
{ apply HS, apply H', assumption,
  rw delayn_zero, assumption },
{ specialize (ih_1 k H H'),
  have ak := nat.lt_of_succ_lt H_1,
  specialize (ih_1 ak),
  specialize (H' _ H_1),
  apply HS, assumption, 
  apply next_delay, assumption }
end

end temporal