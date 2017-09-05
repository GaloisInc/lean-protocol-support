import .ltl
       galois.temporal.fixpoint

universes u v

open temporal lattice

namespace sequent

lemma eventually_cut {T : Type u} {P Q : tProp T}
  : rlist.nil & ◇ P & □ (P => ◇ Q) ⊢ ◇ Q
:= begin
repeat {sequent.revert},
rw tautology_iff, apply temporal.eventually_cut,
end

lemma now_until_eventually {T : Type u}
  {P Q : tProp T}
  : rlist.nil & P & ((◯ P) 𝓤 Q) ⊢ ◇ (P ∩ Q)
:= begin
repeat {sequent.revert},
rw tautology_iff, apply temporal.now_until_eventually,
end

lemma eventually_strengthen_until {T : Type u}
  {P Q : tProp T}
  [decidable_pred Q]
  : rlist.nil & ◇ Q & (P 𝓦 Q) ⊢ (P 𝓤 Q)
:= begin
repeat {sequent.revert},
rw tautology_iff, apply temporal.eventually_strengthen_until,
end

lemma well_founded_LTL_template (A : Type v) (P Q X : tProp A)
  [decidable_pred Q]
  : rlist.nil
    & ◇ Q
    & P
    & ((◯ P) 𝓦 Q)
    & (□ ((P ∩ Q) => ◇ X))
    ⊢ ◇ X
:= begin
sequent.apply eventually_cut,
tactic.swap, sequent.assumption,
sequent.apply now_until_eventually,
sequent.assumption,
sequent.apply eventually_strengthen_until;
  sequent.assumption,
end

lemma until_always_mono {T : Type u}
  {A B P : tProp T} :
  rlist.nil & (□ (A ⇒ B)) & (A 𝓤 P) ⊢ (B 𝓤 P)
:= begin
repeat { sequent.revert },
rw tautology_iff,
apply until_always_mono,
end

lemma example1 {A B P X : tProp ℕ} :
  rlist.nil & (□ (A ⇒ B)) & X & (A 𝓤 P) ⊢ (B 𝓤 P)
:= begin
sequent.revert, sequent.intros,
sequent.apply until_always_mono;
sequent.assumption,
end

lemma example2 {A B C D : tProp ℕ}
  (H : rlist.nil & A & B & A & C ⊢ D)
  : rlist.nil & A & B & C ⊢ D
:= begin
sequent.apply H; sequent.assumption
end

lemma example3 {P Q R : tProp ℕ} :
  rlist.nil & P & Q ⊢ (R ⊓ P) ⊔ (Q ⊓ P)
:= begin
sequent.right, sequent.split, sequent.assumption,
sequent.assumption,
end

lemma example4 {P Q R : tProp ℕ} :
  rlist.nil & P & Q ⊢ (R ⊓ P) ⊔ (Q ⊓ P)
:= begin
sequent.reify_goal, sequent.entails_tactic formula_entails_auto,
end

end sequent