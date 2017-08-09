import .temporal
       .first
import galois.subset.fixpoint

open subset

namespace temporal 

universes u v

def always_fixpoint {T : Type u} (P : tProp T) (X : tProp T) := P ∩ ◯ X

def until_fixpoint {T : Type u} (P Q : tProp T) (X : tProp T) := 
  Q ∪ (P ∩ ◯ X)

lemma always_fixpoint_mono {T : Type u} (P : tProp T) : 
  monotone (always_fixpoint P)
:= begin
unfold monotone, intros X Y H,
unfold always_fixpoint, apply bintersection_mono,
apply included_refl, apply next_mono, assumption
end

lemma nextn_continuous {T : Type u} (n : ℕ)
  : continuous (@nextn T n)
:= begin
unfold continuous, intros Ix inh f,
apply included_eq,
{ intros x H, intros ix,
  dsimp [function.comp], apply H, },
{ intros x H,
  unfold nextn, intros ix, apply H, }
end

lemma next_continuous {T : Type u}
  : continuous (@next T) := nextn_continuous 1

lemma always_fixpoint_continuous {T : Type u} (P : tProp T)
  : continuous (always_fixpoint P)
:= begin
unfold continuous, intros Ix inh f,
unfold always_fixpoint,
rw next_continuous,
unfold has_inter.inter, rw and_continuous_r,
reflexivity,
end

lemma until_fixpoint_mono {T : Type u} (P Q : tProp T) : 
  monotone (until_fixpoint P Q)
:= begin
unfold monotone, intros X Y H,
unfold until_fixpoint, apply bunion_mono,
apply included_refl, apply bintersection_mono,
apply included_refl, apply next_mono, assumption
end

lemma until_fixpoint_continuous {T : Type u} (P Q : tProp T)
  [decidable_pred Q]
  : continuous (until_fixpoint P Q)
:= begin
unfold continuous, intros Ix inh f,
unfold until_fixpoint,
rw next_continuous,
unfold has_inter.inter, rw and_continuous_r,
unfold has_union.union,
rw or_continuous_r,
reflexivity,
end

def weak_until {T : Type u} (P Q : tProp T) : tProp T :=
  greatest_fixpointn (until_fixpoint P Q)

-- \MCW
infix `𝓦` : 50 := weak_until

@[ltl]
def release {T : Type u} (P Q : tProp T) : tProp T :=
  Q 𝓦 (Q ∩ P)

-- \MCR
infix `𝓡` : 50 := release

lemma always_fixpoint_fixes {T : Type u} (P : tProp T)
  : always_fixpoint P (□ P) = □ P
:= begin
unfold always_fixpoint, symmetry, apply always_and_next
end

lemma always_greatest_fixpoint {T : Type u} (P : tProp T) 
  : □ P = greatest_fixpoint (always_fixpoint P)
:= begin
apply included_eq,
{ intros x H, apply (union_st.mk (□ P)),
  unfold always_fixpoint,
  rw ← always_and_next, apply (included_refl _),
  assumption },
{ apply (greatest_fixpoint_le _ _), 
  apply always_fixpoint_mono,
  intros x H,
  unfold always_fixpoint at H,
  intros tr xtr,
  have Hx : □ x tr,
  { apply temporal_induction, assumption,
    intros n IH, rw H at IH, induction IH with H1 H2,
    assumption
  },
  { rw H at Hx,
  rw ← always_and at Hx,
  induction Hx with H1 H2, assumption,
  }
}
end

lemma always_greatest_fixpointn {T : Type u} (P : tProp T)
  : □ P = greatest_fixpointn (always_fixpoint P)
:= begin
rw always_greatest_fixpoint, symmetry,
apply greatest_fixpointn_same,
apply continuous_chain_cocont, apply always_fixpoint_continuous,
end

lemma curry {T : Type u} {P Q R : tProp T}
  (H : ⊩ P ∩ Q => R)
  : ⊩ P => Q => R
:= begin
intros tr HP HQ, apply H, constructor; assumption
end

lemma weak_until_not_always_lemma 
  {T : Type u} (P Q : tProp T) (n : ℕ)
  : ⊩ □ (tNot Q)
    => iterate (until_fixpoint P Q) tt n
    => iterate (always_fixpoint P) tt n
:= begin
induction n; intros tr notQ H; simp [iterate],
simp [iterate] at H,
unfold until_fixpoint at H,
unfold always_fixpoint,
induction H with H H,
specialize (notQ 0),
rw delayn_zero at notQ, contradiction,
induction H with Hl Hr,
constructor, assumption,
unfold next nextn, apply ih_1,
intros n, rw delayn_combine, apply notQ,
apply next_delay, rw delayn_zero, assumption
end

lemma weak_until_not_always {T : Type u} (P Q : tProp T)
  : ⊩ P 𝓦 Q => □ (tNot Q) => □ P
:= begin
intros tr PWQ notQ,
rw always_greatest_fixpointn,
intros n, apply weak_until_not_always_lemma, assumption,
apply PWQ,
end

lemma weak_until_always_mono {T : Type u} (A B P : tProp T)
  : ⊩ □ (A => B) => A 𝓦 P => B 𝓦 P
:= begin
intros tr H AWP n,
specialize (AWP n), revert tr,
induction n; simp [iterate]; intros tr AB H,
assumption,
unfold until_fixpoint, unfold until_fixpoint at H,
induction H with H H, apply or.inl, assumption,
apply or.inr, induction H with Hl Hr,
constructor, rw ← (delayn_zero tr), apply AB,
rw delayn_zero, assumption,
unfold next nextn, apply ih_1,
intros n, rw delayn_combine, apply AB,
apply Hr
end

lemma weak_until_mono {T : Type u} {A B P : tProp T}
  (AB : A ≤ B)
  : (A 𝓦 P) ≤ (B 𝓦 P)
:= begin
intros tr AP,  apply weak_until_always_mono, 
intros n, apply AB, assumption
end

lemma not_weakuntil_yes {T : Type u}
  (P : tProp T) [decP : decidable_pred P]
  : ⊩ tNot P 𝓦 P
:= begin
intros tr n, revert tr, induction n; simp [iterate]; intros tr,
trivial,
have H := decP tr, induction H with H H,
{ apply or.inr,
  constructor, apply H,
  apply ih_1 },
{ apply or.inl, assumption }
end

lemma always_weak_until {T : Type u} (P Q : tProp T) [decidable_pred Q] :
  ⊩ □ (P ∪ Q) => P 𝓦 Q
:= begin
rw always_greatest_fixpointn,
apply greatest_fixpointn_mono,
apply chain_cocont_mono,
apply continuous_chain_cocont,
apply always_fixpoint_continuous,
unfold always_fixpoint until_fixpoint,
intros X tr H, induction H with Hl Hr,
induction Hl with Hl Hl,
{ apply or.inr, 
  constructor; assumption },
{ apply or.inl, assumption }
end

/-- An anologue of `temporal_induction`. If we can prove
    `P` holds now, and if, assuming `Q` doesn't hold,
    `P` implies `◯ P`, then `◯ P` holds weak-until `Q`.
-/
lemma weak_until_induction {T : Type u} (P Q : tProp T)
  [decQ : decidable_pred Q]
  : ⊩ (P => □ (tNot Q => P => (◯ P)) => ◯ P 𝓦 Q) :=
begin
intros tr H0 HS n,
revert tr, induction n; simp [iterate]; intros tr H0 HS,
trivial,
unfold until_fixpoint,
have H := decQ tr, induction H with HQ HQ,
{ apply or.inr, constructor, specialize (HS 0),
  rw delayn_zero at HS, specialize (HS HQ H0), assumption,
  unfold next nextn, apply ih_1,
  specialize (HS 0 HQ H0), assumption,
  intros n, rw delayn_combine, apply HS },
{ apply or.inl, assumption }
end


lemma eventually_strengthen_until {T : Type u}
  (P Q : tProp T)
  [decidable_pred Q]
  : ⊩ ◇ Q => (P 𝓦 Q) => (P 𝓤 Q)
:= begin
intros tr evQ PWQ,
have H := eventually_first_dec _ _ evQ,
clear evQ,
unfold first at H,
induction H with k Hk, induction Hk with Hkl Hkr,
constructor, split, assumption,
admit
end

lemma fair_strengthen_until {T : Type u}
  (P Q : tProp T) [decidable_pred Q] :
  ⊩ □ (P 𝓦 Q)
  => □ (◇ Q)
  => □ (P 𝓤 Q)
:= begin
intros tr PQ fairQ  n,
apply eventually_strengthen_until; apply PQ <|> apply fairQ,
end


lemma weak_until_implies_release {T : Type u} {P Q : tProp T}
  : ⊩ P => (◯ P 𝓦 Q) => Q 𝓡 P
:= begin
intros tr HP HPimpQ n,
specialize (HPimpQ n), revert tr,
induction n; simp [iterate]; intros tr H0 HS,
trivial,
unfold until_fixpoint, unfold until_fixpoint at HS,
induction HS with HS HS,
{ apply or.inl, constructor; assumption },
{ apply or.inr, induction HS with HSl HSr,
  constructor, assumption,
  unfold next nextn, apply ih_1, assumption,
  apply HSr }
end

end temporal