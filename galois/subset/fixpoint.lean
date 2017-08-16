import .subset

universes u v

namespace subset

section
parameters {A : Type u} {B : Type v} (F : subset A → subset B)
def cocontinuous :=
  ∀ (Ix : Type) (f : Ix → subset A), 
    F (union_ix f) = union_ix (F ∘ f)

def cocontinuous_inh :=
  ∀ (Ix : Type) [inhabited Ix] (f : Ix → subset A), 
    F (union_ix f) = union_ix (F ∘ f)

def continuous :=
  ∀ (Ix : Type) (f : Ix → subset A), 
    F (intersection_ix f) = intersection_ix (F ∘ f)

def continuous_inh :=
  ∀ (Ix : Type) [inhabited Ix] (f : Ix → subset A), 
    F (intersection_ix f) = intersection_ix (F ∘ f)

end

section
parameter {A : Type u}

/-- Given a function over subsets, the greatest fixpoint
    for that function is the union of all sets that might
    be produced by applying the fixpoint-/
def greatest_fixpoint (F : subset A → subset A) : subset A
  := union_st (λ P, P ≤ F P)

/-- Given a function over subsets, the greatest fixpoint
    for that function is the intersection of all sets that might
    be produced by applying the fixpoint-/
def least_fixpoint (F : subset A → subset A) : subset A
:= intersection_st (λ P, F P ≤ P)

section
parameters (F : subset A → subset A) (Fmono : monotone F)
include Fmono

/-- Applying F to a greatest fixpoint of F results in
    a set that includes the greatest fixpoint 
    this should likely be an internal only lemma -/
lemma greatest_fixpoint_postfixed 
  : greatest_fixpoint F ≤ F (greatest_fixpoint F)
:= begin
intros tr H, induction H, apply Fmono, tactic.swap,
apply a, assumption, clear a_1 tr,
intros x H, constructor; assumption,
end

/-- Applying F to a greatest fixpoint of F results in
    the same set --/
lemma greatest_fixpoint_fixed 
  : greatest_fixpoint F = F (greatest_fixpoint F)
:= begin
apply included_eq,
{ apply greatest_fixpoint_postfixed, assumption },
{ intros x H, constructor, apply Fmono,
  apply greatest_fixpoint_postfixed, assumption,
  assumption
}
end

/-- Applying a function to the fixpoint is no smaller than the fixpoint -/
lemma least_fixpoint_prefixed 
  : F (least_fixpoint F) ≤ least_fixpoint F
:= begin
unfold least_fixpoint intersection_st, 
intros x H P HP, apply HP, revert x H,
apply Fmono, intros x H, apply H, dsimp, assumption
end

/-- Applying a function to the fixpoint does not change the set -/
lemma least_fixpoint_fixed
  : F (least_fixpoint F) = least_fixpoint F
:= begin
apply included_eq, 
{ apply least_fixpoint_prefixed, assumption },
{ intros x H,
  apply H, dsimp, apply Fmono,
  apply least_fixpoint_prefixed, assumption,
}
end

end

lemma greatest_fixpoint_and_le (F G : subset A → subset A)
  : greatest_fixpoint (λ X, F X ∩ G X)
  ≤ greatest_fixpoint F ∩ greatest_fixpoint G
:= begin
unfold greatest_fixpoint,
apply included_trans,
tactic.swap,
apply union_st_bintersection,
apply union_st_mono, intros x H,
constructor; intros z Hz; 
specialize (H z Hz); induction H with H1 H2; assumption
end

/-- A function F from subset to subset is finitary if
    an arbitrary application can be described as the union of some number of applications to finite arguments -/
def finitary (F : subset A → subset A) : Prop :=
  ∀ x, F x = union_ix_st (λ xs : list A, from_list xs ≤ x) (λ xs, F (from_list xs))

/-- Finitary functions are monotone -/
lemma finitary_monotone (F : subset A → subset A)
  (Ffin : finitary F) : monotone F :=
begin
intros P Q PQ,
repeat { rw Ffin },
intros x H,
induction H,
constructor, apply included_trans; assumption,
assumption,
end


def chain_cont (F : subset A → subset A) :=
  ∀ (f : ℕ → subset A),
  (∀ x y : ℕ, x ≤ y → f x ≤ f y)
  → F (union_ix f) = union_ix (F ∘ f)

def chain_cocont (F : subset A → subset A) :=
  ∀ (f : ℕ → subset A),
  (∀ x y : ℕ, x ≤ y → f y ≤ f x)
  → F (intersection_ix f) = intersection_ix (F ∘ f)

protected def simple_chain (P Q : subset A) : ℕ → subset A
| 0 := P
| (nat.succ n) := Q

private lemma simple_chain_mono 
  {P Q : subset A}  (PQ : P ≤ Q) (x y : ℕ)
  (H : x ≤ y) : simple_chain P Q x ≤ simple_chain P Q y
:= begin
induction H, apply included_refl,
apply included_trans, assumption,
clear ih_1 a x y,
cases b; simp [subset.simple_chain],
intros x Px, apply PQ, assumption,
apply included_refl,
end

private lemma simple_chain_anti 
  {P Q : subset A}  (PQ : Q ≤ P) (x y : ℕ)
  (H : x ≤ y) : simple_chain P Q y ≤ simple_chain P Q x
:= begin
induction H, apply included_refl,
apply included_trans, tactic.swap, assumption,
clear ih_1 a x y,
cases b; simp [subset.simple_chain],
intros x Px, apply PQ, assumption,
apply included_refl,
end


lemma chain_cont_union {F : subset A → subset A}
  (H : chain_cont F) {P Q : subset A}
  (PQ : P ≤ Q)
  : F (P ∪ Q) = F P ∪ F Q
:= begin
unfold chain_cont at H,
specialize (H (subset.simple_chain P Q) (simple_chain_mono PQ)),
transitivity (F (union_ix (subset.simple_chain P Q))),
f_equal,
apply included_eq, rw imp_or at PQ, rw PQ,
intros x Qx, apply (union_ix_st.mk 1),
trivial, dsimp [subset.simple_chain], assumption,
intros x Hx, induction Hx with n _ Hn,
cases n; dsimp [subset.simple_chain] at Hn,
apply or.inl, assumption, apply or.inr, assumption,
rw H, clear H, apply included_eq,
intros x Hx, induction Hx with n _ Hn,
cases n; dsimp [function.comp, subset.simple_chain] at Hn,
apply or.inl, assumption, apply or.inr, assumption,
intros x Hx, induction Hx with Hx Hx,
apply (union_ix_st.mk 0), trivial,
dsimp [function.comp, subset.simple_chain], assumption,
apply (union_ix_st.mk 1), trivial,
dsimp [function.comp, subset.simple_chain], assumption,
end

lemma chain_cocont_intersection {F : subset A → subset A}
  (H : chain_cocont F) {P Q : subset A}
  (PQ : P ≤ Q)
  : F (P ∩ Q) = F P ∩ F Q
:= begin
unfold chain_cocont at H,
specialize (H (subset.simple_chain Q P) (simple_chain_anti PQ)),
transitivity (F (intersection_ix (subset.simple_chain Q P))),
-- f_equal -- TODO: FIX, the tactic isn't working here
apply congr_arg,
apply included_eq, 
intros x PQx n, induction PQx with Px Qx,
cases n; dsimp [subset.simple_chain]; assumption,
rw imp_and at PQ, rw ← PQ,
intros x Hx, apply (Hx 1),
rw H, clear H, apply included_eq,
intros x Hx, constructor, apply (Hx 1),
apply (Hx 0),
intros x FPQx, induction FPQx with FPx FQx,
intros n,
cases n; dsimp [function.comp, subset.simple_chain]; assumption,
end

lemma chain_cont_mono {F : subset A → subset A}
  (H : chain_cont F) : monotone F
:= begin
unfold monotone, intros P Q PQ,
rw imp_or, rw ← chain_cont_union,
rw imp_or at PQ, rw PQ, assumption, assumption
end

lemma chain_cocont_mono {F : subset A → subset A}
  (H : chain_cocont F) : monotone F
  := 
begin
unfold monotone, intros P Q PQ,
rw imp_and, rw ← chain_cocont_intersection,
rw imp_and at PQ, rw ← PQ, assumption, assumption
end

/-- Repeatedly apply a function f starting with x. -/
def iterate {A : Type u} (f : A → A) (x : A) : ℕ → A
| 0 := x
| (nat.succ n) := f (iterate n)

/-- The least fixpoint is described by the union of all sets
    indexed by the number of iterations
-/
def least_fixpointn (F : subset A → subset A) : subset A
  := union_ix (iterate F ff)

/-- The greatest fixpoint is described by the intersection of all sets
    indexed by the number of iterations
-/
def greatest_fixpointn (F : subset A → subset A) : subset A
  := intersection_ix (iterate F tt)

lemma least_fixpointn_postfixed
  {F : subset A → subset A}
  (Fmono : monotone F)
  : least_fixpointn F ≤ F (least_fixpointn F)
:= begin
intros x H, induction H with n _ Hn,
cases n; simp [iterate] at Hn, exfalso, apply Hn,
apply Fmono, tactic.swap, assumption,
clear Hn x,
intros x H, constructor, constructor, assumption,
end

lemma greatest_fixpointn_prefixed
  {F : subset A → subset A}
  (Fmono : monotone F)
  : F (greatest_fixpointn F) ≤ greatest_fixpointn F
:= begin
intros x H n,
cases n; simp [iterate], apply Fmono,
tactic.swap, assumption, clear H x,
intros x H, apply H,
end


lemma continuous_chain_cocont {F : subset A → subset A}
  (H : continuous_inh F) : chain_cocont F :=
begin
intros f fmono, apply H
end

lemma cocontinuous_chain_cont {F : subset A → subset A}
  (H : cocontinuous F) : chain_cont F :=
begin
intros f fmono, apply H
end

lemma and_continuous_r (P : subset A) 
  : continuous_inh (bintersection P)
:= begin
unfold continuous_inh, intros Ix inh f, apply included_eq,
{ intros x H ix, dsimp [function.comp],
  induction H with Hl Hr, constructor, assumption,
  apply Hr  },
{ intros x H, constructor,
  specialize (H inh.default),
  dsimp [function.comp] at H,
  induction H with Hl Hr, assumption,
  intros ix, specialize (H ix),
  induction H with Hl Hr, assumption, }
end

lemma and_cocontinuous_r (P : subset A) 
  : cocontinuous (bintersection P)
:= begin
unfold cocontinuous, intros Ix f, apply included_eq,
{ intros x H, dsimp [function.comp],
  induction H with Hl Hr, induction Hr, 
  constructor, trivial, constructor; assumption,
},
{ intros x H, induction H, induction a_1, constructor,
  assumption, constructor; assumption
}
end

lemma or_continuous_r (P : subset A)
  [decP : decidable_pred P]
  : continuous (bunion P)
:= begin
unfold continuous, intros Ix f,
apply included_eq,
{ intros x H ix, dsimp [function.comp],
  induction H with H H,
  apply or.inl, assumption,
  apply or.inr, apply H, },
{ intros x Hx,
  have H := decP x, induction H with HP HP,
  { apply or.inr, intros n,
    specialize (Hx n), induction Hx with Hl Hr,
    contradiction, assumption },
  { apply or.inl, assumption }
}
end

lemma or_cocontinuous_r (P : subset A)
  : cocontinuous_inh (bunion P)
:= begin
unfold cocontinuous_inh, intros Ix inh f,
apply included_eq,
{ intros x H, dsimp [function.comp],
  induction H with H H,
  constructor, trivial, apply or.inl,
  assumption, apply inh.default,
  induction H, constructor, trivial,
  apply or.inr, assumption },
{ intros x Hx,
  induction Hx with ix _ H', induction H',
  apply or.inl, assumption,
  apply or.inr, constructor, trivial, assumption,
}
end

lemma iterate_mono_tt_succ {F : subset A → subset A}
  (Fmono : monotone F) (n : ℕ)
  : iterate F tt n.succ ≤ iterate F tt n
:= begin
dsimp [iterate], induction n; dsimp [iterate],
apply tt_top, apply Fmono, assumption,
end

lemma iterate_mono_tt_n {F : subset A → subset A}
  (Fmono : monotone F) (x y : ℕ)
  (H : x ≤ y)
  : iterate F tt y ≤ iterate F tt x
:= begin
induction H, apply included_refl,
simp [iterate], apply included_trans,
apply Fmono, assumption,
apply iterate_mono_tt_succ,
apply Fmono,
end


lemma greatest_fixpointn_fixed 
  {F : subset A → subset A}
  (Fcont : chain_cocont F)
  : F (greatest_fixpointn F) = greatest_fixpointn F
:= begin
apply included_eq, apply greatest_fixpointn_prefixed,
apply chain_cocont_mono,
assumption,
unfold greatest_fixpointn,
rw Fcont, intros x Hx,
intros n, dsimp [function.comp],
specialize (Hx n.succ), apply Hx,
intros, apply iterate_mono_tt_n,
apply chain_cocont_mono, assumption,
assumption
end

lemma le_greatest_fixpoint {P : subset A}
  {F : subset A → subset A}
  (H : P ≤ F P)
  : P ≤ greatest_fixpoint F
:= begin
intros x H', constructor, apply H, assumption
end

lemma least_fixpoint_le {P : subset A}
  {F : subset A → subset A}
  (H : F P ≤ P)
  : least_fixpoint F ≤ P
:= begin
intros x H', apply H', apply H
end

lemma greatest_fixpoint_le {P : subset A}
  {F : subset A → subset A} (Fmono : monotone F)
  (H : ∀ Q, Q = F Q → Q ≤ P)
  : greatest_fixpoint F ≤ P
:= begin
apply (H _ (greatest_fixpoint_fixed F Fmono))
end

lemma le_least_fixpoint {P : subset A}
  {F : subset A → subset A} (Fmono : monotone F)
  (H : ∀ Q, F Q = Q → P ≤ Q)
  : P ≤ least_fixpoint F
:= begin
apply (H _ (least_fixpoint_fixed F Fmono))
end

lemma iterate_mono_ff_succ {F : subset A → subset A}
  (Fmono : monotone F) (n : ℕ)
  : iterate F ff n ≤ iterate F ff n.succ
:= begin
dsimp [iterate], induction n; dsimp [iterate],
apply ff_bot, apply Fmono, assumption,
end

lemma iterate_mono_ff_n {F : subset A → subset A}
  (Fmono : monotone F) (x y : ℕ)
  (H : x ≤ y)
  : iterate F ff x ≤ iterate F ff y
:= begin
induction H, apply included_refl,
simp [iterate], apply included_trans,
apply ih_1,
apply iterate_mono_ff_succ,
apply Fmono, 
end

lemma iterate_mono {F : subset A → subset A}
  (Fmono : monotone F) {P Q : subset A}
  (PQ : P ≤ Q) (n : ℕ)
  : iterate F P n ≤ iterate F Q n
:= begin
induction n; simp [iterate],
{ assumption },
{ apply Fmono, assumption }
end

lemma iterate_mono2 {F G : subset A → subset A}
  {P : subset A}
  (Fmono : monotone F)
  (FG : ∀ x, F x ≤ G x)
  (n : ℕ)
  : iterate F P n ≤ iterate G P n
:= begin
induction n; simp [iterate],
{ apply included_refl },
{ apply included_trans, apply Fmono, assumption, 
  apply FG }
end

lemma least_fixpointn_fixed 
  {F : subset A → subset A}
  (Fcoc : chain_cont F)
  : least_fixpointn F = F (least_fixpointn F)
:= begin
apply included_eq, apply least_fixpointn_postfixed,
apply chain_cont_mono, assumption,
unfold least_fixpointn,
rw Fcoc, intros x Hx,
induction Hx with n _ Hn,
dsimp [function.comp] at Hn,
constructor, assumption,
tactic.swap, exact n.succ,
apply Hn, intros,
apply iterate_mono_ff_n,
apply chain_cont_mono, assumption, assumption
end

/-- The fixpoint defined by greatest_fixpointn is actually a greatest fixpoint-/
lemma greatest_fixpointn_same
  {F : subset A → subset A}
  (Fcoc : chain_cocont F)
  : greatest_fixpointn F = greatest_fixpoint F
:= begin
apply included_eq,
apply le_greatest_fixpoint,
rw (greatest_fixpointn_fixed Fcoc),
apply (included_refl (greatest_fixpointn F)),
apply (greatest_fixpoint_le _ _), 
apply chain_cocont_mono, assumption,
intros Q HQ, intros x Qx,
have HQx : ∀ n, Q = iterate F Q n,
intros n, induction n; simp [iterate],
rw ← ih_1, assumption,
intros n, apply iterate_mono,
apply chain_cocont_mono, assumption,
tactic.swap, rw (HQx n) at Qx,
assumption, apply tt_top
end
/-- The fixpoint defined by least_fixpointn is actually a least fixpoint-/
lemma least_fixpointn_same
  {F : subset A → subset A}
  (Fchain_cont : chain_cont F)
  : least_fixpointn F = least_fixpoint F
:= begin
apply included_eq, tactic.swap,
apply least_fixpoint_le,
rw ← (least_fixpointn_fixed Fchain_cont),
apply included_refl,
apply (le_least_fixpoint _ _),
apply chain_cont_mono, assumption,
intros Q HQ, intros x Qx,
have HQx : ∀ n, Q = iterate F Q n,
intros n, induction n; simp [iterate],
rw ← ih_1, symmetry, assumption,
unfold least_fixpointn at Qx,
induction Qx with n _ Hn,
rw (HQx n), apply iterate_mono,
apply chain_cont_mono, assumption,
tactic.swap, assumption, apply ff_bot,
end


lemma greatest_fixpoint_mono
  {F G : subset A → subset A}
  (H : ∀ P, F P ≤ G P)
  : greatest_fixpoint F ≤ greatest_fixpoint G
:= begin
intros x Hx, induction Hx,
constructor, tactic.swap, apply a_1,
dsimp, apply included_trans, apply a, apply H
end

lemma greatest_fixpointn_mono
  {F G : subset A → subset A}
  (Fmono : monotone F)
  (H : ∀ P, F P ≤ G P)
  : greatest_fixpointn F ≤ greatest_fixpointn G
:= begin
unfold greatest_fixpointn,
intros x H n, specialize (H n),
revert H, apply iterate_mono2,
assumption, assumption
end

lemma and_functional_mono
  {F G : subset A → subset A}
  (Fmono : monotone F) (Gmono : monotone G)
  : monotone (λ X, F X ∩ G X)
:= begin
  unfold monotone, intros P Q PQ, apply bintersection_mono,
  apply Fmono, assumption, apply Gmono, assumption
end

lemma greatest_fixpointn_and_le (F G : subset A → subset A)
  (Fmono : monotone F) (Gmono : monotone G)
  : greatest_fixpointn (λ X, F X ∩ G X)
  ≤ greatest_fixpointn F ∩ greatest_fixpointn G
:= begin
intros x H,
  constructor, 
  { revert H,
  apply greatest_fixpointn_mono, apply and_functional_mono,
  apply Fmono, apply Gmono,
  intros P x H, induction H with Hl Hr, apply Hl,
  },
  { revert H,
  apply greatest_fixpointn_mono, apply and_functional_mono,
  apply Fmono, apply Gmono,
  intros P x H, induction H with Hl Hr, apply Hr,
  }
end

lemma tImp_cocontinuous_l {Ix : Type} 
  (P : Ix → subset A) (Q : subset A)
  : (union_ix P => Q) = intersection_ix (λ ix, P ix => Q)
:= begin 
apply included_eq; intros x Hx,
{ intros n Pn, apply Hx,
  constructor, trivial, assumption },
{ intros H, induction H, apply Hx, assumption }
end


end

end subset