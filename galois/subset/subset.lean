import galois.tactic
       galois.list.preds

universes u v
def subset (A : Type u) := A → Prop

namespace subset
section
parameter {A : Type u}
def const (P : Prop) : subset A := λ _, P
def tt : subset A := const true
def ff : subset A := const false

def included (P Q : subset A) := ∀ x : A, P x → Q x

def bintersection (P Q : subset A) := λ x, P x ∧ Q x
def bunion (P Q : subset A) := λ x, P x ∨ Q x

instance : has_union (subset A)
  := ⟨ bunion ⟩

instance subset_has_inter : has_inter (subset A)
  := ⟨ bintersection ⟩

instance subset_has_le : has_le (subset A):= ⟨ included ⟩

lemma included_eq {P Q : subset A}
  (PQ : P ≤ Q) (QP : Q ≤ P) : P = Q
:= begin
apply funext, intros x, apply propext, split,
apply PQ, apply QP
end

lemma included_refl (P : subset A)
  : P ≤ P := λ _ H, H

lemma included_trans {P Q R : subset A}
  (PQ : P ≤ Q) (QR : Q ≤ R)
  : P ≤ R :=
begin
intros x HP, apply QR, apply PQ, assumption
end

lemma bintersection_mono {P P' Q Q' : subset A} 
  (HP : P ≤ P') (HQ : Q ≤ Q')
  : P ∩ Q ≤ P' ∩ Q'
:= begin
intros x H, induction H with Hl Hr,
constructor, apply HP,  assumption,
apply HQ, assumption
end

lemma bunion_mono {P P' Q Q' : subset A} 
  (HP : P ≤ P') (HQ : Q ≤ Q')
  : P ∪ Q ≤ P' ∪ Q'
:= begin
intros x H, induction H with Hl Hr,
{ apply or.inl, apply HP, assumption },
{ apply or.inr, apply HQ, assumption }
end

def intersection_st (F : subset A → Prop)
  : subset A
  := λ x, ∀ P, F P → P x

inductive union_st (F : subset A → Prop)
  (x : A) : Prop
| mk : ∀ P, F P → P x → union_st

def union_st' (F : subset A → Prop) : subset A := union_st F

lemma union_st_bintersection {F G : subset A → Prop}
  : union_st' (λ x, F x ∧ G x) ≤ union_st' F ∩ union_st' G
:= begin
intros x H,
induction H with P FGP Px,
induction FGP with FP GP,
constructor; constructor; assumption
end

lemma union_st_mono {F G : subset (subset A)}
  (H : F ≤ G)
  : union_st' F ≤ union_st' G
:= begin
intros x H,
induction H with P FP Px,
constructor, apply H, assumption, assumption
end

def monotone (F : subset A → subset A) :=
  ∀ P Q, P ≤ Q → F P ≤ F Q

lemma tt_top (P : subset A) : P ≤ tt :=
begin intros x H, constructor end

lemma ff_bot (P : subset A) : ff ≤ P :=
begin intros x H, exfalso, apply H, end

inductive from_list : list A → subset A
| here : ∀ {x xs}, (from_list (x :: xs)) x
| there : ∀ {x y xs}, from_list xs y → from_list (x :: xs) y

inductive union_ix_st {Ix : Type v} (P : Ix → Prop) (F : Ix → subset A) (x : A) : Prop
| mk : ∀ ix, P ix → F ix x → union_ix_st

def intersection_ix {Ix : Type v} (F : Ix → subset A) : subset A
  := λ x, ∀ ix : Ix, F ix x

def union_ix {Ix : Type v} (F : Ix → subset A) : subset A :=
  union_ix_st (λ _, true) F

lemma union_ix_st_mono {Ix : Type v} {P Q : subset Ix} {F G : Ix → subset A}
  (H1 : P ≤ Q)
  (H : ∀ ix : Ix, F ix ≤ G ix)
  : @has_le.le _ subset_has_le (union_ix_st P F) (union_ix_st Q G)
:= begin
intros x H,
induction H with P _ FP Px,
constructor, apply H1, assumption, apply H, assumption,
end

lemma union_ix_mono {Ix : Type v} {F G : Ix → subset A}
  (H : ∀ ix : Ix, F ix ≤ G ix)
  : union_ix F ≤ union_ix G
:= begin
apply union_ix_st_mono, intros x H', apply H',
assumption
end


lemma imp_or (P Q : subset A)
  : (P ≤ Q) = (P ∪ Q = Q)
:= begin
apply propext, split; intros H,
{ apply included_eq, intros x H',
  induction H' with H' H', apply H, assumption, assumption,
  intros x Qx, apply or.inr, assumption },
{ rw ← H, intros x Px, apply or.inl, assumption }
end

lemma imp_and (P Q : subset A)
  : (P ≤ Q) = (P = P ∩ Q)
:= begin
apply propext, split; intros H,
{ apply included_eq, intros x Px,
  constructor, assumption, apply H, assumption,
  intros x PQx, induction PQx with H1 H2,
  assumption },
{ rw H, intros x PQx, induction PQx with H1 H2,
  assumption }
end

end

end subset