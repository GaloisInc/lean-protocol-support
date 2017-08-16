import galois.tactic
       galois.list.preds

universes u v
/-- Defines a subset of a type -/
def subset (A : Sort u) := A → Prop

namespace subset
section
parameter {A : Type u}
/-- A subset that is the same for all members of the type -/
def const (P : Prop) : subset A := λ _, P

/-- The subset with all memebers -/
def tt : subset A := const true

/-- The empty subset -/
def ff : subset A := const false

/-- Subset P is included in subset Q if all members of P are also in Q -/
def included (P Q : subset A) := ∀ x : A, P x → Q x

/-- The intersection of two subsets contains all shared members -/
def bintersection (P Q : subset A) := λ x, P x ∧ Q x

/-- The union of two subsets contains all members of both-/
def bunion (P Q : subset A) := λ x, P x ∨ Q x

/-- Lifting of prop implication --/
def tImp {T : Type u} (P Q : subset T) : subset T :=
  λ x, P x → Q x

infixr `=>` : 50 := tImp


instance : has_union (subset A)
  := ⟨ bunion ⟩

instance subset_has_inter : has_inter (subset A)
  := ⟨ bintersection ⟩

instance subset_has_le : has_le (subset A):= ⟨ included ⟩

/-- If two subsets include eachother they are the same -/
lemma included_eq {P Q : subset A}
  (PQ : P ≤ Q) (QP : Q ≤ P) : P = Q
:= begin
apply funext, intros x, apply propext, split,
apply PQ, apply QP
end

/-- Every set includes itself -/
lemma included_refl (P : subset A)
  : P ≤ P := λ _ H, H

/-- Transitivity of inclusion -/
lemma included_trans {P Q R : subset A}
  (PQ : P ≤ Q) (QR : Q ≤ R)
  : P ≤ R :=
begin
intros x HP, apply QR, apply PQ, assumption
end

/-- Intersection is monotonic, it grows as either of its arguments grows -/
lemma bintersection_mono {P P' Q Q' : subset A} 
  (HP : P ≤ P') (HQ : Q ≤ Q')
  : P ∩ Q ≤ P' ∩ Q'
:= begin
intros x H, induction H with Hl Hr,
constructor, apply HP,  assumption,
apply HQ, assumption
end

/-- Union is monotonic, it grows as either of its arguments grows -/
lemma bunion_mono {P P' Q Q' : subset A} 
  (HP : P ≤ P') (HQ : Q ≤ Q')
  : P ∪ Q ≤ P' ∪ Q'
:= begin
intros x H, induction H with Hl Hr,
{ apply or.inl, apply HP, assumption },
{ apply or.inr, apply HQ, assumption }
end

/--  Intersection such that: The intersection of all subsets defined by F -/
def intersection_st (F : subset A → Prop)
  : subset A
  := λ x, ∀ P, F P → P x

/-- Union such that: The union of all subsets defined by F -/
inductive union_st (F : subset A → Prop)
  (x : A) : Prop
| mk : ∀ P, F P → P x → union_st

def union_st' (F : subset A → Prop) : subset A := union_st F

/-- union_st distributes over and -/
lemma union_st_bintersection {F G : subset A → Prop}
  : union_st' (λ x, F x ∧ G x) ≤ union_st' F ∩ union_st' G
:= begin
intros x H,
induction H with P FGP Px,
induction FGP with FP GP,
constructor; constructor; assumption
end
/-- union st is monotone -/
lemma union_st_mono {F G : subset (subset A)}
  (H : F ≤ G)
  : union_st' F ≤ union_st' G
:= begin
intros x H,
induction H with P FP Px,
constructor, apply H, assumption, assumption
end

/-- Every set is contained in tt -/
lemma tt_top (P : subset A) : P ≤ tt :=
begin intros x H, constructor end

/-- false is contained in every set -/
lemma ff_bot (P : subset A) : ff ≤ P :=
begin intros x H, exfalso, apply H, end

definition from_list' (l : list A) : subset A := 
fun x :A, x ∈ l 

/-- Create a subset of items contained in a list -/
inductive from_list : list A → subset A
| here : ∀ {x xs}, (from_list (x :: xs)) x
| there : ∀ {x y xs}, from_list xs y → from_list (x :: xs) y

/-- Union of an indexed set such that : If we have a set of indexes
    defined by P, and a mapping from those indexes to subsets defined
    by F, this function gives the union of the range of F over P -/
inductive union_ix_st {Ix : Type v} (P : Ix → Prop) (F : Ix → subset A) (x : A) : Prop
| mk : ∀ ix, P ix → F ix x → union_ix_st

/-- Intersection of an indexed set: If we have an indexed collection of
    subsets, this is the intersection over the entire range of those subsets -/
def intersection_ix {Ix : Type v} (F : Ix → subset A) : subset A
  := λ x, ∀ ix : Ix, F ix x

/-- Intersection of an indexed set: If we have an indexed collection of
    subsets, this is the union over the entire range of those subsets -/
def union_ix {Ix : Type v} (F : Ix → subset A) : subset A :=
  union_ix_st (λ _, true) F

/-- If we increase the domain of the indexes, the union of the range increases as well -/
lemma union_ix_st_mono {Ix : Type v} {P Q : subset Ix} {F G : Ix → subset A}
  (H1 : P ≤ Q)
  (H : ∀ ix : Ix, F ix ≤ G ix)
  : @has_le.le _ subset_has_le (union_ix_st P F) (union_ix_st Q G)
:= begin
intros x H,
induction H with P _ FP Px,
constructor, apply H1, assumption, apply H, assumption,
end

/-- If we increase the range of the indexed sets, union ix
    of those index sets increases -/
lemma union_ix_mono {Ix : Type v} {F G : Ix → subset A}
  (H : ∀ ix : Ix, F ix ≤ G ix)
  : union_ix F ≤ union_ix G
:= begin
apply union_ix_st_mono, intros x H', apply H',
assumption
end

lemma intersection_ix_mono {Ix : Type v} {F G : Ix → subset A}
  (H : ∀ ix : Ix, F ix ≤ G ix)
  : intersection_ix F ≤ intersection_ix G
:= begin
intros x H' ix, apply H, apply H'
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

lemma and_distr_l (P Q R : subset A)
 : (P ∩ Q) ∪ (P ∩ R) = P ∩ (Q ∪ R)
:= begin
apply included_eq; intros x Hx,
induction Hx with H H, induction H with H H',
constructor, assumption, apply or.inl, assumption,
induction H with H H', constructor, assumption,
apply or.inr, assumption,
induction Hx with H H', induction H' with H' H',
apply or.inl, constructor; assumption,
apply or.inr, constructor; assumption
end

lemma inter_comm (P Q : subset A) : P ∩ Q = Q ∩ P
:= begin 
apply funext, intros x, simp [has_inter.inter],
unfold bintersection, rw and_comm,
end

end

/-- Definition of monotone for unary functions over subsets -/
def monotone {A : Type u} {B : Type v} (F : subset A → subset B) :=
  ∀ P Q, P ≤ Q → F P ≤ F Q

end subset
