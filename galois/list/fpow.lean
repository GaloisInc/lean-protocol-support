-- Kuratowski-finite powerset
import .preds

universes u

section
parameter {A : Type u}
def incl_elements (xs ys : list A) : Prop :=
  ∀ x : A, x ∈ xs → x ∈ ys

def same_elements (xs ys : list A) : Prop :=
  ∀ x : A, x ∈ xs ↔ x ∈ ys

def incl_same {xs ys : list A}
  (H : incl_elements xs ys) (H' : incl_elements ys xs)
  : same_elements xs ys
:= begin
intros z, split, apply H, apply H'
end

def same_incl1 {xs ys : list A}
  (H : same_elements xs ys)
  : incl_elements xs ys
:= begin
intros z,
destruct (H z), intros, apply mp, assumption
end

def same_incl2 {xs ys : list A}
  (H : same_elements xs ys)
  : incl_elements ys xs
:= begin
intros z,
destruct (H z), intros, apply mpr, assumption
end

def same_incl  {xs ys : list A}
  (H : same_elements xs ys)
  : incl_elements xs ys ∧ incl_elements ys xs
:= begin
split, apply (same_incl1 H), apply (same_incl2 H)
end

def cons_mono {x y : A} {xs ys : list A}
  (Hhd : x = y)
  (Htl : incl_elements xs ys)
  : incl_elements (x :: xs) (y :: ys)
:= begin
induction Hhd,
intros z Hz, simp [has_mem.mem, list.mem] at Hz,
induction Hz, induction a, simp [has_mem.mem, list.mem],
simp [has_mem.mem, list.mem],
right, apply Htl, assumption
end

def cons_same {x y : A} {xs ys : list A}
  (Hhd : x = y)
  (Htl : same_elements xs ys)
  : same_elements (x :: xs) (y :: ys)
:= begin
have Htl' := same_incl Htl, clear Htl,
induction Htl' with Htl1 Htl2,
apply incl_same; apply cons_mono, assumption,
apply Htl1, symmetry, assumption, apply Htl2,
end

end

def fpow (A : Type u) := quot (@same_elements A)

namespace fpow
section
parameter {A : Type u}

def from_list : list A → fpow A := quot.mk _

def nil : fpow A := quot.mk _ []

def cons (x : A) (xs : fpow A) : fpow A :=
begin
fapply (quot.lift_on xs); clear xs,
exact (λ xs, quot.mk _ (x :: xs)),
intros xs ys Heq, apply quot.sound,
unfold same_elements,
intros z, apply cons_same, reflexivity, assumption
end

instance mem  : has_mem A (fpow A) :=
begin
constructor, intros x xs,
fapply (quot.lift_on xs); clear xs,
exact (λ xs, x ∈ xs),
intros xs ys H, apply propext, apply H
end

end

end fpow