-- Kuratowski-finite powerset
import .preds
       galois.tactic

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

lemma incl_elements_refl (xs : list A) : incl_elements xs xs
:= begin
intros x H, apply H
end

lemma incl_elements_trans {xs ys zs : list A}
  (H : incl_elements xs ys) (H' : incl_elements ys zs)
  : incl_elements xs zs
:= begin
intros x H'', apply H', apply H, assumption,
end

lemma incl_elements_app {xs ys xs' ys' : list A}
  (H : incl_elements xs xs') (H' : incl_elements ys ys')
  : incl_elements (xs ++ ys) (xs' ++ ys')
:= begin
intros z X, rw list.mem_append, rw list.mem_append at X,
induction X with X X,
left, apply H, assumption,
right, apply H', assumption
end

lemma same_elements_app_comm {xs ys : list A}
  : same_elements (xs ++ ys) (ys ++ xs)
:= begin
intros z, repeat {rw list.mem_append},
rw or_comm,
end

lemma same_elements_refl (xs : list A) : same_elements xs xs
:= begin
dsimp [same_elements], intros, trivial,
end

lemma same_elements_trans {xs ys zs : list A}
  (H : same_elements xs ys) (H' : same_elements ys zs)
  : same_elements xs zs
:= begin
dsimp [same_elements],
intros, rw H, rw H',
end

lemma same_elements_symm {xs ys : list A}
  (H : same_elements xs ys)
  : same_elements ys xs
:= begin
dsimp [same_elements] at *,
intros, rw H,
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

lemma same_elements_app {xs ys xs' ys' : list A}
  (H : same_elements xs xs') (H' : same_elements ys ys')
  : same_elements (xs ++ ys) (xs' ++ ys')
:= begin
apply incl_same,
apply incl_elements_app; apply same_incl1; assumption,
apply incl_elements_app; apply same_incl2; assumption,
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

lemma same_elements_fpow {A} {xs ys : list A}
  : same_elements xs ys ↔ fpow.from_list xs = fpow.from_list ys
:= begin
split; intros H,
apply quot.sound, assumption,
have H' := quot.exact _ H,
clear H,
induction H', assumption,
apply same_elements_refl,
apply same_elements_symm; assumption,
apply same_elements_trans; assumption,
end