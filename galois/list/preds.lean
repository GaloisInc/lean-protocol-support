/- Useful predicates and lemmas for quantifying over lists -/
universes u v

namespace list

inductive Exists {a : Type u} (P : a -> Prop) : list a -> Prop
| here : ∀ {h t}, P h -> Exists (h :: t)
| there : ∀ {h t}, Exists t -> Exists (h::t)


inductive Forall {A} (P : A -> Prop) : list A -> Prop
| nil : Forall []
| cons : ∀ {x xs}, P x -> Forall xs -> Forall (x :: xs)

lemma map_Forall {A : Type u} {B : Type v} (f : A -> B) (P : B -> Prop)
  (xs : list A)
  (Pxs : Forall (λ x, P (f x)) xs)
  : Forall P (list.map f xs) :=
begin
induction Pxs,
{ constructor },
{ simp [list.map], constructor; assumption
}
end

lemma impl_Forall2 {A : Type u} {P Q R : A → Prop} {xs : list A}
  (Pxs : Forall P xs) (Qxs : Forall Q xs)
  (impl : ∀ x, P x → Q x → R x)
  : Forall R xs
:= begin
induction Pxs; cases Qxs; constructor,
  { apply impl; assumption },
  { apply ih_1, assumption }
end

lemma impl_Forall {A : Type u} {P Q : A -> Prop}
  (xs : list A)
  (Pxs : Forall P xs)
  (impl : forall x, P x -> Q x)
  : Forall Q xs :=
begin
induction Pxs; constructor,
  { apply impl, assumption },
  { assumption }
end

lemma Forall_invert {A : Type u} {P : A -> Prop} {xs : list A}
  (H : list.Forall P xs)
  : (match xs with
  | [] := true
  | (y :: ys) := P y ∧ list.Forall P ys
  end : Prop) :=
begin
induction H; dsimp,
  { constructor },
  { split; assumption }
end

lemma concat_Forall {A : Type u} {P : A -> Prop}
  {xs ys : list A}
  (Hxs : Forall P xs) (Hys : Forall P ys)
  : Forall P (xs ++ ys)
:=
begin
induction xs,
{ dsimp, assumption },
{ simp [append],
  have Hxs' := Forall_invert Hxs,
  clear Hxs,
  dsimp at Hxs',
  cases Hxs',
  constructor, assumption,
  apply ih_1, assumption }
end

instance Exists_decidable {A} (P : A -> Prop)
  [decidable_pred P] : decidable_pred (list.Exists P) :=
begin
simp [decidable_pred],
intros xs,
induction xs,
{ apply decidable.is_false , intros contra,
  cases contra },
{ apply (@decidable.by_cases (list.Exists P a_1)); intros,
  { apply decidable.is_true, apply list.Exists.there, assumption },
  {
  apply (@decidable.by_cases (P a)); intros,
    { apply decidable.is_true, constructor, assumption },
    { apply decidable.is_false, intros contra,
      cases contra; contradiction
    }
  }
}
end

end list
