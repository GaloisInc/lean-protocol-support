/- Useful predicates and lemmas for quantifying over lists -/

import galois.tactic

universes u v

namespace list

inductive Exists {a : Type u} (P : a -> Prop) : list a -> Prop
| here : ∀ {h t}, P h -> Exists (h :: t)
| there : ∀ {h t}, Exists t -> Exists (h::t)

-- Desugar list.Exists into existential.
theorem mem_implies_Exists {α:Type} (P : α → Prop) (l : list α)
  (pr : ∃(v : α), v ∈ l ∧ P v)
: Exists P l :=
begin
  induction l,
  case nil {
    apply exists.elim pr,
    intros v f,
    simp at f,
    contradiction,
  },
  case list.cons h r ind {
    simp at pr,
    apply exists.elim pr,
    intros v v_pr,

    cases v_pr with pv mem,

    cases mem,
    { apply list.Exists.here,
      simp [eq.symm a, pv],
    },
    { apply list.Exists.there,
      apply ind,
      exact exists.intro v (and.intro a pv),
    },
  },
end

theorem exists_map {α β : Type} (P : β → Prop) (f : α → β) (l : list α)
: Exists P (l.map f) ↔ Exists (P ∘ f) l :=
begin
  induction l with h r ind,
  case list.nil {
    apply iff.intro; intro hyp; cases hyp,
  },
  case list.cons h r ind {
    apply iff.intro; intro hyp,
    { cases hyp,
      { apply Exists.here,
        simp [function.comp],
        exact a,
      },
      { apply Exists.there,
        rw [← ind],
        exact a,
      },
    },
    { cases hyp,
      { apply Exists.here,
        simp [function.comp] at a,
        exact a,
      },
      { apply Exists.there,
        rw [← ind] at a,
        exact a,
      },
    },
  },
end

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

lemma Forall_mem_equiv {A : Type u}
  (P : A → Prop) (xs : list A)
  : xs.Forall P ↔ (∀ x, x ∈ xs → P x)
:= begin
split; intros H,
{ induction H,
  intros, rw list.mem_nil_iff at a, contradiction,
  intros, apply_in a_2 list.eq_or_mem_of_mem_cons,
  induction a_2, subst x_1, assumption, apply ih_1,
  assumption,
},
{ induction xs, constructor, constructor,
  apply H, constructor, reflexivity,
  apply ih_1, intros, apply H,
  right, assumption,
}
end

lemma map_Forall_iff {A : Type u} {B : Type v} (f : A -> B) (P : B -> Prop)
  (xs : list A)
  : Forall P (list.map f xs)
  ↔ Forall (λ x, P (f x)) xs :=
begin
split; intros H,
{ induction xs; dsimp [map] at H,
  constructor,
  apply_in H Forall_invert,
  dsimp at H, induction H with Hx Hxs,
  constructor, assumption, apply ih_1, assumption,
 },
{ apply map_Forall, assumption }
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

lemma Forall_app_iff {A : Type u} {P : A → Prop}
  {xs ys : list A}
  : Forall P (xs ++ ys) ↔ Forall P xs ∧ Forall P ys
:= begin
split; intros H,
{ induction xs, split, constructor, assumption,
dsimp [list.append] at H,
apply_in H Forall_invert,
dsimp at H, induction H with Pa H,
specialize (ih_1 H), induction ih_1 with h1 h2,
split, constructor; assumption, assumption },
{ induction H with H H', apply concat_Forall; assumption }
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

instance Forall_decidable {A} (P : A -> Prop)
  [decidable_pred P] : decidable_pred (list.Forall P) :=
begin
intros xs,
induction xs,
{ apply decidable.is_true, constructor },
{ apply (@decidable.by_cases (list.Forall P a_1)); intros,
  {
  apply (@decidable.by_cases (P a)); intros,
    { apply decidable.is_true, constructor; assumption },
    { apply decidable.is_false, intros contra,
      cases contra; contradiction
    }
  },
  { apply decidable.is_false, intros contra, apply a_2,
    cases contra, assumption, }
}
end

end list
