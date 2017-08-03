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
{ simp [concat], 
  have Hxs' := Forall_invert Hxs,
  clear Hxs,
  dsimp at Hxs',
  cases Hxs',
  constructor, assumption,
  apply ih_1, assumption }
end

def In {a:Type u} (i:a) := Exists (eq i)

@[simp]
lemma In_or_cons_iff : forall T (i : T) h t,
In i (h:: t) <-> i = h ∨ In i t :=
begin
    intros; split; intros,
    {
        revert h,
        induction t; intros,
        {
            cases a,
            { subst i, left, refl },
            { cases a_1}
        },
        {
            cases a_2,
            {
                subst i,
                left, refl
            },
            {
                simp [In] at ih_1,
                have iha := ih_1 _ a_3,
                clear ih_1, clear a_3,
                cases iha,
                {
                    right, subst i, apply Exists.here, refl
                },
                {
                    right, apply Exists.there, assumption
                }

            }
        }

    },
    {
        revert h,
        induction t; intros,
        {
            cases a,
            {
                subst i, apply Exists.here, refl
            },
            {
                cases a
            }
        },
        {
            cases a_2,
            {
                subst i, 
                apply Exists.here, refl
            },
            {
                apply Exists.there,
                apply a_2
            }
        }
    }
end

@[simp]
lemma In_or_app_iff : forall {T} (i : T) l1 l2,
In i (l1 ++ l2) <-> In i l1 ∨ In i l2 :=
begin
intros; split; intros,
{
    induction l1,
    {
        simp at a, right, assumption
    },
    {
        simp at a, 
        cases a,
        {
            subst i, left, apply Exists.here, refl,
        },
        {
            have iha := ih_1 a_2,
            cases iha,
            { 
                left,
                apply Exists.there,
                apply a_3,
            } ,
            {
                right, assumption
            }
        }
    }
},
{
    induction l1; simp,
    {
        cases a,
        cases a,
        assumption,
    },
    {
        cases a,
        {
            simp at a_2,
            cases a_2,
            {
                subst i,
                left, refl
            },
            {
                right,
                apply ih_1,
                left, assumption
            }
        },
        {
            right,
            apply ih_1, right, assumption,
        }
    }
}
end

@[simp]
lemma In_self : forall {T} (i : T), In i [i] <-> true := 
begin
intros,
split;intros,
trivial,
apply Exists.here, refl
end

lemma In_reverse_In : forall {T} (i :T) l, 
In i l <-> In i (list.reverse l) :=
begin
intros;
split;
intros; induction l,
{   cases a, },
{
    cases a,
    { subst i,
        simp,
    },
    {
        simp, right, right, apply ih_1, assumption,
    }
},
{
    cases a,
},
{
    simp at a,
    simp,
    cases a,
    {
        left, assumption
    },
    {
        cases a_2,
        { cases a_2},
        right, apply ih_1, assumption
    }
}
end

instance Exists_decidable {A} (P : A -> Prop)
  [decidable_pred P] : decidable_pred (list.Exists P)
:=
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

instance In_decidable {A} [decidable_eq A]
  (x : A)
  : decidable_pred (list.In x)
:= begin
unfold list.In,
apply list.Exists_decidable
end

end list