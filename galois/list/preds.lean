/- Useful predicates and lemmas for quantifying over lists -/

namespace list

inductive Exists {a : Type} (P : a -> Prop) : list a -> Prop
| Exists_this : ∀ h t, P h -> Exists (h :: t)
| Exists_rest : ∀ h t, Exists t -> Exists (h::t)

inductive Forall {a : Type} (P : a -> Prop) : list a -> Prop
| Forall_this : ∀ h t, P h -> Forall t -> Forall (h :: t)


def In {a:Type} (i:a) := Exists (eq i)

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
            { cases a_2}
        },
        {
            cases a_2,
            {
                subst i,
                left, refl
            },
            {
                simp [In] at ih_1,
                note iha := ih_1 _ a_3,
                clear ih_1, clear a_3,
                cases iha,
                {
                    right, subst i, apply Exists.Exists_this, refl
                },
                {
                    right, apply Exists.Exists_rest, assumption
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
                subst i, apply Exists.Exists_this, refl
            },
            {
                cases a_1
            }
        },
        {
            cases a_2,
            {
                subst i, 
                apply Exists.Exists_this, refl
            },
            {
                apply Exists.Exists_rest,
                apply a_3
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
            subst i, left, apply Exists.Exists_this, refl,
        },
        {
            note iha := ih_1 a_2,
            cases iha,
            { 
                left,
                apply Exists.Exists_rest,
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
        cases a_1,
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
apply Exists.Exists_this, refl
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
        { cases a_3},
        right, apply ih_1, assumption
    }
}
end

end list