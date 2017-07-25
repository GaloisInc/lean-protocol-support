import .preds

universes u

namespace list

inductive member {A : Type u} : list A → Type u
| here : ∀ {x : A} {xs : list A}, member (x :: xs)
| there : ∀ {x : A} {xs : list A}, member xs → member (x :: xs)

definition get_member {A : Type u} 
  : ∀ {xs : list A}, member xs -> A
| (x :: xs) member.here := x
| (x :: xs) (member.there m) := get_member m

definition remove_member {A : Type u}
  : ∀ (xs : list A), member xs → list A
| (x :: xs) member.here := xs
| (x :: xs) (member.there m) := x :: remove_member xs m

definition update_member {A : Type u} (y : A)
  : ∀ (xs : list A), member xs → list A
| (x :: xs) member.here := y :: xs
| (x :: xs) (member.there m) := x :: update_member xs m

inductive member_st {A : Type u} (P : A → Prop) : list A → Type u
| here {} : ∀ {x : A} {xs : list A}, P x → member_st (x :: xs)
| there {} : ∀ {x : A} {xs : list A}, member_st xs → member_st (x :: xs)

inductive el_member {A : Type u} : A → list A → Type u
| here : ∀ {x : A} {xs : list A}, el_member x (x :: xs)
| there : ∀ {y x : A} {xs : list A}, el_member y xs → el_member y (x :: xs)

def member_to_el_member {A : Type u}
  : ∀ {xs : list A} (m : member xs), el_member (get_member m) xs
| (x :: xs) member.here := el_member.here
| (x :: xs) (member.there m) := el_member.there (member_to_el_member m)

def member_st_to_member {A : Type u} {P : A → Prop}
  : ∀ {xs : list A}, member_st P xs → member xs
| ._ (@member_st.here ._ ._ x xs H) := member.here
| ._ (@member_st.there ._ ._ _ _ m) := member.there (member_st_to_member m)

def el_member_to_member {A : Type u}
  : ∀ {x : A} {xs : list A}, el_member x xs → member xs
| ._ .(x :: xs) (@el_member.here ._ x xs) := member.here
| ._ ._ (@el_member.there ._ _ _ _ m) := member.there (el_member_to_member m)

inductive void : Type

def member_st_decide {A : Type u} 
  (P : A → Prop) [decidable_pred P]
  (xs : list A)
  : member_st P xs ⊕ (member_st P xs → void)
:= begin
induction xs,
{ right, 
  intros H, cases H },
{ induction ih_1,
  { left, 
    apply member_st.there, assumption
  },
  { apply (@decidable.by_cases (P a)); intros,
    { left, apply member_st.here, assumption },
    { right, intros contra, cases contra,
      contradiction, apply a_2, assumption
    }
  }
}
end

def el_member_decide {A : Type u} [decidable_eq A]
  (x : A) (xs : list A)
  : el_member x xs ⊕ (el_member x xs → void)
:=
begin
induction xs,
{ right, 
  intros H, cases H },
{ induction ih_1,
  { left, 
    apply el_member.there, assumption
  },
  { apply (@decidable.by_cases (x = a)); intros,
    { subst a, left, apply el_member.here },
    { right, intros contra, cases contra,
      contradiction, apply a_2, assumption
    }
  }
}
end

def check_member {A : Type u} [decidable_eq A]
  (x : A) (xs : list A)
  : option (member xs)
  := match el_member_decide x xs with
  | (sum.inl m) := some (el_member_to_member m)
  | (sum.inr _) := none
  end

end list