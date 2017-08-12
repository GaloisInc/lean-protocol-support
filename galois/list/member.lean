import .preds

universes u

namespace list

inductive member {A : Type u} : list A → Type u
| here : ∀ {x : A} {xs : list A}, member (x :: xs)
| there : ∀ {x : A} {xs : list A}, member xs → member (x :: xs)

namespace member
definition value {A : Type u} 
  : ∀ {xs : list A}, member xs -> A
| (x :: xs) member.here := x
| (x :: xs) (member.there m) := value m
end member

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

namespace member
def to_el_member {A : Type u}
  : ∀ {xs : list A} (m : member xs), el_member m.value xs
| (x :: xs) here := el_member.here
| (x :: xs) (there m) := el_member.there (to_el_member m)
end member

namespace member_st
def to_member {A : Type u} {P : A → Prop}
  : ∀ {xs : list A}, member_st P xs → member xs
| ._ (@here ._ ._ x xs H) := member.here
| ._ (@there ._ ._ _ _ m) := member.there (to_member m)
end member_st

namespace el_member
def to_member {A : Type u}
  : ∀ {x : A} {xs : list A}, el_member x xs → member xs
| ._ .(x :: xs) (@here ._ x xs) := member.here
| ._ ._ (@there ._ _ _ _ m) := member.there (to_member m)
end el_member

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
  | (sum.inl m) := some m.to_member
  | (sum.inr _) := none
  end

lemma el_member_value {A : Type u}
  (x : A) (xs : list A) (m : el_member x xs)
  : m.to_member.value = x
:= begin 
induction m; simp [member.value, el_member.to_member],
assumption
end

lemma member_st_P_value {A : Type u}
  {P : A → Prop} {xs : list A}
  (m : member_st P xs)
  : P m.to_member.value
:= begin
induction m; simp [member_st.to_member, member.value];
assumption,
end

def check_member_ok {A : Type u} [decidable_eq A]
  (x : A) (xs : list A)
  (m : xs.member)
  (H : check_member x xs = some m)
  : m.value = x
:= begin
unfold check_member at H,
cases (el_member_decide x xs);
  dsimp [check_member] at H;
  try {contradiction},
injection H with H', clear H,subst m,
apply el_member_value,
end

end list