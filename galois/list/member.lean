import .preds

universes u

namespace list

inductive member {A : Type u} : list A → Type u
| here : ∀ {x : A} {xs : list A}, member (x :: xs)
| there : ∀ {x : A} {xs : list A}, member xs → member (x :: xs)

namespace member

section
parameter {α : Type u}

def value
  : ∀ {xs : list α}, member xs -> α
| (x :: xs) member.here := x
| (x :: xs) (member.there m) := value m

-- Given a member of the append of two lists, this returns a member
-- of one or the other depending on which list is referenced.
def case_append :
 Π {l1 l2 : list α}, member (l1 ++ l2) →  member l1 ⊕ member l2
| (h::r) _ member.here := sum.inl member.here
| (h::r) l2 (member.there m) :=
  match @case_append r l2 m with
  | sum.inr z := sum.inr z
  | sum.inl z := sum.inl (member.there z)
  end
| [] l2  m :=
  let q := congr_arg member (list.nil_append l2) in
  sum.inr (cast q m)

end
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

def to_member_st {A : Type u}
  : ∀ {xs : list A} (m : member xs) (P : A → Prop) (Pm : P m.value), member_st P xs
| (x :: xs) here _ Px := member_st.here Px
| (x :: xs) (there m) _ Px := member_st.there (to_member_st m _ Px)
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

def member_st_decide' {A : Type u}
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

def member_st_decide {A : Type u}
  (P : A → Prop) [decidable_pred P]
  : ∀ (xs : list A)
  , member_st P xs ⊕ (member_st P xs → void)
| [] := begin right, intros x, cases x end
| (x :: xs) := if H : P x
    then sum.inl (@member_st.here _ _ x xs H)
    else match member_st_decide xs with
      | (sum.inr f) := sum.inr
        begin
          intros contra, cases contra,
          contradiction, apply f, assumption
        end
      | (sum.inl m) := sum.inl (member_st.there m)
      end

def check_member_st {A : Type u}
  (P : A → Prop) [decidable_pred P]
  (xs : list A) : option (member_st P xs)
  := match member_st_decide P xs with
  | sum.inl r := some r
  | sum.inr contra := none
  end


lemma member_st_decide_present {A : Type u}
  {P : A → Prop} [decP : decidable_pred P]
  {xs : list A}
  (m : member_st P xs)
  : psigma (λ m' : member_st P xs,
     member_st_decide P xs = sum.inl m')
:= begin
induction m; clear xs; rename xs_1 xs,
{ constructor, unfold member_st_decide,
    rw (dif_pos a),
},
{ have H := decP x, induction H,
  { induction ih_1 with mxs Pmxs,
    constructor,
    unfold member_st_decide,
    rw (dif_neg a_1), rw Pmxs,
    dsimp [member_st_decide], reflexivity,
  },
  { constructor,
    unfold member_st_decide,
    rw (dif_pos a_1),
  }
}
end

def el_member_decide {A : Type u} [decidable_eq A]
  (z : A) : ∀ (xs : list A)
  , el_member z xs ⊕ (el_member z xs → void)
| [] := begin right, intros x, cases x end
| (x :: xs) := if H : z = x
    then begin induction H, exact sum.inl el_member.here end
    else match el_member_decide xs with
      | (sum.inr f) := sum.inr
        begin
          intros contra, clear _match, cases contra,
          contradiction, apply f, assumption
        end
      | (sum.inl m) := sum.inl (el_member.there m)
      end

lemma el_member_decide_present {A : Type u} [deceqA : decidable_eq A]
  {z : A} {xs : list A}
  (m : el_member z xs)
  : psigma (λ m', el_member_decide z xs = sum.inl m')
:= begin
induction m; clear z xs; rename xs_1 xs,
{ constructor, unfold el_member_decide,
    rw (dif_pos (eq.refl x)),
},
{ have H := deceqA y x, induction H,
  { induction ih_1 with mxs Pmxs,
    constructor,
    unfold el_member_decide,
    rw (dif_neg a_1), rw Pmxs,
    dsimp [el_member_decide], reflexivity,
  },
  { induction a_1, constructor,
    unfold el_member_decide,
    rw (dif_pos (eq.refl _)),
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

lemma check_member_ok {A : Type u} [decidable_eq A]
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

lemma check_member_present {A : Type u} [decidable_eq A]
  (xs : list A)
  (m : xs.member)
  : psigma (λ m', check_member m.value xs = some m')
:= begin
have m' := m.to_el_member,
have H := el_member_decide_present m',
unfold check_member,
induction H with m'' Hm'',
rw Hm'', dsimp [check_member],
constructor, reflexivity
end

end list
