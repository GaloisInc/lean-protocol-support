open nat

namespace list

  variable {T : Type}

  definition rol1 : list T → list T
  | nil        := nil
  | (cons a l) := l ++ [a]

  definition ror1_aux : T → list T → list T
  | a nil        := cons a nil
  | a (cons b l) := cons b (cons a l)

  definition ror1 : list T → list T
  | nil        := nil
  | (cons a l) := ror1_aux a (ror1 l)

  definition rol : list T → ℕ → list T
  | l 0        := l
  | l (succ n) := rol1 (rol l n)

  --definition ror (l : list T) (n : ℕ) : list T := reverse (rol (reverse l) n)
  definition ror : list T → ℕ → list T
  | l 0        := l
  | l (succ n) := ror1 (ror l n)

  theorem ror1_concat (l : list T) (a : T) 
  : ror1 (l ++ [a]) = a::l :=
  begin
    induction l,
    case list.nil { refl, },
    case list.cons h r ind {
      simp [ror1, ind, ror1_aux],
    },
  end

  theorem ror1_rol1 (l : list T) : ror1 (rol1 l) = l :=
  begin
    induction l,
    case list.nil { refl, },
    case list.cons h r ind {
      simp [rol1, ror1_concat],
    }
  end

  theorem rol1_ror1_aux (a : T) (l : list T) : rol1 (ror1_aux a l) = cons a (rol1 l) :=
  list.cases_on l rfl (λ b l', rfl)

  theorem rol1_ror1 (l : list T) : rol1 (ror1 l) = l :=
  list.rec_on l rfl (λ a l' H, eq.trans (rol1_ror1_aux _ _) (congr_arg (cons a) H))

  theorem length_rol1 (l : list T) : length (rol1 l) = length l :=
  begin
    induction l,
    case list.nil { refl, },
    case list.cons h r ind {
      simp [rol1],
    }
  end

  theorem length_rol (l : list T) (n : ℕ) : length (rol l n) = length l :=
  nat.rec_on n rfl (λ a H, eq.trans (length_rol1 _) H)

  theorem length_ror1_aux (a : T) (l : list T) : length (ror1_aux a l) = succ (length l) :=
  list.cases_on l rfl (λ b l', rfl)

  theorem length_ror1 (l : list T) : length (ror1 l) = length l :=
  list.rec_on l rfl (λ a l' H, (eq.trans (length_ror1_aux a (ror1 l')) (congr_arg succ H)))

  theorem length_ror (l : list T) (n : ℕ) : length (ror l n) = length l :=
  nat.rec_on n rfl (λ a H, eq.trans (length_ror1 _) H)
  --eq.trans (@length_reverse _ _) (eq.trans (@length_rol _ _ _) (@length_reverse _ _))
  --by rewrite [↑ror, length_reverse, length_rol, length_reverse]

  theorem rol_rol (m n : ℕ) (l : list T) : rol (rol l m) n = rol l (m + n) :=
  nat.rec_on n rfl (λ a H, congr_arg rol1 H)

  --theorem ror_ror (m n : ℕ) (l : list T) : ror (ror l m) n = ror l (m + n) :=
  --by rewrite [↑ror, reverse_reverse, rol_rol]

end list
