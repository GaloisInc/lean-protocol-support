/- Some theorems about list intersection -/

namespace list

@[simp]
theorem nil_inter {α : Type} [decidable_eq α] (x : list α) : list.nil ∩ x = [] := rfl

@[simp]
theorem inter_nil {α : Type} [decidable_eq α] (x : list α) : x ∩ list.nil = [] :=
begin
  induction x with v xr ind,
  { refl, },
  { unfold has_inter.inter,
    unfold has_inter.inter at ind,
    simp [list.inter, ind],
  },
end

theorem inter_conjunction {α : Type} [decidable_eq α] (e : α) (x y : list α)
: e ∈ (x ∩ y) ↔ e ∈ x ∧ e ∈ y :=
begin
  induction x with v xr ind,
  { simp, },
  unfold has_inter.inter,
  unfold has_inter.inter at ind,
  simp [list.inter],
  apply dite (v ∈ y),
  { intro v_in_y,
    simp [v_in_y, ind],
    apply dite (e = v),
    { intro e_eq_v,
      simp [e_eq_v, v_in_y],
    },
    { intro e_ne_v,
      simp [e_ne_v],
    }
  },
  { intro v_notin_y,
    simp [v_notin_y, ind],
    apply dite (e = v),
    { intro e_eq_v,
      simp [e_eq_v, v_notin_y],
    },
    { intro e_ne_v,
      simp [e_ne_v],
    },
  },
end

end list
