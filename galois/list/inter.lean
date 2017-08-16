/- Some theorems about list intersection -/

namespace list

@[simp]
theorem nil_inter {α : Type} [decidable_eq α] (x : list α) : list.nil ∩ x = [] := rfl

@[simp]
theorem cons_inter {α : Type} [decidable_eq α] (a : α) (x y : list α)
: (a::x) ∩ y = if a ∈ y then a :: (x ∩ y) else x ∩ y := rfl

@[simp]
theorem inter_nil {α : Type} [decidable_eq α] (x : list α) : x ∩ list.nil = [] :=
begin
  induction x with v xr ind,
  { refl, },
  { simp [cons_inter, ind], },
end

theorem inter_conjunction {α : Type} [decidable_eq α] (e : α) (x y : list α)
: e ∈ (x ∩ y) ↔ e ∈ x ∧ e ∈ y :=
begin
  induction x,
  case list.nil { simp, },
  case list.cons v xr ind {
    simp,
    by_cases (v ∈ y) with h,
    all_goals {
      simp [h, ind],
      by_cases (e = v) with e_eq_v,
      all_goals { simp [*], },
    },
  },
end

end list
