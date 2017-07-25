/- Basic theorems about bool -/

@[simp]
lemma coe_sort_bool_to_equality (b:bool) : @coe_sort _ coe_sort_bool b = (b = tt) :=
begin
  cases b,
  all_goals { simp [coe_sort, has_coe_to_sort.coe]},
end
