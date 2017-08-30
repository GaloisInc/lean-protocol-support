/-
Defines a lookup function for assoc-lists.
-/
universes u v

namespace list

section

parameter {α : Type u}
parameter {β : Type v}
parameter [decidable_eq α]
parameter (k : α)

/-- Return the key associated with the name or fail if not found. -/
def alist_lookup : list (α × β) → option β
| [] := option.none
| ((h,v) :: r) :=
  if h = k then
    option.some v
   else
    alist_lookup r

/-- Recursive function to implment alist_lookup_and_remove below. -/
def alist_lookup_and_remove_core
: list (α × β) → list (α × β) → option (β × list (α × β))
| prev [] := option.none
| prev ((h,v) :: r) :=
  if h = k then
    option.some (v, prev.reverse ++ r)
   else
    alist_lookup_and_remove_core ((h,v)::prev) r

/-- Return the key associated with the name and a list with that element removed
 or fail if not found. -/
def alist_lookup_and_remove  : list (α × β) → option (β × list (α × β)) :=
  alist_lookup_and_remove_core []

end

end list
