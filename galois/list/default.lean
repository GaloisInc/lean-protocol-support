import .init .tail .inter .map_accum_lemmas .take_drop_lemmas .preds .fin_nth

namespace list

-- This runs a function over a list returning the intermediate results and a
-- a final result.
def map_accuml {α  σ β : Type} (f : σ → α → β × σ) : σ → list α → (list β × σ)
| c [] := ([], c)
| c (y::yr) :=
  let z := f c y in
  let r := map_accuml z.2 yr in
  (z.1 :: r.1, r.2)

def first_index_of_core {α : Type} (p : α → bool) : ℕ → list α → option (ℕ × α)
| c [] := option.none
| c (h::r) :=
  if p h = tt then
    option.some (c,h)
  else
    first_index_of_core (c+1) r

-- This searches a list for an element that satisfies a predicate.
--
-- If it finds an element, it returns the index and element.  Otherwise, it
-- returns none.
def first_index_of {α : Type} (p : α → bool) (l : list α) : option (ℕ × α) :=
  first_index_of_core p 0 l

end list
