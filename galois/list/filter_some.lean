universes u

namespace list

def filter_some {A : Type u} : list (option A) → list A
| [] := []
| (mx :: xs) := (match mx with
  | none := λ l, l
  | some x := list.cons x
  end) (filter_some xs)

lemma map_filter_some {A B} (f : A → B) (xs : list (option A))
  : filter_some (map (option.map f) xs)
  = map f (filter_some xs)
:= begin
induction xs; dsimp [list.map, option.map, option.bind, filter_some],
{ reflexivity },
{ induction a; dsimp [option.map, option.bind, function.comp, filter_some],
  { assumption },
  { rw ih_1 }
}
end

end list