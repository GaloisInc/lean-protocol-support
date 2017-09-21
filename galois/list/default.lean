import galois.tactic
       .init .tail .inter .map_accum_lemmas .nth
       .take_drop_lemmas .preds .fin_nth

universe u

def second {X A B : Type} (f : A -> B) : X × A -> X × B
| (x, y) := (x, f y)

lemma second_simpl {X A B : Type} (f : A -> B)
  (x : X) (y : A)
  : second f (x, y) = (x, f y)
  := rfl

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


def find_option {A} [decidable_eq A] (item: A) (l : list A) : option ℕ :=
let index := list.index_of item l in
if index = l.length then none else some index

lemma find_option_mem_len {A} [decidable_eq A] {x : A} {xs : list A}
  (H : x ∈ xs)
  : ∃ n, xs.find_option x = some n ∧ n < xs.length
:= begin
rw ← list.index_of_lt_length at H,
destruct (find_option x xs),
{ intros Hnone, exfalso,
  unfold find_option at Hnone, dsimp at Hnone,
  rw if_neg at Hnone, injection Hnone,
  apply ne_of_lt, assumption },
{ intros n Hn, constructor, split, assumption,
  unfold find_option at Hn, dsimp at Hn,
  have H : index_of x xs ≠ length xs,
  apply ne_of_lt, assumption,
  rw (if_neg H) at Hn, injection Hn with Hn',
  rw ← Hn', assumption
}
end

lemma find_option_mem {A} [decidable_eq A] {x : A} {xs : list A}
  (H : x ∈ xs)
  : ∃ n, xs.find_option x = some n
:= begin
apply_in H find_option_mem_len,
induction H with n H, induction H with H H',
constructor, assumption,
end

lemma find_index_append {A} {P : A → Prop} [decidable_pred P]
  (xs ys : list A)
  (n : ℕ)
  (Hn : n ≠ xs.length)
  (H : xs.find_index P = n)
  : (xs ++ ys).find_index P = n
:= begin
revert n,
induction xs; intros,
{ dsimp [list.index_of, list.find_index] at H, subst n,
  exfalso, apply Hn, reflexivity, },
{ dsimp [list.index_of, list.find_index] at H,
  rename a x,
  apply (if HPx : P x then _ else _),
  { rw (if_pos HPx) at H, subst n,
    dsimp [list.index_of, list.find_index],
    rw (if_pos HPx), },
  { rw (if_neg HPx) at H,
    dsimp, dsimp [list.index_of, list.find_index],
    rw (if_neg HPx),
    cases n, injection H,
    rename a n, injection H with H', clear H,
    f_equal, apply ih_1, intros contra, apply Hn,
    dsimp [list.length], dsimp [has_add.add, nat.add],
    f_equal, assumption, assumption
  }
}
end

lemma index_of_append {A} [decidable_eq A] (x : A) (xs ys : list A)
  (n : ℕ)
  (Hn : n ≠ xs.length)
  (H : list.index_of x xs = n)
  : list.index_of x (xs ++ ys) = n
:= begin
apply list.find_index_append; assumption
end

lemma find_option_append {A} [decidable_eq A] (x : A) (xs ys : list A)
  (n : ℕ)
  (Hn : xs.find_option x = some n)
  : (xs ++ ys).find_option x = some n
:= begin
unfold find_option at Hn, dsimp at Hn,
apply (if H : list.index_of x xs = list.length xs then _ else _),
{ rw (if_pos H) at Hn, contradiction, },
{ rw (if_neg H) at Hn,
  injection Hn with Hn', clear Hn,
  dsimp, dsimp [find_option],
  rw list.index_of_append, tactic.rotate 2, assumption,
  tactic.swap, intros contra, apply H, subst n, assumption,
  rw list.index_of_eq_length at H, subst Hn',
  rw [not_not] at H,
  rw ← list.index_of_lt_length at H,
  have H1 : list.index_of x xs ≠ list.length (xs ++ ys),
  apply ne_of_lt, rw list.length_append,
  apply lt_of_lt_of_le, assumption,
  rw add_comm,
  apply le_add_of_nonneg_left, apply nat.zero_le,
  simp [H1],
 }
end

lemma nth_cons_drop {A : Type} : forall h t n (i :A),
n ≠ 0 ->
list.nth (h :: t) (n) = some i ->
list.nth t (n - 1) = some i :=
begin
intros,
cases n,
{ contradiction },
{
  dsimp at *,
  simp at *,
  assumption,
}
end

lemma pair_induction_same_length {X Y}
  (P : list X → list Y → Sort u)
  (P0 : P [] [])
  (PS : ∀ x y xs ys, P xs ys → P (x :: xs) (y :: ys))
  (xs : list X) (ys : list Y) (H : xs.length = ys.length)
  : P xs ys
:= begin
revert xs, induction ys; intros; dsimp at H,
{ apply_in H list.eq_nil_of_length_eq_zero, subst xs,
  assumption, },
{ cases xs; dsimp at H, contradiction,
  apply PS, apply ih_1,
  apply nat.add_right_cancel, assumption,
}
end

lemma map_compose {A B C : Type}
  (f : A -> B) (g : B -> C) (xs : list A)
  : map (g ∘ f) xs = map g (map f xs)
:=
begin
induction xs,
{ reflexivity },
{ simp [map] }
end

lemma reverse_core_app {A : Type} (xs ys zs : list A)
  : list.reverse_core xs (ys ++ zs)
  = list.reverse_core xs ys ++ zs
:= begin
revert ys zs,
induction xs; intros,
{ simp [list.reverse_core] },
{ simp [list.reverse_core],
  rw <- list.cons_append,
  rw ih_1 }
end

lemma cons_reverse {A : Type} (x : A) (xs : list A)
  : list.reverse (x :: xs) = list.reverse xs ++ [x]
:=
begin
unfold list.reverse,
simp [list.reverse_core],
induction xs,
{ reflexivity },
{ simp [list.reverse_core],
  rw <- (reverse_core_app a_1 [a] [x]),
  dsimp, reflexivity
 }
end

lemma cons_reverse_app {A : Type} (x : A) (xs : list A)
: (list.reverse ∘ list.cons x) xs =
   ((λ xs, xs ++ [x]) ∘ list.reverse) xs
:=
begin
induction xs,
{ reflexivity },
{ simp [function.comp], }
end

lemma zip_same_length {X Y}
  (xs ys : list X) (xs' ys' : list Y) (H : xs.length = xs'.length)
  : zip (xs ++ ys) (xs' ++ ys')
  = zip xs xs' ++ zip ys ys'
:= begin
revert H xs' xs,
apply list.pair_induction_same_length,
reflexivity, intros, dsimp [list.zip, list.zip_with],
f_equal, assumption
end

lemma zip_map_r {X Y Z} (xs : list X) (ys : list Y)
  (f : Y → Z)
  : zip xs (map f ys) =
  list.map (second f) (list.zip xs ys)
:= begin
revert ys, induction xs; intros,
{ reflexivity },
{ cases ys,
  { reflexivity },
  { dsimp [list.zip, list.zip_with], f_equal,
    specialize (ih_1 a_3),
    unfold list.zip at ih_1,
    rw ih_1,
  }
 }
end

lemma map_fst_second {X A B : Type}
  (xs : list (X × A)) (f : A -> B)
  : map (prod.fst ∘ second f) xs
  = map prod.fst xs
:= begin
induction xs,
{ reflexivity },
{ simp only [list.map],
  cases a with i1 i2,
  simp only [second],
  rw ih_1, reflexivity
}
end

lemma map_not_nil {A B} (xs) (f : A -> B)
  (H : xs ≠ []) : list.map f xs ≠ [] :=
begin
cases xs,
{ contradiction },
{ simp [list.map], }
end

lemma map_nil {A B : Type} (f : A -> B)
  (xs : list A)
  (H : xs = [])
  : list.map f xs = []
  :=
begin
rw H, reflexivity
end

lemma repeat_length {A} (x : A) (n : ℕ)
  : (list.repeat x n).length = n
:= begin
induction n; simp [list.repeat, list.length],
end

def mem_induction {A : Type u}
  (P : A → list A → Prop)
  (Phere : ∀ x xs, P x (x :: xs))
  (Pthere : ∀ x y ys, P x ys → P x (y :: ys))
  (x : A) (xs : list A) (H : x ∈ xs)
  : P x xs
:= begin
induction xs, cases H,
dsimp [has_mem.mem, list.mem] at H,
induction H, subst a, apply Phere,
apply Pthere, apply ih_1, assumption,
end

end list

universe variable v

namespace list

variables {α : Type u} {β : Type v}

/- null theorems -/

-- Return true if list is empty
--
-- null x is equivalent to x = nil, but always decidable even if equality
-- of list elements is undecidable
def null : list α → Prop := λx, x = nil

instance null_decidable : ∀ xs : list α, decidable (null xs)
| nil := is_true (begin unfold null end)
| (x :: xs) := is_false (begin unfold null, contradiction end)

/- foldl theorem -/

-- Recursor to prove properties about a list and a left-fold over that list
protected
lemma foldl_rec_gen (P : list β → α → Prop)
                    (f : α → β → α)
                    (h : ∀(l : list β) (t : α) (e : β), P l t →  P (l ++ [e]) (f t e))
: ∀(r : list β) (s : α), P r s → ∀ (l : list β), P (r ++ l) (foldl f s l)
| r s p l :=
begin
  revert r s p,
  induction l,
  case list.nil { intros r s p, simp, exact p, },
  case list.cons e l ind {
    intros r s p,
    simp [foldl],
    have g := ind (r ++ [e]) (f s e) (h r s e p),
    simp at g,
    exact g,
  }
end

-- Recursor to prove properties about a list and a left-fold over that list
protected
theorem foldl_rec (P : list β → α → Prop)
                  (f : α → β → α)
                  (ind_step : ∀(l : list β) (t : α) (e : β), P l t →  P (l ++ [e]) (f t e))
                  (s : α)
                  (base_case : P nil s)
                  (l : list β)
: P l (foldl f s l) :=
  list.foldl_rec_gen P f ind_step nil s base_case l

def drop_last {a : Type} (l : list a) := list.remove_nth l (list.length l - 1)


end list