import galois.tactic
       .init .tail .inter .map_accum_lemmas .take_drop_lemmas .preds .fin_nth

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
  apply_in H not_not_elim,
  rw ← list.index_of_lt_length at H,
  have H1 : list.index_of x xs ≠ list.length (xs ++ ys),
  apply ne_of_lt, rw list.length_append,
  apply lt_of_lt_of_le, assumption,
  rw add_comm,
  apply le_add_of_nonneg_left, apply nat.zero_le,
  rw (if_neg H1), apply_instance,
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

end list
