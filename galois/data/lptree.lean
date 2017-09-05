-- Vaguely following an approach taken in this paper:
-- https://arxiv.org/pdf/1401.7886.pdf
-- author: Ben Sherman
import data.list.basic
       galois.list.preds
       galois.tactic
       galois.nat.lemmas
       galois.list

universes u v

def depair {A} : list (A × A) -> list A
| [] := []
| ((x, y) :: zs) := y :: x :: depair zs

namespace binary_tree

/-- An `lptree A` represents a binary tree (without internal nodes)
    whose left subtrees are all perfect, where the sizes of these
    perfect left subtrees increase as the roots of those subtrees
    move towards the root of the entire tree.
    (the "lp" in "lptree" is for left-perfect)

    Effectively, an `lptree unit` is a binary natural number,
    and for any `lptree A`, this corresponding binary natural number
    indicates the number of items of type A in the tree.
-/
inductive lptree : Type u -> Type (u + 1)
| nil : ∀ {A}, lptree A
| cons : ∀ {A}, option A -> lptree (A × A) -> lptree A

def double {A : Type u} {B : Type v} (f : A → B)
  (x : A × A) : B × B :=
  let (a, b) := x in (f a, f b).

namespace lptree

def height : ∀ {A : Type u}, lptree A → ℕ
| _ nil := 0
| _ (cons mx t) := height t + 1

def size : ∀ {A : Type u}, lptree A → ℕ
| _ nil := 0
| _ (cons mx t) := 2 * size t + (match mx with
  | some _ := 1
  | none := 0
  end)

/-- Indicates when an `lptree A` has at least one value of `A` in it
    (i.e., its corresponding binary natural number is nonzero.)
-/
inductive nonzero : ∀  {A : Type u}, lptree A -> Prop
| cons_some : ∀ {A} (a : A) t, nonzero (lptree.cons (some a) t)
| extend : ∀ {A} ma (t : lptree (A × A)), @nonzero (A × A) t ->
    nonzero (lptree.cons ma t)

/-- Add a single element to a left-perfect tree.
    (A generalization of adding one to a binary natural number.)
-/
def insert : ∀ {A : Type u}, A -> lptree A -> lptree A
| A x lptree.nil := lptree.cons (some x) lptree.nil
| A x (lptree.cons none t') := lptree.cons (some x) t'
| A x (lptree.cons (some y) t') := lptree.cons none (insert (y, x) t')

def map : ∀ {A : Type u} {B : Type v}, (A → B) → lptree A → lptree B
| A B f lptree.nil := lptree.nil
| A B f (lptree.cons x t') := lptree.cons (option.map f x) (map (double f) t')

/-- Enumerate the leaves of an lptree from right to left
    (i.e., going up towards larger left-perfect subtrees
-/
def leaves : ∀ {A}, lptree A -> list A
| A nil := []
| A (cons mx t) := (match mx with
  | none := λ zs, zs
  | (some x) := list.cons x
  end) (depair (leaves t))

/-- Decision procedure to determine whether
    an lptree is nonempty
-/
def nonzero_bool
  : ∀ {A : Type}, lptree A -> bool
| _ nil := false
| _ (cons (some x) t) := true
| _ (cons none t) := nonzero_bool t

def nonzero_bool_equiv {A : Type}
  (t : lptree A)
  : nonzero_bool t = true ↔ nonzero t
:=
begin
split; intro H,
{ induction t,
  { contradiction },
  { cases a, simp [nonzero_bool] at H,
    { constructor,
      apply ih_1, assumption },
    { constructor }
  }
},
{ induction H,
  { simp [nonzero_bool] },
  { cases ma,
    { simp [nonzero_bool], assumption },
    { reflexivity }
  }
}
end

def nonzero_dec {A : Type}
  (t : lptree A)
  : decidable (nonzero t)
:=
begin
rw <- nonzero_bool_equiv,
apply bool.decidable_eq
end

end lptree

lemma map_insert {A B} (f : A → B) (t : lptree A) (x : A)
  : (t.insert x).map f = (t.map f).insert (f x)
:= begin
revert B,
induction t; intros, dsimp [lptree.insert, lptree.map], reflexivity,
induction a; simp [lptree.insert, lptree.map, option.map, option.bind],
rw ih_1, reflexivity,
end

lemma insert_size {A : Type u} (x : A) (t : lptree A)
  : (t.insert x).size = t.size + 1
:= begin
induction t; dsimp [lptree.size, lptree.insert],
{ simp },
{ induction a; dsimp [lptree.size, lptree.insert],
  { reflexivity },
  { rw ih_1,
    rw mul_add, repeat { rw add_assoc },
    f_equal, }
}
end

lemma map_height {A B} (f : A → B) (t : lptree A)
  : (t.map f).height = t.height
:= begin
revert B,
induction t; intros; simp [lptree.map, lptree.height],
f_equal, apply ih_1,
end

lemma map_size {A B} (f : A → B) (t : lptree A)
  : (t.map f).size = t.size
:= begin
revert B,
induction t; intros; simp [lptree.map, lptree.size],
induction a; simp [lptree.map, option.map, option.bind, lptree.size],
rw mul_comm, f_equal, apply ih_1,
f_equal, rw mul_comm, f_equal, apply ih_1,
end

lemma size_le_height {A : Type u} (t : lptree A)
  : t.size + 1 ≤ 2 ^ t.height
:= begin
induction t; dsimp [lptree.size, lptree.height, nat.pow],
{ rw add_comm, },
{ induction a; dsimp [lptree.size],
  { rw add_assoc, rw (add_comm 0 1), rw add_zero, rw mul_comm,
    rw nat.mul_2_add, rw nat.mul_2_add, rw add_assoc,
    apply nat.le_add_compat,
    apply le_trans, tactic.swap, assumption,
    constructor, constructor, assumption,
   },
  { rw add_assoc, rw ← nat.mul_2_add, rw ← mul_comm,
    rw ← add_mul, apply mul_le_mul, assumption,
    apply le_refl, apply nat.zero_le, apply nat.zero_le,
  }
}
end

inductive nz_minimal : ∀ {A}, lptree A → Prop
| last : ∀ {A} x : A, nz_minimal (lptree.cons (some x) lptree.nil)
| cons : ∀ {A} (mx : option A) t, nz_minimal t → nz_minimal (lptree.cons mx t)

inductive minimal {A} : lptree A → Prop
| zero : minimal (lptree.nil)
| nz_minimal : ∀ t, nz_minimal t → minimal t

lemma insert_nz_minimal {A : Type u} (t : lptree A)
  (mint : minimal t) (x : A)
  : nz_minimal (t.insert x)
:= begin
induction mint,
{ constructor },
{ induction a,
  { dsimp [lptree.insert], constructor, constructor },
  { induction mx; dsimp [lptree.insert],
    { constructor, assumption },
    { constructor, apply ih_1, assumption }
  }
}
end

/-- If you add one to an lptree, it is nonzero
-/
def insert_nonzero {A : Type u} (t : lptree A)
  : ∀ x : A, lptree.nonzero (t.insert x) :=
begin
induction t with A A ma t IHt; intros x,
{ simp [lptree.insert], constructor },
{ cases ma,
  { simp [lptree.insert], constructor },
  { simp [lptree.insert], constructor, apply IHt }
}
end


def list_to_lptree {A : Type u} : list A -> lptree A :=
  list.foldr lptree.insert lptree.nil

lemma map_list_to_lptree {A : Type u} {B : Type v}
  (f : A → B) (xs : list A)
  : (list_to_lptree xs).map f = list_to_lptree (xs.map f)
:= begin
revert B,
induction xs; intros, reflexivity,
dsimp [list_to_lptree, lptree.map, list.map],
rw map_insert, f_equal, unfold list_to_lptree at ih_1,
apply ih_1,
end

lemma list_to_lptree_length {A : Type u} (xs : list A)
  : (list_to_lptree xs).size = xs.length
:= begin
unfold list_to_lptree,
induction xs; dsimp [list.foldr, lptree.size],
{ reflexivity },
{ rw insert_size, rw ih_1, }
end

/-- This only is correct if the lptree is minimal. -/
def log2_of_succ_lptree {A} (t : lptree A)
  := t.height

def log2_of_succ (n : ℕ) :=
  log2_of_succ_lptree (list_to_lptree (list.repeat unit.star n))

def log2 (n : ℕ) : ℕ := log2_of_succ n.pred

lemma list_to_lptree_nz_minimal {A} (x : A) (xs : list A)
  : nz_minimal (list_to_lptree (x :: xs))
:= begin
revert x,
induction xs; intros,
constructor,
dsimp [list_to_lptree],
apply insert_nz_minimal, apply minimal.nz_minimal,
apply ih_1,
end

lemma list_to_lptree_minimal {A} (xs : list A)
  : minimal (list_to_lptree xs)
:= begin
cases xs, apply minimal.zero,
apply minimal.nz_minimal, apply list_to_lptree_nz_minimal
end

lemma same_length_map {A : Type u} {B : Type v}
  (xs : list A) (ys : list B) (Hlen : xs.length = ys.length)
  : xs.map (λ _, unit.star) = ys.map (λ _, unit.star)
:= begin
apply list.pair_induction_same_length _ _ _ xs ys Hlen,
simp, reflexivity, intros,
simp [list.map], simp [list.map], f_equal,
assumption
end

lemma lptree_height_skeleton {A} (t : lptree A)
  : t.height = (t.map (λ _, unit.star)).height
:= begin
symmetry, apply map_height,
end

lemma lptree_height_length {A B} (xs : list A) (ys : list B)
  (Hlen : xs.length = ys.length)
  : (list_to_lptree xs).height = (list_to_lptree ys).height
:= begin
rw (lptree_height_skeleton (list_to_lptree xs)),
rw (lptree_height_skeleton (list_to_lptree ys)),
repeat { rw map_list_to_lptree },
rw same_length_map, assumption,
end

lemma list_to_lptree_height {A} (xs : list A)
  : (list_to_lptree xs).height = log2_of_succ xs.length
:= begin
rw ← list_to_lptree_length,
unfold log2_of_succ log2_of_succ_lptree,
rw list_to_lptree_length,
apply lptree_height_length,
rw list.repeat_length,
end

lemma list_to_lptree_height' {A} (xs : list A)
  : (list_to_lptree xs).height = log2 xs.length.succ
:= begin
unfold log2, dsimp [nat.pred],
apply list_to_lptree_height,
end

lemma lptree_leaves_cons {A} (t : lptree A)
  (x : A)
  : (t.insert x).leaves =
     x :: t.leaves
  :=
begin
induction t,
{ reflexivity },
{ cases a; simp only [lptree.insert, lptree.leaves],
  { rw ih_1,
    simp only [depair]
   }
}
end

/-- If we produce an lptree from a list of elements,
    then enumerate the leaves, we get the same list back
-/
lemma lptree_leaves_list {A} (xs : list A)
  : (list_to_lptree xs).leaves = xs
  :=
begin
induction xs,
{ reflexivity },
{ simp [list_to_lptree], rw lptree_leaves_cons,
  f_equal, assumption
}
end

lemma depair_nil {A} (xs : list (A × A))
  : xs = [] -> depair xs = []
:= begin
intros H, rw H, reflexivity
end

lemma lptree_not_nonzero_no_leaves {A : Type}
  (t : lptree A)
  (H : ¬ lptree.nonzero t)
  : t.leaves = []
:= begin
rw <- lptree.nonzero_bool_equiv at H,
induction t,
{ reflexivity },
{ cases a,
  { simp [lptree.leaves],
    apply depair_nil, apply ih_1,
    simp [lptree.nonzero_bool] at H,
    assumption
     },
  { simp [lptree.nonzero_bool] at H,
    contradiction }
}
end

lemma list_to_lptree.nonzero {A} (xs : list A)
  (H : xs ≠ []) : lptree.nonzero (list_to_lptree xs) :=
begin
cases xs,
{ contradiction },
{ simp [list_to_lptree], apply insert_nonzero }
end

end binary_tree