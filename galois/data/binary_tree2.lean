
-- Vaguely following an approach taken in this paper:
-- https://arxiv.org/pdf/1401.7886.pdf
-- author: Ben Sherman
import data.list.basic
       galois.list.preds
       galois.tactic

namespace binary_tree

run_cmd mk_simp_attr `empt

universes u v

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
| nonzero_cons_some : ∀ {A} (a : A) t, nonzero (lptree.cons (some a) t)
| nonzero_extend : ∀ {A} ma (t : lptree (A × A)), @nonzero (A × A) t ->
    nonzero (lptree.cons ma t)

-- def ptree_to_lptree : ∀ {A} {n}, ptree A n -> lptree A
-- | A 0 x := lptree.cons (some x) lptree.nil
-- | A (nat.succ n') x:= lptree.cons none (@ptree_to_lptree (A × A) n' x)

/-- Add a single element to a left-perfect tree.
    (A generalization of adding one to a binary natural number.)
-/
def insert : ∀ {A : Type u}, A -> lptree A -> lptree A
| A x lptree.nil := lptree.cons (some x) lptree.nil
| A x (lptree.cons none t') := lptree.cons (some x) t'
| A x (lptree.cons (some y) t') := lptree.cons none (insert (y, x) t')

def map : ∀ {A : Type u} {B : Type v}, (A → B) → lptree A → lptree B
| A B f lptree.nil := lptree.nil
| A B f (lptree.cons none t') := lptree.cons none (map (double f) t')
| A B f (lptree.cons (some y) t') := lptree.cons (some (f y)) (map (double f) t')

end lptree

lemma map_insert {A B} (f : A → B) (t : lptree A) (x : A)
  : (t.insert x).map f = (t.map f).insert (f x)
:= begin
revert B,
induction t; intros, dsimp [lptree.insert, lptree.map], reflexivity,
induction a; simp [lptree.insert, lptree.map],
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
induction a; simp [lptree.map, lptree.height]; f_equal; apply ih_1,
end

lemma map_size {A B} (f : A → B) (t : lptree A)
  : (t.map f).size = t.size
:= begin
revert B,
induction t; intros; simp [lptree.map, lptree.size],
induction a; simp [lptree.map, lptree.size],
rw mul_comm, f_equal, apply ih_1,
f_equal, rw mul_comm, f_equal, apply ih_1,
end

lemma mul_2_add {n : nat} : n * 2 = n + n
:= begin
induction n, simp,
dsimp [has_mul.mul, nat.mul],
simp,
end

lemma le_add_r {x y : nat} : x ≤ x + y
:= begin
induction y, simp,
apply le_trans, assumption,
apply nat.add_le_add_left, constructor,
constructor,
end

lemma le_add_compat {x y x' y' : nat}
  (Hx : x ≤ x') (Hy : y ≤ y') : x + y ≤ x' + y'
:= begin
induction Hx, apply nat.add_le_add_left, assumption,
apply le_trans, apply ih_1,
simp, apply nat.add_le_add_left, constructor,
constructor,
end

lemma size_le_height {A : Type u} (t : lptree A)
  : t.size + 1 ≤ 2 ^ t.height
:= begin
induction t; dsimp [lptree.size, lptree.height, nat.pow],
{ rw add_comm, },
{ induction a; dsimp [lptree.size],
  { rw add_assoc, rw (add_comm 0 1), rw add_zero, rw mul_comm,
    rw mul_2_add, rw mul_2_add, rw add_assoc,
    apply le_add_compat,
    apply le_trans, tactic.swap, assumption,
    constructor, constructor, assumption,
   },
  { rw add_assoc, rw ← mul_2_add, rw ← mul_comm,
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

lemma repeat_length {A} (x : A) (n : ℕ)
  : (list.repeat x n).length = n
:= begin
induction n; simp [list.repeat, list.length],
end

lemma list_to_lptree_minimal {A} (xs : list A)
  : minimal (list_to_lptree xs)
:= begin
cases xs, apply minimal.zero,
apply minimal.nz_minimal, apply list_to_lptree_nz_minimal
end

lemma list.pair_induction_same_length {X Y}
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

lemma list_to_tree_height {A} (xs : list A)
  : (list_to_lptree xs).height = log2_of_succ xs.length
:= begin
rw ← list_to_lptree_length,
unfold log2_of_succ log2_of_succ_lptree,
rw list_to_lptree_length,
apply lptree_height_length,
rw repeat_length,
end

lemma list_to_tree_height' {A} (xs : list A)
  : (list_to_lptree xs).height = log2 xs.length.succ
:= begin
unfold log2, dsimp [nat.pred],
apply list_to_tree_height,
end

/-- Binary trees *with* internal nodes
    (which differs from both `ptree` and `lptree`)

    In this formulation, every binary tree has at least
    one item of type A in it.
-/
inductive tree (A : Type) : Type
| leaf (item : A) : tree
| node (item : A) (l r : tree) : tree

namespace tree
def height {A : Type} : tree A → ℕ
| (leaf x) := 0
| (node x l r) := max (height l) (height r) + 1
end tree

def twice {A} (f : A -> A -> A)
  (x y : A × A) : A × A :=
  let (a, b) := x in let (p, q) := y in
     (f a b, f p q).

def untwice_tree {A} (f : A -> A -> A)
  : tree (A × A) -> tree A
| (tree.leaf (x, y)) := tree.node (f x y) (tree.leaf x) (tree.leaf y)
| (tree.node (x, y) l r) := tree.node (f x y) (untwice_tree l) (untwice_tree r)

lemma max_same (n : ℕ) : max n n = n
:= begin
unfold max, rw (if_pos (le_refl n)),
end

lemma max_add {m n k : ℕ} : max (m + k) (n + k) = max m n + k
:= begin
unfold max,
apply (if H : m ≤ n then _ else _),
rw (if_pos H), rw if_pos,
apply nat.add_le_add_right, assumption,
rw (if_neg H), rw if_neg,
intros contra, apply H, rw ← nat.add_le_add_iff_le_right,
assumption,
end

lemma untwice_tree_height {A} (f : A → A → A)
  (x : tree (A × A))
  : (untwice_tree f x).height = x.height + 1
:= begin
induction x; induction item; dsimp [untwice_tree, tree.height],
{ rw max_same, },
{ rw ih_1, rw ih_2, clear ih_1 ih_2 fst snd,
  f_equal, rw max_add,
}
end

/-- Pick the item at the root of the tree -/
def root {A} : tree A -> A
| (tree.node x _ _) := x
| (tree.leaf x) := x

/-- Combine a left and right subtree into a single tree
    with some function that determines the root of the
    new tree from the roots of the subtrees
-/
def combine {A} (f : A -> A -> A) (l r : tree A)
  : tree A := tree.node (f (root l) (root r)) l r

lemma combine_height {A} (f : A → A → A) (l r : tree A)
  : (combine f l r).height = max l.height r.height + 1
:= rfl

/-- Compute a list of left subtrees, starting with the furthest
    down
-/
def lptree_to_tree_helper
  : ∀ {A}, (A -> A -> A) -> lptree A -> list (tree A)
| A f lptree.nil := []
| A f (lptree.cons mx t') := (match mx with
    | some x := list.cons (tree.leaf x)
    | none := λ zs, zs
    end)
      (list.map (untwice_tree f) (lptree_to_tree_helper (twice f) t'))

def lptree_to_tree_helper_option
  : ∀ {A}, (A -> A -> A) -> lptree A -> list (option (tree A))
| A f lptree.nil := []
| A f (lptree.cons mx t') := list.cons
   (option_map tree.leaf mx)
      (list.map (option_map (untwice_tree f)) (lptree_to_tree_helper_option (twice f) t'))

def asc_heights : ℕ → list ℕ → ℕ
| n [] := n
| n (x :: xs) := asc_heights(max x n + 1) xs

def max_tree_list_height {A : Type} (x : tree A) (xs : list (tree A)) : ℕ
  := asc_heights x.height (xs.map tree.height)

lemma list.map_compose {A B C : Type}
  (f : A -> B) (g : B -> C) (xs : list A)
  : list.map (g ∘ f) xs = list.map g (list.map f xs)
:=
begin
induction xs,
{ reflexivity },
{ simp [list.map] }
end

lemma tree_height_untwice_tree {A} (f : A → A → A) :
  (tree.height ∘ untwice_tree f) = (nat.succ ∘ tree.height)
:= begin
apply funext, intros x; dsimp [function.comp],
rw untwice_tree_height,
end

lemma nat.neg_le_le (x y : ℕ) (H : ¬ x ≤ y)
  : y ≤ x
:= begin
apply (if H' : y ≤ x then _ else _),
assumption, exfalso,
have H1 := @nat.le_total x y,
induction H1; contradiction,
end

lemma max_mono {x y x' y' : ℕ} (Hx : x ≤ x') (Hy : y ≤ y')
  : max x y ≤ max x' y'
:= begin
unfold max,
apply (if H : x ≤ y then _ else _),
{ rw (if_pos H),
  apply (if H' : x' ≤ y' then _ else _),
  rw (if_pos H'), assumption,
  rw (if_neg H'), apply le_trans, assumption,
  apply nat.neg_le_le, assumption,
},
{ rw (if_neg H),
  apply (if H' : x' ≤ y' then _ else _),
  rw (if_pos H'), apply le_trans; assumption,
  rw (if_neg H'), assumption,
}
end

lemma asc_heights_helper_mono {m n : ℕ} (H : m ≤ n)
  (xs : list ℕ)
  : asc_heights m xs ≤ asc_heights n xs
:= begin
revert m n,
induction xs; intros; dsimp [asc_heights], assumption,
apply ih_1, apply nat.add_le_add_right, apply max_mono,
apply nat.le_refl, assumption,
end

lemma asc_heights_succ (n : ℕ) (xs : list ℕ)
  : asc_heights n.succ (xs.map nat.succ) ≤ (asc_heights n xs).succ
:= begin
revert n;
induction xs; intros; dsimp [asc_heights],
{ constructor, },
{ repeat { rw ← nat.add_one },
  rw max_add, apply le_trans, apply ih_1,
  rw ← nat.add_one,
}
end

/-- Given a rightmost subtree, and a list of left subtrees
    starting from furthest toward the rightmost subtree and
    moving towards the root, assemble them into a single tree.
-/
def assemble_left_subtrees {A} (f : A -> A -> A)
  : tree A -> list (tree A) -> tree A
  | x [] := x
  | x (y :: ys) := assemble_left_subtrees (combine f y x) ys

/-- Convert a left-perfect tree to a binary tree with internal
    nodes, using the function `f` to produce internal nodes
    from the roots of the corresponding subtrees. Since lptrees
    may be empty, but trees may not, we return `none` exactly
    when the lptree is empty.
-/
def lptree_to_tree {A} (f : A -> A -> A)
  (t : lptree A) : option (tree A) :=
  match lptree_to_tree_helper f t with
  | [] := none
  | (x :: xs) := some (assemble_left_subtrees f x xs)
  end

def filter_some {A} : list (option A) → list A
| [] := []
| (mx :: xs) := (match mx with
  | none := λ l, l
  | some x := list.cons x
  end) (filter_some xs)

def assemble_left_subtrees_option {A} (f : A → A → A) : list (option (tree A)) → option (tree A)
| [] := none
| (none :: xs) := assemble_left_subtrees_option xs
| (some x :: xs) := some (assemble_left_subtrees f x (filter_some xs))

def lptree_to_tree_option {A} (f : A -> A -> A)
  (t : lptree A) : option (tree A) :=
  assemble_left_subtrees_option f (lptree_to_tree_helper_option f t)

inductive Issome {A} : option A -> Prop
  | MkIsSome : forall a : A, Issome (some a)

lemma lptree.nonzero_subtrees {A} (t : lptree A)
  (f : A -> A -> A)
  (H : lptree_to_tree_helper f t ≠ [])
  : Issome (lptree_to_tree f t)
  :=
begin
unfold lptree_to_tree,
revert H,
destruct (lptree_to_tree_helper f t); intros,
{ contradiction },
{ clear H, rw a_2, simp [lptree_to_tree._match_1], constructor }
end

lemma map_not_nil {A B} xs (f : A -> B)
  (H : xs ≠ []) : list.map f xs ≠ [] :=
begin
cases xs,
{ contradiction },
{ simp [list.map], }
end


lemma lptree.nonzero_tree {A} (t : lptree A)
  (f : A -> A -> A)
  (tnonzero : lptree.nonzero t)
  : Issome (lptree_to_tree f t) :=
begin
apply lptree.nonzero_subtrees,
induction tnonzero with A x t A ma t tnonzero IHtnonzero,
{ dsimp, simp [lptree_to_tree_helper], },
{ simp [lptree_to_tree_helper],
  cases ma; simp [lptree_to_tree_helper._match_1],
  { apply map_not_nil, apply IHtnonzero },
}
end

namespace tree
/-- Enumerate the leaves of a binary tree from right to left
-/
def leaves {A} : tree A -> list A
| (node x l r) := leaves r ++ leaves l
| (leaf x) := [x]

lemma leaves_combine {A} f
  (x y : tree A)
  : (combine f x y).leaves
  = y.leaves ++ x.leaves :=
begin
induction x,
  { simp [combine, leaves] },
  { reflexivity }
end
end tree

def tree_leaves_option {A} : option (tree A) -> list A
| none := []
| (some t) := t.leaves

def depair {A} : list (A × A) -> list A
| [] := []
| ((x, y) :: zs) := y :: x :: depair zs

/-- Enumerate the leaves of an lptree from right to left
    (i.e., going up towards larger left-perfect subtrees
-/
def lptree_leaves : ∀ {A}, lptree A -> list A
| A lptree.nil := []
| A (lptree.cons mx t) := (match mx with
  | none := λ zs, zs
  | (some x) := list.cons x
  end) (depair (lptree_leaves t))

/-- Given a tree specified by a list of its left subtrees and
    its rightmost subtree, enumerate its leaves from right to left
-/
def left_subtrees_leaves {A}
  (f : A -> A -> A)
  : list (tree A) -> tree A -> list A
| [] x := x.leaves
| (y :: ys) x := left_subtrees_leaves ys (combine f y x)

/-- Enumerate the leaves of a tree specified by a list of
    left subtrees (with an empty rightmost subtree)
    in reverse order
-/
def left_subtrees_leaves' {A}
  : list (tree A) -> list A
| [] := []
| (t :: ts) := t.leaves ++ left_subtrees_leaves' ts


lemma left_subtrees_leaves_same {A}
  (f : A -> A -> A) (ts : list (tree A))
  : ∀ t : tree A,
    left_subtrees_leaves f ts t = t.leaves ++ left_subtrees_leaves' ts
  :=
begin
induction ts; intros,
  { simp [left_subtrees_leaves],
    simp [left_subtrees_leaves']
  },
  { simp [left_subtrees_leaves'],
    simp [left_subtrees_leaves],
    rw ih_1,
    rw tree.leaves_combine,
    rw list.append_assoc
   }
end

lemma list_to_lptree.nonzero {A} (xs : list A)
  (H : xs ≠ []) : lptree.nonzero (list_to_lptree xs) :=
begin
cases xs,
{ contradiction },
{ simp [list_to_lptree], apply insert_nonzero }
end

def merge_to_tree {A} (f : A -> A -> A)
  (xs : list A) : option (tree A)
  := lptree_to_tree f (list_to_lptree xs)

lemma list_to_tree_Some {A} (xs : list A)
  f (H : xs ≠ [])
  : Issome (merge_to_tree f xs)
  :=
begin
  apply lptree.nonzero_tree,
  apply list_to_lptree.nonzero,
  assumption
end

lemma not_Issome_none {A : Type} : ¬ Issome (@none A) :=
begin
generalize b : (@none A) = a,
intros contra,
induction contra,
contradiction
end

def tree_mem {A} (t : tree A) : tree A -> Prop
| (tree.node i l r) := t = tree.node i l r ∨ tree_mem l ∨ tree_mem r
| (tree.leaf i) := t = tree.leaf i

lemma list_map_nil {A B : Type} (f : A -> B)
  (xs : list A)
  (H : xs = [])
  : list.map f xs = []
  :=
begin
rw H, reflexivity
end

lemma lptree_to_tree_helper_nonempty_nonzero {A}
  (f : A -> A -> A)
  (t : lptree A)
  (H : lptree_to_tree_helper f t ≠ [])
  : lptree.nonzero t :=
begin
induction t,
  { contradiction },
  { cases a,
    { simp [lptree_to_tree_helper] at H, constructor,
     apply ih_1, intros contra, apply H,
     apply list_map_nil, apply contra },
    { constructor }
  }
end

lemma assemble_left_subtrees_height {A : Type}
  (f : A → A → A) (x : tree A) (xs : list (tree A))
  : (assemble_left_subtrees f x xs).height = max_tree_list_height x xs
:= begin
revert x,
unfold max_tree_list_height,
induction xs; intros;
  dsimp [tree.height, assemble_left_subtrees, asc_heights],
{ reflexivity },
{ rw ih_1, rw combine_height, }
end

lemma asc_heights_lemma1 (xs : list ℕ) (n : ℕ)
  : asc_heights n (list.map nat.succ xs)
  ≤ asc_heights n xs + 1
:= begin
apply le_trans, tactic.swap,
apply asc_heights_succ,
apply asc_heights_helper_mono,
constructor, constructor,
end

def opt_default {A} (default : A) : option A → A
| (some x) := x
| none := default

lemma asc_heights_filter_some1 {A} (n : ℕ) (xs : list (option (tree A))) :
 asc_heights n (list.map tree.height (filter_some xs)) ≤
    asc_heights n
      (list.map (opt_default 0 ∘ option_map tree.height) xs)
:= begin
revert n,
induction xs; intros; dsimp [asc_heights, list.map, filter_some],
{ apply le_refl },
{ induction a; dsimp [filter_some],
  { apply le_trans, apply ih_1,
    apply asc_heights_helper_mono,
    apply le_trans, tactic.swap, apply le_add_r,
    apply le_max_right, },
  { dsimp [asc_heights], apply le_trans,
    apply ih_1,
    apply asc_heights_helper_mono,
    apply nat.add_le_add_right,
    apply max_mono,
    { apply le_refl },
    { apply le_refl }
  }
}
end

lemma asc_heights_filter_some {A} (n : ℕ) (xs : list (option (tree A))) :
 asc_heights n (list.map tree.height (filter_some xs)) ≤
    asc_heights (n + 1)
      (list.map (opt_default 0 ∘ option_map tree.height) xs)
:= begin
apply le_trans, apply asc_heights_filter_some1,
apply asc_heights_helper_mono, constructor, constructor,
end

lemma max_0_r (x : ℕ) : max x 0 = x
:= begin
unfold max,
apply (if H : x ≤ 0 then _ else _),
rw (if_pos H), symmetry, rw ← nat.le_zero_iff,
assumption, rw if_neg, assumption,
end

lemma assemble_left_subtrees_option_height {A : Type}
  (f : A → A → A) (xs : list (option (tree A)))
  : (match assemble_left_subtrees_option f xs with
    | none := true
    | some t := t.height ≤ asc_heights 0 (list.map (opt_default 0 ∘ option_map tree.height) xs)
    end : Prop)
:= begin
destruct (assemble_left_subtrees_option f xs),
{ intros Hnone, rw Hnone, dsimp, constructor, },
{ intros t Ht, rw Ht, dsimp,
  revert t, induction xs; intros; dsimp [list.map, asc_heights],
  { dsimp [assemble_left_subtrees_option] at Ht, contradiction, },
  { induction a,
    { dsimp [assemble_left_subtrees_option] at Ht,
      specialize (ih_1 _ Ht), apply le_trans, assumption,
      apply asc_heights_helper_mono, apply nat.zero_le,
      },
    { dsimp [assemble_left_subtrees_option] at Ht,
      injection Ht with Ht', clear Ht,
      subst t,
      rw assemble_left_subtrees_height,
      clear ih_1,
      unfold max_tree_list_height,
      apply le_trans, apply asc_heights_filter_some,
      apply asc_heights_helper_mono,
      dsimp [option_map, opt_default, option_bind, function.comp],
      rw max_0_r,
    }
  }
}
end

lemma asc_heights_list_mono_lemma (n : ℕ) (xs : list (option ℕ)) :
  asc_heights n (xs.map (opt_default 0 ∘ option_map nat.succ))
≤ asc_heights n (xs.map (nat.succ ∘ opt_default 0))
:= begin
revert n,
induction xs; intros; dsimp [list.map, asc_heights],
{ apply nat.le_refl,  },
{ apply le_trans, apply ih_1,
  apply asc_heights_helper_mono,
  apply nat.add_le_add_right,
  apply max_mono,
  { dsimp [function.comp], induction a;
      dsimp [option_map, option_bind, opt_default],
    apply nat.zero_le, apply nat.le_refl },
  { apply le_refl }
}
end

lemma asc_heights_succ_option (n : ℕ) (xs : list (option ℕ))
  : asc_heights n.succ (xs.map (opt_default 0 ∘ option_map nat.succ))
  ≤ (asc_heights n (xs.map (opt_default 0))).succ
:= begin
revert n;
induction xs; intros; dsimp [asc_heights],
{ constructor, },
{ repeat { rw nat.add_one },
  apply le_trans, apply ih_1,
  apply nat.succ_le_succ, apply asc_heights_helper_mono,
  repeat { rw ← nat.add_one }, rw ← max_add,
  apply max_mono,
  { induction a; dsimp [opt_default, function.comp, option_map, option_bind],
    apply nat.zero_le, apply le_refl,
  },
  { apply le_refl }
}
end

lemma option_map_compose {A B C} (f : A → B) (g : B → C)
  : option_map (g ∘ f) = option_map g ∘ option_map f
:= begin
apply funext; intros x, induction x; reflexivity,
end

lemma stupid_lemma {A} (a : A)
  : ((opt_default 0 ∘ option_map tree.height) ((some ∘ tree.leaf) a))
  = 0 := rfl

lemma asc_heights_lemma {A : Type}
  (f : A → A → A) (t : lptree A)
  : asc_heights 0 (list.map (opt_default 0 ∘ option_map tree.height) (lptree_to_tree_helper_option f t))
  ≤ lptree.height t
:= begin
induction t; dsimp [lptree_to_tree_helper_option, lptree.height, asc_heights],
{ apply nat.zero_le, },
{ rw ← list.map_compose,
  rw function.comp.assoc
    (opt_default 0) (option_map tree.height) (option_map (untwice_tree f)),
  rw ← option_map_compose,
  rw tree_height_untwice_tree,
  rw option_map_compose (tree.height) (nat.succ),
  rw ← function.comp.assoc
    (opt_default 0) (option_map nat.succ) (option_map tree.height),
  rw list.map_compose,
  apply le_trans, apply asc_heights_list_mono_lemma,
  rw ← list.map_compose,
  rw function.comp.assoc
    (nat.succ) (opt_default 0) (option_map tree.height),
  rw list.map_compose,
  repeat { rw nat.add_one },
  apply le_trans,
  apply asc_heights_succ,
  apply nat.succ_le_succ,
  induction a; dsimp [option_map, option_bind
  , lptree_to_tree_helper_option, lptree.height
  , asc_heights],
  {
    apply ih_1,
  },
  { rw stupid_lemma,
    dsimp [max], rw (if_pos (le_refl 0)),
    apply ih_1,
  }
}
end

lemma lptree_to_tree_option_height
  {A : Type}
  (f : A → A → A) (lpt : lptree A)
  : (match lptree_to_tree_option f lpt with
    | none := true
    | some t := t.height ≤ lpt.height
    end : Prop)
:= begin
destruct (lptree_to_tree_option f lpt),
{ intros Hnone, rw Hnone, dsimp, constructor },
{ intros t Ht, rw Ht, dsimp,
  unfold lptree_to_tree_option at Ht,
  have H := assemble_left_subtrees_option_height
    f (lptree_to_tree_helper_option f lpt),
  rw Ht at H, dsimp at H,
  apply le_trans, assumption,
  apply asc_heights_lemma,
}
end

lemma map_filter_some {A B} (f : A → B) (xs : list (option A))
  : filter_some (list.map (option_map f) xs)
  = list.map f (filter_some xs)
:= begin
induction xs; dsimp [list.map, option_map, option_bind, filter_some],
{ reflexivity },
{ induction a; dsimp [option_map, option_bind, function.comp, filter_some],
  { assumption },
  { rw ih_1 }
}
end

lemma lptree_to_tree_helper_option_equiv
  {A : Type}
  (f : A → A → A) (lpt : lptree A)
  : lptree_to_tree_helper f lpt
  = filter_some (lptree_to_tree_helper_option f lpt)
:= begin
induction lpt;
  dsimp [lptree_to_tree_helper, lptree_to_tree_helper_option, filter_some],
{ reflexivity },
{ induction a;
    dsimp [option_map, option_bind, lptree_to_tree_helper, lptree_to_tree_helper_option, filter_some],
    { rw map_filter_some, f_equal,
    apply ih_1, },
    { f_equal, rw map_filter_some, f_equal, apply ih_1 }
 }
end

lemma assemble_left_subtrees_option_filter_some
  {A : Type} (f : A → A → A)
  (xs : list (option (tree A)))
  : assemble_left_subtrees_option f xs = match filter_some xs with
  | [] := none
  | (y :: ys) := some (assemble_left_subtrees f y ys)
  end
:= begin
induction xs; dsimp [filter_some, assemble_left_subtrees_option],
{ reflexivity },
{ rename a x, induction x; dsimp [filter_some, assemble_left_subtrees_option],
  { rw ih_1, },
  { reflexivity }
}
end

lemma lptree_to_tree_option_equiv
  {A : Type}
  (f : A → A → A) (lpt : lptree A)
  : lptree_to_tree_option f lpt = lptree_to_tree f lpt
:= begin
unfold lptree_to_tree_option lptree_to_tree,
rw assemble_left_subtrees_option_filter_some,
destruct (lptree_to_tree_helper f lpt),
{ intros Hnone, rw Hnone, dsimp [lptree_to_tree],
  rw lptree_to_tree_helper_option_equiv at Hnone,
  rw Hnone,
},
{ intros t ts Hts, rw Hts, dsimp [lptree_to_tree],
  rw lptree_to_tree_helper_option_equiv at Hts,
  rw Hts,
}
end

/-- Decision procedure to determine whether
    an lptree is nonempty
-/
def lptree.nonzero_bool
  : ∀ {A : Type}, lptree A -> bool
| _ lptree.nil := false
| _ (lptree.cons (some x) t) := true
| _ (lptree.cons none t) := lptree.nonzero_bool t

def lptree.nonzero_bool_equiv {A : Type}
  (t : lptree A)
  : lptree.nonzero_bool t = true ↔ lptree.nonzero t
:=
begin
split; intro H,
{ induction t,
  { contradiction },
  { cases a, simp [lptree.nonzero_bool] at H,
    { constructor,
      apply ih_1, assumption },
    { constructor }
  }
},
{ induction H,
  { simp [lptree.nonzero_bool] },
  { cases ma,
    { simp [lptree.nonzero_bool], assumption },
    { reflexivity }
  }
}
end

def lptree.nonzero_dec {A : Type}
  (t : lptree A)
  : decidable (lptree.nonzero t)
:=
begin
rw <- lptree.nonzero_bool_equiv,
apply bool.decidable_eq
end

lemma lptree_to_tree_some_nonzero {A}
  (f : A -> A -> A)
  (t : lptree A) :
  ∀ (x : tree A) (H : lptree_to_tree f t = some x), lptree.nonzero t :=
begin
intros, apply (lptree_to_tree_helper_nonempty_nonzero f),
unfold lptree_to_tree at H,
intros contra,
rw contra at H,
simp [lptree_to_tree._match_1] at H,
contradiction
end

/-- This inductive predicate holds of a binary tree
    if all of its internal nodes can be compute by applying
    `f` to the roots of its left and right subtrees
-/
inductive internal_nodes_ok {A} (f : A -> A -> A) : tree A -> Prop
| leaf : forall  x : A, internal_nodes_ok (tree.leaf x)
| node : forall x l r, internal_nodes_ok l -> internal_nodes_ok r
      -> x = f (root l) (root r) -> internal_nodes_ok (tree.node x l r)

lemma internal_nodes_ok_combine {A} (f : A -> A -> A)
  (x y : tree A)
  (Hx : internal_nodes_ok f x)
  (Hy : internal_nodes_ok f y)
  : internal_nodes_ok f (combine f x y) :=
begin
unfold combine,
constructor, assumption, assumption, reflexivity
end

lemma assemble_left_subtrees_preserves_nodes
 {A} (f : A -> A -> A) (xs : list (tree A))
 (Hxs : list.Forall (internal_nodes_ok f) xs)
 : ∀ (x : tree A) (Hx : internal_nodes_ok f x),
   internal_nodes_ok f (assemble_left_subtrees f x xs)
 :=
 begin
 induction Hxs; intros,
 { simp [assemble_left_subtrees], assumption },
 { simp [assemble_left_subtrees],
   apply ih_1, apply internal_nodes_ok_combine,
   assumption, assumption }
 end

lemma assemble_left_subtrees_preserves_leaves
  {A} (f : A -> A -> A) (xs : list (tree A))
  : ∀ (x : tree A),
   (assemble_left_subtrees f x xs).leaves
   = left_subtrees_leaves f xs x :=
begin
induction xs; intros,
{ reflexivity },
{ simp [assemble_left_subtrees],
  rw ih_1,
  reflexivity
}
end

lemma congr_arg2_pair {A B C} (f : A -> B -> C)
  (a a' : A) (b b' : B)
  : (a, b) = (a', b') -> f a b = f a' b'
  :=
begin
intros H, injection H,
subst a,
subst b
end

lemma root_untwice_tree {A} (f : A -> A -> A) (t : tree (A × A))
  : forall (x y : A) (Hroot : root t = (x, y))
  , f x y = root (untwice_tree f t) :=
begin
induction t; intros,
{ simp [root] at Hroot,
  rw Hroot,
  simp [untwice_tree],
  reflexivity,
},
{ simp [root] at Hroot,
  rw Hroot,
  simp [untwice_tree],
  reflexivity
}
end

lemma root_untwice_tree' {A} (f : A -> A -> A) (l r : tree (A × A))
  : twice f (root l) (root r)
  = (root (untwice_tree f l), root (untwice_tree f r))
  :=
begin
  generalize Ql : (root l) = Pl,
  cases Pl,
  generalize Qr : (root r) = Pr,
  cases Pr,
  simp [twice],
  apply and.intro,
  all_goals { apply root_untwice_tree, assumption, },
end

lemma internal_nodes_ok_twice {A}
  (f : A -> A -> A) (x : tree (A × A))
  (H : internal_nodes_ok (twice f) x)
  : internal_nodes_ok f (untwice_tree f x)
:=
begin
induction x,
{ cases item, simp [untwice_tree],
    constructor, constructor, constructor, reflexivity
},
{ cases item, simp [untwice_tree], constructor,
  { apply ih_1, clear ih_1 ih_2,
    generalize Q : (tree.node (fst, snd) l r) = P,
    rw Q at H, revert fst snd l r Q,
    induction H; intros,
    { contradiction },
    { injection Q, subst l_1, assumption }
  },
  { apply ih_2, clear ih_1 ih_2,
    generalize Q : (tree.node (fst, snd) l r) = P,
    rw Q at H, revert fst snd l r Q,
    induction H; intros,
    { contradiction },
    { injection Q, subst r_1, assumption }
  },
  { clear ih_1 ih_2,
    generalize Q : (tree.node (fst, snd) l r) = P,
    rw Q at H, revert fst snd l r Q,
    induction H; intros,
    { contradiction },
    { subst x, injection Q, subst l_1, subst r_1,
      clear Q, generalize Y : (root l) = X,
      apply congr_arg2_pair, rw h,
      apply root_untwice_tree' }
  },
}
end



lemma internal_nodes_ok_lptree_to_tree_helper
  {A} (f : A -> A -> A) (t : lptree A)
  : list.Forall (internal_nodes_ok f)
    (lptree_to_tree_helper f t) :=
begin
induction t,
{ simp [lptree_to_tree_helper],
  constructor },
{ simp [lptree_to_tree_helper],
  cases a,
  { simp [lptree_to_tree_helper._match_1],
    specialize (ih_1 (twice f)),
    apply list.map_Forall,
    apply list.impl_Forall,
        { assumption },
        { intros, apply internal_nodes_ok_twice, apply a }
  },
  { simp [lptree_to_tree_helper._match_1],
    constructor,
      { constructor },
      { apply list.map_Forall,
        apply list.impl_Forall,
        { apply ih_1 },
        { intros, apply internal_nodes_ok_twice, assumption }
      }
  }
}
end

/-- If we convert an lptree to a tree, producing internal
    nodes with f, indeed all the internal nodes are the
    result of applying f to the roots of their subtrees.
-/
theorem lptree_nodes_spec {A} (t : lptree A)
  (f : A -> A -> A)
  : (match lptree_to_tree f t with
  | (some t') := internal_nodes_ok f t'
  | none := true
  end : Prop)
:=
begin
generalize Q : (lptree_to_tree f t) = P,
cases P,
{ dsimp, constructor },
{ dsimp,
  generalize W : (lptree_to_tree_helper f t) = Z,
  cases Z,
  { unfold lptree_to_tree at Q,
    rewrite W at Q,
    simp [lptree_to_tree._match_1] at Q,
    contradiction },
  { unfold lptree_to_tree at Q,
    rewrite W at Q,
    simp [lptree_to_tree._match_1] at Q,
    injection Q with Q', clear Q, subst a,
    have H := internal_nodes_ok_lptree_to_tree_helper f t,
    rw W at H,
    clear W,
    apply_in H list.Forall_invert,
    dsimp at H,
    induction H,
    apply assemble_left_subtrees_preserves_nodes;
    assumption
    }
}
end

lemma lptree_leaves_cons {A} (t : lptree A)
  (x : A)
  : lptree_leaves (t.insert x) =
     x :: lptree_leaves t
  :=
begin
induction t,
{ reflexivity },
{ cases a,
  { simp [lptree.insert, lptree_to_tree, lptree_to_tree_helper],
    simp [lptree_leaves]},
  { simp [lptree.insert],
    simp [lptree_leaves],
    rw ih_1,
    simp [depair]
   }
}
end

/-- If we produce an lptree from a list of elements,
    then enumerate the leaves, we get the same list back
-/
lemma lptree_leaves_list {A} (xs : list A)
  : lptree_leaves (list_to_lptree xs) = xs
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

lemma depair_app {A} (xs ys : list (A × A))
  : depair (xs ++ ys) = depair xs ++ depair ys
:=
begin
induction xs,
{ reflexivity },
{ cases a,
  simp [depair],
  rw ih_1 }
end


lemma depair_tree_leaves {A} (f : A -> A -> A)
  (t : tree (A × A))
  : depair t.leaves = (untwice_tree f t).leaves
:=
begin
induction t,
{ cases item, simp [tree.leaves, untwice_tree],
  simp [depair]
},
{ simp [tree.leaves],
  rw depair_app,
  rw [ih_1, ih_2],
  cases item with i1 i2,
  simp [untwice_tree],
  simp [tree.leaves] }
end


lemma depair_leaves {A} (f : A -> A -> A)
  (xs : list (tree (A × A)))
: depair (left_subtrees_leaves' xs) =
    left_subtrees_leaves' (list.map (untwice_tree f) xs)
:=
begin
induction xs,
{ reflexivity },
{ simp [left_subtrees_leaves'],
  rw depair_app,
  f_equal,
  apply depair_tree_leaves,
  assumption }
end

lemma lptree_leaves_helper_same' {A} f (t : lptree A)
 : lptree_leaves t
 = left_subtrees_leaves' (lptree_to_tree_helper f t) :=
begin
induction t,
{ reflexivity },
{ simp [lptree_leaves],
  simp [lptree_to_tree_helper],
  cases a,
  { simp [lptree_leaves],
    simp [lptree_to_tree_helper],
    rw (ih_1 (twice f)),
    rw depair_leaves,
   },
  { simp [lptree_leaves],
    simp [lptree_to_tree_helper],
    simp [left_subtrees_leaves'],
    simp only [tree.leaves],
    f_equal,
    rw (ih_1 (twice f)),
    apply depair_leaves },
}
end

lemma lptree_leaves_helper_same {A} f (t : lptree A)
 : lptree_leaves t
 = match lptree_to_tree_helper f t with
   | [] := []
   | x :: xs := left_subtrees_leaves f xs x
   end :=
begin
simp,
rw (lptree_leaves_helper_same' f),
generalize : (lptree_to_tree_helper f t) = xs,
intros,
cases xs,
{ reflexivity },
{ dsimp,
  symmetry,
  apply left_subtrees_leaves_same }
end

lemma lptree_not_nonzero_no_leaves {A : Type}
  (t : lptree A)
  (H : ¬ lptree.nonzero t)
  : lptree_leaves t = []
:= begin
rw <- lptree.nonzero_bool_equiv at H,
induction t,
{ reflexivity },
{ cases a,
  { simp [lptree_leaves],
    apply depair_nil, apply ih_1,
    simp [lptree.nonzero_bool] at H,
    assumption
     },
  { simp [lptree.nonzero_bool] at H,
    contradiction }
}
end

/-- If we compute the leaves of an lptree, it is the same
    as if we convert it to a binary tree and then compute
    the leaves
-/
lemma tree_lptree_leaves {A} f (t : lptree A)
  : lptree_leaves t = tree_leaves_option (lptree_to_tree f t)
  :=
begin
generalize P : (lptree_to_tree f t) = Q,
cases Q,
{ simp [tree_leaves_option],

  cases (lptree.nonzero_dec t),
  apply lptree_not_nonzero_no_leaves,
  assumption,
  cases t,
  reflexivity,
  exfalso,
  have H' := lptree.nonzero_tree _ f a,
  rw P at H',
  apply (@not_Issome_none (tree A)),
  assumption
},
{ simp [tree_leaves_option],
  generalize W : (lptree_to_tree_helper f t) = Z,
  cases Z,
  { unfold lptree_to_tree at P,
    rewrite W at P,
    simp [lptree_to_tree._match_1] at P,
    contradiction },
  { unfold lptree_to_tree at P,
    rewrite W at P,
    simp [lptree_to_tree._match_1] at P,
    injection P, clear P,
    subst a,
    rw assemble_left_subtrees_preserves_leaves,
    rw (lptree_leaves_helper_same f),
    simp, rw W }
}
end

/-- If we take a list, convert it to an lptree, convert
    that to a binary tree, and compute the leaves,
    we get back the original list
-/
lemma lptree_leaves_ok {A} (f : A -> A -> A) (xs : list A)
  : xs = tree_leaves_option (merge_to_tree f xs) :=
begin
transitivity,
rw <-(lptree_leaves_list xs),
unfold merge_to_tree,
rw (tree_lptree_leaves f)
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

section paths

parameter A : Type
/-- We use lr to denote a direction a path follows from the root-/
inductive lr : Type
| left
| right

/-- A path through a tree is a left or right direction, and the siblings that
    weren't visited-/
@[reducible]
def path := list (lr × A)


parameter {link : Type}
parameter mk_link : lr → A → A → link

def all_paths_core : tree A -> list link -> list (list link)
| (tree.node i l r) path :=
                 all_paths_core r ((mk_link lr.left (root l) (root r)) ::path)
              ++ all_paths_core l ((mk_link lr.right (root l) (root r)) ::path)
| (tree.leaf i) path := [path]

/-- get all paths (in order left to right) from root to leaf
    these paths start with leafs, and are meant to be followed
    up the tree in order to reconstruct a root in log(n) operations
 -/
def all_paths (tr : tree A): list (list link) :=
              all_paths_core tr []

def second {X A B : Type} (f : A -> B) : X × A -> X × B
| (x, y) := (x, f y)

def all_paths' : tree A -> list (list link)
| (tree.leaf i) := [[]]
| (tree.node i l r) :=
     list.map (λ p, p ++ [mk_link lr.left (root l) (root r)]) (all_paths' r)
  ++ list.map (λ p, p ++ [mk_link lr.right (root l) (root r)]) (all_paths' l)

/-- Get all paths, but this time the paths give the direction
    to follow from the root to the leaf. Finally, we also return the
    leaf element that the path leads to.
-/

def all_paths_rev : tree A -> list (list link)
| (tree.leaf i) := [[]]
| (tree.node i l r) :=
     list.map (list.cons (mk_link lr.left (root l) (root r))) (all_paths_rev r)
  ++ list.map (list.cons (mk_link lr.right (root l) (root r))) (all_paths_rev l)

lemma all_paths_rev_height (t : tree A)
  : list.Forall (λ ls : list link, ls.length ≤ t.height) (all_paths_rev t)
:= begin
induction t; dsimp [all_paths_rev, tree.height],
{ constructor, apply le_refl, constructor },
{ apply list.concat_Forall; apply list.map_Forall;
  apply list.impl_Forall; try { assumption },
  { intros x H,
    dsimp [list.length], apply nat.add_le_add_right,
    apply le_trans, assumption, apply le_max_right,
  },
  { intros x H,
    dsimp [list.length], apply nat.add_le_add_right,
    apply le_trans, assumption, apply le_max_left, }
}
end

def all_paths_rev_option : option (tree A) → list (list link)
| none := []
| (some t) := all_paths_rev t

theorem end_to_end_height (xs : list A)
  (f : A → A → A)
  (n : ℕ)
  (Hlen : log2 (xs.length + 1) ≤ n)
  : list.Forall (λ ls : list link, ls.length ≤ n) $
      all_paths_rev_option (lptree_to_tree f (list_to_lptree xs))
:= begin
destruct (lptree_to_tree f (list_to_lptree xs)),
{ intros Hnone, rw Hnone, constructor, },
{ intros t Ht, rw Ht, dsimp [all_paths_rev_option],
  apply list.impl_Forall, apply all_paths_rev_height,
  intros, apply le_trans, assumption,
  clear a x,
  rw ← lptree_to_tree_option_equiv at Ht,
  have H2 := lptree_to_tree_option_height f (list_to_lptree xs),
  rw Ht at H2, dsimp at H2,
  apply le_trans, apply H2, clear H2,
  rw list_to_tree_height' xs,
  apply Hlen,
 }
end

lemma all_paths_core_app (t : tree A) (p p' : list link)
  : all_paths_core t (p ++ p') =
    list.map (λ z, z ++ p') (all_paths_core t p)
:= begin
revert p p',
induction t; intros,
{ reflexivity },
{ dsimp [all_paths_core],
  repeat { rw ← list.cons_append },
  rw [ih_1, ih_2],
  rw list.map_append,
}
end

lemma all_paths_same_core (t : tree A) (p : list link)
  : all_paths_core t p = list.map (λ z, z ++ p) (all_paths' t)
:=
begin
revert p,
induction t; intros,
{ reflexivity },
{ simp [all_paths_core, all_paths'],
  f_equal,
  { rw ih_2,
    f_equal, apply funext,
    intros x,
    dsimp [function.comp],
    rw list.append_assoc,
    reflexivity, },
  { rw ih_1,
    f_equal, apply funext,
    intros x,
    dsimp [function.comp],
    rw list.append_assoc,
    reflexivity, }
}
end

lemma all_paths_same (t : tree A)
  : all_paths t = all_paths' t
:= begin
unfold all_paths,
rw all_paths_same_core,
apply list.map_id',
intros x, simp,
end

/-- Indeed, `all_paths` and `all_paths` are the same, except one
    gives paths in the reverse order compared to the other
-/
lemma all_paths_reverse (t : tree A)
  : list.map (list.reverse) (all_paths_rev t) = all_paths' t
:=
begin
induction t,
{ reflexivity },
{ simp [all_paths_rev, all_paths'],
  f_equal,
  { rw <- ih_2,
    rw <- list.map_compose,
    f_equal, apply funext,
    intros x,
    simp [function.comp], },
  { rw <- ih_1,
    rw <- list.map_compose,
    f_equal, apply funext,
    intros x,
    simp [function.comp]  }
}
end

protected def right_core : tree A -> path -> path
| (tree.node i l r) path :=
                  right_core r ((lr.right, root l) ::path)
| (tree.leaf i) path := path

/-- get only the rightmost path of a tree (all directions will be lr.right) -/
def right_path (tr : tree A) : path :=
              right_core tr []


/-- given a path (in reverse order from the paths obtained by right_path and all_paths!!)
    follow that path from the root and return the tree at that point-/
def tree_at_path : tree A -> path -> option (tree A)
| t [] := some t
| (tree.node i l r) (h :: t) := match h with
                                | (lr.left, _) := tree_at_path l t
                                | (lr.right, _) := tree_at_path r t
                                end
| (tree.leaf _) _ := none

parameter (compute_parent : link → A → A)

def reconstruct_root (xs : list link) (x : A) : A
  := xs.foldr compute_parent x

def reconstruct_items_rev : list link → A → list A
| [] lf := []
| (x :: xs) lf := reconstruct_root (x :: xs) lf :: reconstruct_items_rev xs lf

/-- Rebuilds all of the items in a path given the combination function, a
    path, and an initial value, path moves towards the root-/
def reconstruct_items (node_combine : A -> A -> A) : path → A → list A
| [] _ := []
| ((lr.left, i) :: t) last_item := let new_item := node_combine last_item i in
                                    new_item :: (reconstruct_items t new_item)
| ((lr.right, i) :: t) last_item := let new_item := node_combine i last_item in
                                    new_item :: (reconstruct_items t new_item)

/-- Given
    a prospective leaf item `lf`,
    a path `p` that is supposed to lead to that leaf item,
    and a tree `t`, this predicate indicates that indeed
    following the path `p` along the tree `t` leads to the leaf `lf`.
-/
inductive path_in_tree_rev : A -> list A -> tree A -> Prop
| leaf : ∀ lf : A, path_in_tree_rev lf [] (tree.leaf lf)
| left : ∀ lf x xs l r,
         path_in_tree_rev lf xs l -> path_in_tree_rev lf (x :: xs) (tree.node x l r)
| right : ∀ lf x xs l r,
         path_in_tree_rev lf xs r -> path_in_tree_rev lf (x :: xs) (tree.node x l r)


lemma second_simpl {X A B : Type} (f : A -> B)
  (x : X) (y : A)
  : second f (x, y) = (x, f y)
  := rfl

parameter combine_data : A → A → A
def compute_parent_correct := forall (left right : A) dir,
  compute_parent (mk_link dir left right) (match dir with
                  | lr.left := right
                  | lr.right := left end)
    = combine_data left right

lemma tree_leaves_all_paths_rev_len (x : tree A)
  : x.leaves.length = (all_paths_rev x).length
:= begin
induction x; dsimp [tree.leaves, all_paths_rev, list.length],
{ reflexivity },
{ repeat { rw list.length_append },
  repeat { rw list.length_map },
  f_equal; assumption,
}
end


lemma list.zip_same_length {X Y}
  (xs ys : list X) (xs' ys' : list Y) (H : xs.length = xs'.length)
  : list.zip (xs ++ ys) (xs' ++ ys')
  = list.zip xs xs' ++ list.zip ys ys'
:= begin
revert H xs' xs,
apply list.pair_induction_same_length,
reflexivity, intros, dsimp [list.zip, list.zip_with],
f_equal, assumption
end

lemma list.zip_map_r {X Y Z} (xs : list X) (ys : list Y)
  (f : Y → Z)
  : list.zip xs (list.map f ys) =
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

lemma tree_leaves_all_paths_rev {X : Type u} (l r : tree A) (f g : list link → X) :
  (list.zip (r.leaves ++ l.leaves)
       (list.map f (all_paths_rev r) ++ list.map g (all_paths_rev l)))
  =
  list.zip r.leaves (list.map f (all_paths_rev r))
  ++ list.zip l.leaves (list.map g (all_paths_rev l))
:= begin
apply list.zip_same_length, rw list.length_map,
apply tree_leaves_all_paths_rev_len,
end


/-- If we compute the list of paths to all leaves in a tree
    where the internal nodes are all the result of applying
    and then use those paths and the leaves they point to
    to try to

-/
lemma reconstruct_root_correct
  (t : tree A)
  (H : internal_nodes_ok combine_data t)
  (comp_par_corr : compute_parent_correct)
  : list.Forall (λ p : A × list link,
    reconstruct_root p.snd p.fst = root t) (list.zip t.leaves (all_paths_rev t))
:= begin
induction H,
{ simp [all_paths_rev], constructor,
  { dsimp, simp [reconstruct_root], reflexivity },
  { constructor }
},
{ dsimp [all_paths_rev, tree.leaves],
  rw tree_leaves_all_paths_rev,
  apply list.concat_Forall,
  { clear ih_1, rw list.zip_map_r, apply list.map_Forall,
    apply list.impl_Forall, apply ih_2,
    clear ih_2 a a_1,
    simp [root],
    intros lf p,
    subst x,
    intros H,
    dsimp [second],
    dsimp [reconstruct_root],
    have H' := comp_par_corr (root l) (root r) lr.left,
    simp [compute_parent_correct] at H',
    dsimp [reconstruct_root] at H,
    rw H, apply H', },
  { clear ih_2, rw list.zip_map_r, apply list.map_Forall,
    apply list.impl_Forall, apply ih_1,
    clear ih_1 a a_1,
    simp [root],
    intros lf p,
    subst x,
    intros H,
    simp [second],
    simp [reconstruct_root],
    have H' := comp_par_corr (root l) (root r) lr.right,
    simp [compute_parent_correct] at H',
    dsimp [reconstruct_root] at H,
    rw H, apply H', }
}
end

lemma list.map_fst_second {X A B : Type}
  (xs : list (X × A)) (f : A -> B)
  : list.map (prod.fst ∘ second f) xs
  = list.map prod.fst xs
:= begin
induction xs,
{ reflexivity },
{ simp [list.map],
  cases a with i1 i2,
  simp [second],
  rw ih_1, reflexivity
}
end

lemma reconstruct_items_correct
  (comp_par_corr : compute_parent_correct)
  (t : tree A)
  : internal_nodes_ok combine_data t
  -> list.Forall (λ p : A × list link, let (lf, pth) := p in
      path_in_tree_rev lf (reconstruct_items_rev pth lf) t)
        (list.zip t.leaves (all_paths_rev t))
:= begin
intros H, induction H,
{ dsimp [all_paths_rev],
  constructor, dsimp, constructor, constructor },
{ dsimp at ih_1 ih_2,
  dsimp, dsimp [all_paths_rev, tree.leaves],
  rw tree_leaves_all_paths_rev,
  apply list.concat_Forall,
  { rw list.zip_map_r, apply list.map_Forall,
    apply_in a_1 (reconstruct_root_correct),
    apply comp_par_corr,
    apply list.impl_Forall2, apply a_1, apply ih_2,
    intros p H H', induction p with lf pth,
    dsimp at H H', dsimp [second],
    dsimp [reconstruct_items_rev],
    dsimp [reconstruct_root],
    dsimp [reconstruct_root] at H, rw H,
    have H2 := comp_par_corr (root l) (root r) lr.left,
    dsimp [compute_parent_correct] at H2,
    rw H2,
    rw ← a_2, apply path_in_tree_rev.right, assumption,
  },
  { rw list.zip_map_r, apply list.map_Forall,
    apply_in a reconstruct_root_correct,
    apply comp_par_corr,
    apply list.impl_Forall2, apply a, apply ih_1,
    intros p H H', induction p with lf pth,
    dsimp at H H', dsimp [second],
    simp [reconstruct_items_rev],
    simp [reconstruct_root],
    dsimp [reconstruct_root] at H, rw H,
    have H2 := comp_par_corr (root l) (root r) lr.right,
    dsimp [compute_parent_correct] at H2,
    rw H2,
    rw ← a_2, apply path_in_tree_rev.left, assumption, }
}
end

end paths

--#eval (lptree_to_tree nat.add (list_to_lptree [7,6,5,4,3,2,1]))

end binary_tree
