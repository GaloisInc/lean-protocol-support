
-- Vaguely following an approach taken in this paper:
-- https://arxiv.org/pdf/1401.7886.pdf
-- author: Ben Sherman

import galois.list.preds
import galois.tactic

namespace binary_tree

run_cmd mk_simp_attr `empt

section trees
universe variable u

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

/-- Indicates when an `lptree A` has at least one value of `A` in it
    (i.e., its corresponding binary natural number is nonzero.)
-/
inductive lptree_nonzero : ∀  {A : Type u}, lptree A -> Prop
| nonzero_cons_some : ∀ {A} (a : A) t, lptree_nonzero (lptree.cons (some a) t)
| nonzero_extend : ∀ {A} ma (t : lptree (A × A)), @lptree_nonzero (A × A) t ->
    lptree_nonzero (lptree.cons ma t)

-- def ptree_to_lptree : ∀ {A} {n}, ptree A n -> lptree A
-- | A 0 x := lptree.cons (some x) lptree.nil
-- | A (nat.succ n') x:= lptree.cons none (@ptree_to_lptree (A × A) n' x)

/-- Add a single element to a left-perfect tree.
    (A generalization of adding one to a binary natural number.)
-/
def lptree_cons : ∀ {A : Type u}, A -> lptree A -> lptree A
| A x lptree.nil := lptree.cons (some x) lptree.nil
| A x (lptree.cons none t') := lptree.cons (some x) t'
| A x (lptree.cons (some y) t') := lptree.cons none (lptree_cons (y, x) t')

/-- If you add one to an lptree, it is nonzero
-/
def lptree_cons_nonzero {A : Type u} (t : lptree A)
  : ∀ x : A, lptree_nonzero (lptree_cons x t) :=
begin
induction t with A A ma t IHt; intros x,
{ simp [lptree_cons], constructor },
{ cases ma,
  { simp [lptree_cons], constructor },
  { simp [lptree_cons], constructor, apply IHt }
}
end


def list_to_lptree {A : Type u} : list A -> lptree A :=
  list.foldr lptree_cons lptree.nil

/-- Binary trees *with* internal nodes
    (which differs from both `ptree` and `lptree`)

    In this formulation, every binary tree has at least
    one item of type A in it.
-/
inductive tree (A : Type) : Type
| leaf (item : A) : tree
| node (item : A) (l r : tree) : tree 

def twice {A} (f : A -> A -> A)
  (x y : A × A) : A × A :=
  let (a, b) := x in let (p, q) := y in
     (f a b, f p q).

def untwice_tree {A} (f : A -> A -> A)
  : tree (A × A) -> tree A 
| (tree.leaf (x, y)) := tree.node (f x y) (tree.leaf x) (tree.leaf y)
| (tree.node (x, y) l r) := tree.node (f x y) (untwice_tree l) (untwice_tree r)

/-- Pick the item at the root of the tree -/
def root {A} : tree A -> A
| (tree.node x _ _) := x
| (tree.leaf x) := x

/-- Combine a left and right subtree into a single tree
    with some function that determines the root of the
    new tree from the roots of the subtrees
-/
def combine {A} (f : A -> A -> A) (l r : tree A)
  : tree A := tree.node (f (root l) (root r)) l r.

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

inductive Issome {A} : option A -> Prop
  | MkIsSome : forall a : A, Issome (some a)

lemma lptree_nonzero_subtrees {A} (t : lptree A)
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
{ simp [list.map] with empt, contradiction }
end


lemma lptree_nonzero_tree {A} (t : lptree A)
  (f : A -> A -> A)
  (tnonzero : lptree_nonzero t)
  : Issome (lptree_to_tree f t) :=
begin
apply lptree_nonzero_subtrees,
induction tnonzero with A x t A ma t tnonzero IHtnonzero,
{ dsimp, simp [lptree_to_tree_helper] with empt, contradiction },
{ simp [lptree_to_tree_helper],
  cases ma; simp [lptree_to_tree_helper._match_1] with empt,
  { apply map_not_nil, apply IHtnonzero },
  { contradiction }
}
end

/-- Enumerate the leaves of a binary tree from right to left
-/
def tree_leaves {A} : tree A -> list A
| (tree.node x l r) := tree_leaves r ++ tree_leaves l
| (tree.leaf x) := [x]

def tree_leaves_option {A} : option (tree A) -> list A
| none := []
| (some t) := tree_leaves t

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
| [] x := tree_leaves x
| (y :: ys) x := left_subtrees_leaves ys (combine f y x)

lemma tree_leaves_combine {A} f
  (x y : tree A)
  : tree_leaves (combine f x y)
  = tree_leaves y ++ tree_leaves x :=
begin
induction x,
  { simp [combine, tree_leaves] },
  { reflexivity }
end

/-- Enumerate the leaves of a tree specified by a list of
    left subtrees (with an empty rightmost subtree)
    in reverse order
-/
def left_subtrees_leaves' {A}
  : list (tree A) -> list A
| [] := []
| (t :: ts) := tree_leaves t ++ left_subtrees_leaves' ts


lemma left_subtrees_leaves_same {A}
  (f : A -> A -> A) (ts : list (tree A))
  : ∀ t : tree A, 
    left_subtrees_leaves f ts t = tree_leaves t ++ left_subtrees_leaves' ts
  :=
begin
induction ts; intros,
  { simp [left_subtrees_leaves],
    simp [left_subtrees_leaves']
  },
  { simp [left_subtrees_leaves'], 
    simp [left_subtrees_leaves],
    rw ih_1, 
    rw tree_leaves_combine,
    rw list.append_assoc
   }
end

lemma list_to_lptree_nonzero {A} (xs : list A)
  (H : xs ≠ []) : lptree_nonzero (list_to_lptree xs) :=
begin
cases xs,
{ contradiction },
{ simp [list_to_lptree], apply lptree_cons_nonzero }
end

def merge_to_tree {A} (f : A -> A -> A)
  (xs : list A) : option (tree A)
  := lptree_to_tree f (list_to_lptree xs)

def merge_to_tree_default {A} (f : A -> A -> A)
  (xs : list A) (default : A) : tree A :=
  match merge_to_tree f xs with 
  | (some t) := t
  | none := tree.leaf default
  end

lemma list_to_tree_Some {A} (xs : list A)
  f (H : xs ≠ []) 
  : Issome (merge_to_tree f xs)
  :=
begin
  apply lptree_nonzero_tree,
  apply list_to_lptree_nonzero,
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
  : lptree_nonzero t :=
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

/-- Decision procedure to determine whether
    an lptree is nonempty
-/
def lptree_nonzero_bool
  : ∀ {A : Type}, lptree A -> bool
| _ lptree.nil := false
| _ (lptree.cons (some x) t) := true
| _ (lptree.cons none t) := lptree_nonzero_bool t

def lptree_nonzero_bool_equiv {A : Type}
  (t : lptree A)
  : lptree_nonzero_bool t = true ↔ lptree_nonzero t
:=
begin
split; intro H,
{ induction t,
  { contradiction },
  { cases a, simp [lptree_nonzero_bool] at H,
    { constructor,
      apply ih_1, assumption },
    { constructor }
  }
},
{ induction H, 
  { simp [lptree_nonzero_bool] },
  { cases ma, 
    { simp [lptree_nonzero_bool], assumption },
    { reflexivity }
  }
}
end

def lptree_nonzero_dec {A : Type}
  (t : lptree A)
  : decidable (lptree_nonzero t)
:=
begin
rw <- lptree_nonzero_bool_equiv,
apply bool.decidable_eq
end

lemma lptree_to_tree_some_nonzero {A}
  (f : A -> A -> A)
  (t : lptree A) :
  ∀ (x : tree A) (H : lptree_to_tree f t = some x), lptree_nonzero t :=
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
   tree_leaves (assemble_left_subtrees f x xs)
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
f_equal; apply root_untwice_tree; assumption
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
  : lptree_leaves (lptree_cons x t) = 
     x :: lptree_leaves t
  :=
begin
induction t,
{ reflexivity },
{ cases a,
  { simp [lptree_cons, lptree_to_tree, lptree_to_tree_helper], 
    simp [lptree_leaves]},
  { simp [lptree_cons],
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
  : depair (tree_leaves t) = tree_leaves (untwice_tree f t)
:=
begin
induction t,
{ cases item, simp [tree_leaves, untwice_tree],
  simp [depair]
},
{ simp [tree_leaves],
  rw depair_app,
  rw [ih_1, ih_2],
  cases item with i1 i2,
  simp [untwice_tree],
  simp [tree_leaves] }
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
    simp [tree_leaves] with empt,
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
  (H : ¬ lptree_nonzero t)
  : lptree_leaves t = []
:= begin
rw <- lptree_nonzero_bool_equiv at H,
induction t,
{ reflexivity },
{ cases a,
  { simp [lptree_leaves],
    apply depair_nil, apply ih_1,
    simp [lptree_nonzero_bool] at H,
    assumption
     },
  { simp [lptree_nonzero_bool] at H,
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
  
  cases (lptree_nonzero_dec t),
  apply lptree_not_nonzero_no_leaves,
  assumption,
  cases t,
  reflexivity,
  exfalso,
  have H' := lptree_nonzero_tree _ f a,
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

lemma list.map_extensional {A B : Type} (f g : A -> B)
  (xs : list A)
  : (∀ x, f x = g x)
  -> list.map f xs = list.map g xs
:= begin
intros H,
induction xs,
{ reflexivity },
{ simp [list.map], f_equal,
  apply H, assumption
 }
end

lemma list.append_nil_left {A} (xs : list A)
  : xs = [] ++ xs := rfl

lemma list.map_compose {A B C : Type} 
  (f : A -> B) (g : B -> C) (xs : list A)
  : list.map (g ∘ f) xs = list.map g (list.map f xs)
:=
begin
induction xs,
{ reflexivity },
{ simp [list.map] }
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
{ simp [function.comp] }
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

def all_paths_core : tree A -> path -> list (A × path)
| (tree.node i l r) path :=  
                 all_paths_core r ((lr.right, root l) ::path)
              ++ all_paths_core l ((lr.left, root r) ::path)
| (tree.leaf i) path := [(i, path)]

/-- get all paths (in order left to right) from root to leaf
    these paths start with leafs, and are meant to be followed
    up the tree in order to reconstruct a root in log(n) operations
 -/
def all_paths (tr : tree A): list (A × path) :=
              all_paths_core tr []

def second {X A B : Type} (f : A -> B) : X × A -> X × B
| (x, y) := (x, f y)

def all_paths' : tree A -> list (A × path)
| (tree.leaf i) := [(i, [])]
| (tree.node i l r) :=
     list.map (second (λ p, p ++ [(lr.right, root l)])) (all_paths' r)
  ++ list.map (second (λ p, p ++ [(lr.left, root r)])) (all_paths' l)

/-- Get all paths, but this time the paths give the direction
    to follow from the root to the leaf. Finally, we also return the
    leaf element that the path leads to.
-/
def all_paths_rev : tree A -> list (A × path)
| (tree.leaf i) := [(i, [])]
| (tree.node i l r) :=
     list.map (second (list.cons (lr.right, root l))) (all_paths_rev r)
  ++ list.map (second (list.cons (lr.left , root r))) (all_paths_rev l)

lemma all_paths_core_app (t : tree A) (p p' : path)
  : all_paths_core t (p ++ p') =
    list.map (second (λ z, z ++ p')) (all_paths_core t p)
:= begin
revert p p',
induction t; intros,
{ reflexivity },
{ simp [all_paths_core],
  rw [<-list.cons_append, <-list.cons_append],
  rw [ih_1, ih_2] }
end

lemma all_paths_same_core (t : tree A) (p : path)
  : all_paths_core t p = list.map (second (λ z, z ++ p)) (all_paths' t)
:=
begin
revert p,
induction t; intros,
{ reflexivity },
{ simp [all_paths_core, all_paths'],
  f_equal,
  { rw ih_2,
    apply list.map_extensional,
    intros, cases x with i1 i2,
    dsimp [function.comp, second],
    simp [second] },
  { rw ih_1,
    apply list.map_extensional,
    intros, cases x with i1 i2,
    dsimp [function.comp, second], simp [second] }
}
end

lemma all_paths_same (t : tree A)
  : all_paths t = all_paths' t
:= begin
unfold all_paths,
rw all_paths_same_core,
apply list.map_id',
intros x, cases x with i1 i2,
simp [second]
end

/-- Indeed, `all_paths` and `all_paths` are the same, except one
    gives paths in the reverse order compared to the other
-/
lemma all_paths_reverse (t : tree A)
  : list.map (second list.reverse) (all_paths_rev t) = all_paths' t
:=
begin
induction t,
{ reflexivity },
{ simp [all_paths_rev, all_paths'],
  f_equal,
  { rw <- ih_2,
    rw <- list.map_compose,
    apply list.map_extensional,
    intros x, cases x with lf xs,
    simp [function.comp, second] },
  { rw <- ih_1,
    rw <- list.map_compose,
    apply list.map_extensional,
    intros x, cases x with lf xs,
    simp [function.comp, second]  }
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


def reconstruct_root (f : A -> A -> A) : path -> A -> A
| [] lf := lf
| ((lr.left, i) :: xs) lf := f (reconstruct_root xs lf) i
| ((lr.right, i) :: xs) lf := f i (reconstruct_root xs lf)

def reconstruct_items_rev (f : A → A → A) : path → A → list A
| [] lf := []
| (x :: xs) lf := reconstruct_root f (x :: xs) lf :: reconstruct_items_rev xs lf

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

/-- If we compute the list of paths to all leaves in a tree
    where the internal nodes are all the result of applying 
    and then use those paths and the leaves they point to
    to try to 

-/
lemma reconstruct_root_correct (f : A -> A -> A)
  (t : tree A)
  (H : internal_nodes_ok f t)
  : list.Forall (λ p : A × path, 
    reconstruct_root f p.snd p.fst = root t) (all_paths_rev t)
:= begin
induction H,
{ simp [all_paths_rev], constructor,
  { dsimp, simp [reconstruct_root], reflexivity },
  { constructor }
},
{ simp [all_paths_rev],
  apply list.concat_Forall,
  { clear ih_1, apply list.map_Forall,
    apply list.impl_Forall, apply ih_2,
    clear ih_2 a a_1,
    simp [root],
    intros p, subst x, cases p with lf p,
    dsimp,
    intros H,
    dsimp [second],
    simp [reconstruct_root],
    rw <- H },
  { clear ih_2, apply list.map_Forall,
    apply list.impl_Forall, apply ih_1,
    clear ih_1 a a_1,
    simp [root],
    intros p, subst x, cases p with lf p,
    dsimp,
    intros H,
    simp [second],
    simp [reconstruct_root],
    rw <-H  }
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

/-- The leaves produced by the `all_paths_rev`
    function agree with the leaves produced
    by `tree_leaves`
-/
lemma all_paths_rev_tree_leaves (f : A -> A -> A)
  (t : tree A)
  : list.map prod.fst (all_paths_rev t)
  = tree_leaves t
:= begin
induction t,
{ reflexivity },
{ simp [tree_leaves, all_paths_rev],
  rw list.map_fst_second,
  rw list.map_fst_second,
  rw ih_1, rw ih_2
  }
end

lemma reconstruct_items_correct (f : A -> A -> A) 
  (t : tree A)
  : internal_nodes_ok f t
  -> list.Forall (λ p, let (lf, pth) := p in  
      path_in_tree_rev lf (reconstruct_items_rev f pth lf) t) (all_paths_rev t) 
:= begin
intros H, induction H,
{ simp [all_paths_rev],
  constructor, dsimp, constructor, constructor },
{ dsimp at ih_1 ih_2,
  dsimp, simp [all_paths_rev],
  apply list.concat_Forall,
  { apply list.map_Forall,
    apply_in a_1 (reconstruct_root_correct),
    apply list.impl_Forall2, apply a_1, apply ih_2,
    intros p H H', induction p with lf pth,
    dsimp at H H', dsimp [second],
    simp [reconstruct_items_rev],
    simp [reconstruct_root], rw H,
    rw ← a_2, apply path_in_tree_rev.right, assumption,
  },
  { apply list.map_Forall,
    apply_in a reconstruct_root_correct,
    apply list.impl_Forall2, apply a, apply ih_1,
    intros p H H', induction p with lf pth,
    dsimp at H H', dsimp [second],
    simp [reconstruct_items_rev],
    simp [reconstruct_root], rw H,
    rw ← a_2, apply path_in_tree_rev.left, assumption, }
}
end

end paths

end trees

--#eval (lptree_to_tree nat.add (list_to_lptree [7,6,5,4,3,2,1]))

end binary_tree