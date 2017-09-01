-- author: Ben Sherman
import .lptree
       galois.list
       galois.list.filter_some

namespace binary_tree

universes u v

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

def tree_mem {A} (t : tree A) : tree A -> Prop
| (tree.node i l r) := t = tree.node i l r ∨ tree_mem l ∨ tree_mem r
| (tree.leaf i) := t = tree.leaf i

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

end binary_tree
