import galois.list

namespace tree

inductive tree (α : Type ) : Type
| node : α → list tree → tree
open tree

def isLeaf {α : Type} : tree α -> bool
| (tree.node _ [] ) := true
| _ := false

def rootitem {a : Type } : tree a -> a
| (tree.node i _) := i

def childitems {a : Type} : tree a -> list a
| (tree.node i cs) := do
                        c <- cs,
                        return (rootitem c)

def rootchildren {a : Type} : tree a -> list (tree a)
| (tree.node _ cs) := cs


inductive hasparent {a : Type} (parent : a) (child : a) : tree a -> Prop
| parent_root : ∀ (t : list (tree a)), list.Exists (λ x, eq child (rootitem x)) t -> hasparent (tree.node parent t)
| move_down : ∀ (t' : list (tree a)) t, list.Exists hasparent t' -> hasparent t

inductive Exists {a: Type} (P : a -> Prop) : tree a -> Prop
| Exists_this : forall i t, P i -> Exists (tree.node i t)
| Exists_rest : forall i t, list.Exists Exists t -> Exists (tree.node i t)

def In {a} (i:a) := Exists (eq i)

inductive Forall {a: Type} (P : a -> Prop) : tree a -> Prop
| Forall_this : forall i t, P i -> list.Forall Forall t -> Forall (tree.node i t)


def subtree_at_index {a :Type} : list ℕ -> tree a -> option (tree a)
| [] x := some x /-(tree.node i t) := some i -/
| (h::t) (tree.node i cs) := do
                                nc <- list.nth cs h ,
                                subtree_at_index t nc

def at_index {a :Type} (i : list ℕ) (t : tree a) :=
    do
        st <- subtree_at_index i t,
        return (rootitem st)


def update_index_node {a : Type} (n: tree a) : list ℕ -> tree a -> option (tree a)
| [] (tree.node _ _) := some n
| (h::t) (tree.node i cs) := do nc <- list.nth cs h,
                              uc <- update_index_node t nc,
                              return (tree.node i (list.update_nth cs h uc))

def update_index_item {a : Type} (i: a) : list ℕ -> tree a -> option (tree a)
| [] (tree.node _ cs) := some (tree.node i cs)
| (h::t) (tree.node i cs) := do nc <- list.nth cs h,
                              uc <- update_index_item t nc,
                              return (tree.node i (list.update_nth cs h uc))


end tree
