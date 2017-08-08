import aim.list

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

-- if we get a node by index, dropping the last step of that index gives us the parent of that node
lemma dropLastHasParent : forall {a: Type} (i : list nat) (t : tree a) (p: a) (c:a),
i ≠ [] ->
some c = at_index i t ->
some p = at_index (list.drop_last i) t ->
hasparent p c t :=
sorry /-begin
intros _ _ _ _ _ lne sc cp, cases t with it cs,
induction i with h t ih,
  contradiction,
  simp [at_index] at sc,
  unfold list.drop_last at cp,
  cases (list.nth cs h) with c,
    unfold bind at sc,
end
-/

lemma bind_some : forall {a β: Type} (i : a) (f : a → option β),
(some i >>= f) = f i :=
begin
  admit
end


lemma atIndex_update : forall {a : Type} (t nt: tree a) (i : list nat) (n : a),
    update_index_item n i t = some nt ->
    at_index i nt = some n :=
begin
intros,
induction i,
 { cases t,
    simp [update_index_item] at a_1,
    injection a_1,
    subst nt,
    simp [at_index, subtree_at_index, bind_some, rootitem],
    trivial,
 },
 {
    rename a_1 a,
     cases t,
     simp [update_index_item] at a,
     admit,

 }

end


end tree
