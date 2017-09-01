import .lptree_to_tree

universes u

namespace binary_tree

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
    simp only [second],
    simp only [reconstruct_root],
    have H' := comp_par_corr (root l) (root r) lr.right,
    simp only [compute_parent_correct] at H',
    dsimp [reconstruct_root] at H,
    dsimp [list.foldr],
    rw H, apply H', }
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


theorem end_to_end_height (xs : list A)
  (f : A → A → A)
  : list.Forall (λ ls : list link, ls.length ≤ log2 (xs.length + 1)) $
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
  rw list_to_lptree_height' xs,
 }
end

end paths

end binary_tree