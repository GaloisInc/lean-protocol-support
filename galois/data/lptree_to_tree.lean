import .lptree .binary_tree
       galois.option

namespace binary_tree

def twice {A} (f : A -> A -> A)
  (x y : A × A) : A × A :=
  let (a, b) := x in let (p, q) := y in
     (f a b, f p q)

def untwice_tree {A} (f : A -> A -> A)
  : tree (A × A) -> tree A
| (tree.leaf (x, y)) := tree.node (f x y) (tree.leaf x) (tree.leaf y)
| (tree.node (x, y) l r) := tree.node (f x y) (untwice_tree l) (untwice_tree r)

lemma untwice_tree_height {A} (f : A → A → A)
  (x : tree (A × A))
  : (untwice_tree f x).height = x.height + 1
:= begin
induction x; induction item; dsimp [untwice_tree, tree.height],
{ rw nat.max_same, },
{ rw ih_1, rw ih_2, clear ih_1 ih_2 fst snd,
  f_equal, rw nat.max_add,
}
end

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

lemma tree_height_untwice_tree {A} (f : A → A → A) :
  (tree.height ∘ untwice_tree f) = (nat.succ ∘ tree.height)
:= begin
apply funext, intros x; dsimp [function.comp],
rw untwice_tree_height,
end

lemma asc_heights_helper_mono {m n : ℕ} (H : m ≤ n)
  (xs : list ℕ)
  : asc_heights m xs ≤ asc_heights n xs
:= begin
revert m n,
induction xs; intros; dsimp [asc_heights], assumption,
apply ih_1, apply nat.add_le_add_right, apply nat.max_mono,
apply nat.le_refl, assumption,
end

lemma asc_heights_succ (n : ℕ) (xs : list ℕ)
  : asc_heights n.succ (xs.map nat.succ) ≤ (asc_heights n xs).succ
:= begin
revert n;
induction xs; intros; dsimp [asc_heights],
{ constructor, },
{ repeat { rw ← nat.add_one },
  rw nat.max_add, apply le_trans, apply ih_1,
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

def assemble_left_subtrees_option {A} (f : A → A → A) : list (option (tree A)) → option (tree A)
| [] := none
| (none :: xs) := assemble_left_subtrees_option xs
| (some x :: xs) := some (assemble_left_subtrees f x xs.filter_some)

def lptree_to_tree_option {A} (f : A -> A -> A)
  (t : lptree A) : option (tree A) :=
  assemble_left_subtrees_option f (lptree_to_tree_helper_option f t)

lemma lptree.nonzero_subtrees {A} (t : lptree A)
  (f : A -> A -> A)
  (H : lptree_to_tree_helper f t ≠ [])
  : option.Issome (lptree_to_tree f t)
  :=
begin
unfold lptree_to_tree,
revert H,
destruct (lptree_to_tree_helper f t); intros,
{ contradiction },
{ clear H, rw a_2, simp [lptree_to_tree._match_1], constructor }
end


lemma lptree.nonzero_tree {A} (t : lptree A)
  (f : A -> A -> A)
  (tnonzero : lptree.nonzero t)
  : option.Issome (lptree_to_tree f t) :=
begin
apply lptree.nonzero_subtrees,
induction tnonzero with A x t A ma t tnonzero IHtnonzero,
{ dsimp, simp [lptree_to_tree_helper], },
{ simp [lptree_to_tree_helper],
  cases ma; simp [lptree_to_tree_helper._match_1],
  { apply list.map_not_nil, apply IHtnonzero },
}
end


def merge_to_tree {A} (f : A -> A -> A)
  (xs : list A) : option (tree A)
  := lptree_to_tree f (list_to_lptree xs)

lemma list_to_tree_Some {A} (xs : list A)
  f (H : xs ≠ [])
  : option.Issome (merge_to_tree f xs)
  :=
begin
  apply lptree.nonzero_tree,
  apply list_to_lptree.nonzero,
  assumption
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
     apply list.map_nil, apply contra },
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
 asc_heights n (list.map tree.height xs.filter_some) ≤
    asc_heights n
      (list.map (opt_default 0 ∘ option_map tree.height) xs)
:= begin
revert n,
induction xs; intros; dsimp [asc_heights, list.map, list.filter_some],
{ apply le_refl },
{ induction a; dsimp [list.filter_some],
  { apply le_trans, apply ih_1,
    apply asc_heights_helper_mono,
    apply le_trans, tactic.swap, apply nat.le_add_r,
    apply le_max_right, },
  { dsimp [asc_heights], apply le_trans,
    apply ih_1,
    apply asc_heights_helper_mono,
    apply nat.add_le_add_right,
    apply nat.max_mono,
    { apply le_refl },
    { apply le_refl }
  }
}
end

lemma asc_heights_filter_some {A} (n : ℕ) (xs : list (option (tree A))) :
 asc_heights n (list.map tree.height xs.filter_some) ≤
    asc_heights (n + 1)
      (list.map (opt_default 0 ∘ option_map tree.height) xs)
:= begin
apply le_trans, apply asc_heights_filter_some1,
apply asc_heights_helper_mono, constructor, constructor,
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
      rw nat.max_0_r,
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
  apply nat.max_mono,
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
  repeat { rw ← nat.add_one }, rw ← nat.max_add,
  apply nat.max_mono,
  { induction a; dsimp [opt_default, function.comp, option_map, option_bind],
    apply nat.zero_le, apply le_refl,
  },
  { apply le_refl }
}
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
  rw ← option.map_compose,
  rw tree_height_untwice_tree,
  rw option.map_compose (tree.height) (nat.succ),
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

lemma lptree_to_tree_helper_option_equiv
  {A : Type}
  (f : A → A → A) (lpt : lptree A)
  : lptree_to_tree_helper f lpt
  = (lptree_to_tree_helper_option f lpt).filter_some
:= begin
induction lpt;
  dsimp [lptree_to_tree_helper, lptree_to_tree_helper_option, list.filter_some],
{ reflexivity },
{ induction a;
    dsimp [option_map, option_bind, lptree_to_tree_helper
      , lptree_to_tree_helper_option, list.filter_some],
    { rw list.map_filter_some, f_equal,
    apply ih_1, },
    { f_equal, rw list.map_filter_some, f_equal, apply ih_1 }
 }
end

lemma assemble_left_subtrees_option_filter_some
  {A : Type} (f : A → A → A)
  (xs : list (option (tree A)))
  : assemble_left_subtrees_option f xs = match xs.filter_some with
  | [] := none
  | (y :: ys) := some (assemble_left_subtrees f y ys)
  end
:= begin
induction xs; dsimp [list.filter_some, assemble_left_subtrees_option],
{ reflexivity },
{ rename a x, induction x; dsimp [list.filter_some, assemble_left_subtrees_option],
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

lemma lptree.leaves_helper_same' {A} f (t : lptree A)
 : t.leaves
 = left_subtrees_leaves' (lptree_to_tree_helper f t) :=
begin
induction t,
{ reflexivity },
{ simp [lptree.leaves],
  simp [lptree_to_tree_helper],
  cases a,
  { simp [lptree.leaves],
    simp [lptree_to_tree_helper],
    rw (ih_1 (twice f)),
    rw depair_leaves,
   },
  { simp [lptree.leaves],
    simp [lptree_to_tree_helper],
    simp [left_subtrees_leaves'],
    simp only [tree.leaves],
    f_equal,
    rw (ih_1 (twice f)),
    apply depair_leaves },
}
end

lemma lptree.leaves_helper_same {A} f (t : lptree A)
 : t.leaves
 = match lptree_to_tree_helper f t with
   | [] := []
   | x :: xs := left_subtrees_leaves f xs x
   end :=
begin
simp,
rw (lptree.leaves_helper_same' f),
generalize : (lptree_to_tree_helper f t) = xs,
intros,
cases xs,
{ reflexivity },
{ dsimp,
  symmetry,
  apply left_subtrees_leaves_same }
end

/-- If we compute the leaves of an lptree, it is the same
    as if we convert it to a binary tree and then compute
    the leaves
-/
lemma tree_lptree.leaves {A} f (t : lptree A)
  : t.leaves = tree_leaves_option (lptree_to_tree f t)
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
  apply (@option.not_Issome_none (tree A)),
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
    rw (lptree.leaves_helper_same f),
    simp, rw W }
}
end

/-- If we take a list, convert it to an lptree, convert
    that to a binary tree, and compute the leaves,
    we get back the original list
-/
lemma lptree.leaves_ok {A} (f : A -> A -> A) (xs : list A)
  : xs = tree_leaves_option (merge_to_tree f xs) :=
begin
transitivity,
rw ← (lptree_leaves_list xs),
unfold merge_to_tree,
rw (tree_lptree.leaves f)
end

--#eval (lptree_to_tree nat.add (list_to_lptree [7,6,5,4,3,2,1]))

end binary_tree