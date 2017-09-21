import galois.data.bounded_list
import galois.list.take_drop_lemmas
import galois.list.member

universes u v

namespace merkle

structure combine_result (Link Data : Type) :=
(root : Data)
(left : Link)
(right : Link)

/-- Operations needed to build a Merkle tree.-/
structure ops (Leaf Link Data : Type) :=
(empty_root : Data)
(leaf_data : Leaf → Data)
(combine_data : Data -> Data → combine_result Link Data)
/-- This stores information about a path from a leaf to a root.

 max_req_level bounds the length of the links.
-/
structure path (Leaf Link : Type) (max_req_level : ℕ) :=
(leaf  : Leaf)
(links : bounded_list Link max_req_level)

/-- This represents a result of computing a merkle tree-/
structure result (Leaf Link Data : Type) (max_req_level : ℕ) :=
-- what we are aggregating
(root : Data)
-- the paths through the tree to get to this point
(paths : list (path Leaf Link max_req_level))
-- what we have not yet aggregated
(remaining : list Leaf)

section path

parameters {Leaf Link : Type}

def path.extend_none {n:ℕ} (p : path Leaf Link n)
: path Leaf Link n.succ :=
  { links := p.links.extend 1
  , leaf  := p.leaf
  }

theorem path.leaf_extend_none (n : ℕ)
: path.leaf ∘ @path.extend_none n = path.leaf :=
begin
  apply funext,
  intro p,
  cases p,
  simp [function.comp, path.extend_none],
end

def path.extend_sibling {n : ℕ}
    (l : Link)
    (p : path Leaf Link n)
: path Leaf Link n.succ :=
{ links := p.links.cons l
, leaf  := p.leaf
}

theorem path.leaf_extend_sibling (n : ℕ) (l : Link)
: path.leaf ∘ @path.extend_sibling n l = path.leaf :=
begin
  apply funext,
  intro p,
  cases p,
  simp [function.comp, path.extend_sibling],
end

end path

section merkle

-- This contains the types for the leaves of the tree and link elements
parameters {Leaf Link Data : Type}
parameter (ops : ops Leaf Link Data)

def merkle_core
     : Π (n : ℕ) (e : Leaf) (rest : list Leaf), result Leaf Link Data n
| 0 e rest :=
{ root := ops.leaf_data e
, paths := [{ leaf := e
            , links := bounded_list.nil
            }]
, remaining := rest
}
| (nat.succ n) e rest := do
  let left_result := merkle_core n e rest in
  match left_result.remaining with
  | [] :=
      { root := left_result.root
      , paths := left_result.paths.map path.extend_none
      , remaining := []
      }
  | (e' :: rest') :=
      let right_result := merkle_core n e' rest' in
      let z := ops.combine_data left_result.root right_result.root in
      { root := z.root
      , paths := left_result.paths.map  (path.extend_sibling z.left)
              ++ right_result.paths.map (path.extend_sibling z.right)
      , remaining := right_result.remaining
      }
  end

section proofs


theorem merkle_core_ind
  {P : ℕ → Leaf → list Leaf → Prop}
  (n : ℕ) (e : Leaf) (l : list Leaf)
  (base : ∀ (e:Leaf) (l:list Leaf), P 0 e l)
  (ind1 : ∀ (n:ℕ) (e:Leaf) (l:list Leaf)
      (pr : (merkle_core n e l).remaining = list.nil)
      (ind : P n e l), P n.succ e l)
  (ind2 : ∀ (n:ℕ) (e:Leaf) (l:list Leaf) (v : Leaf) (r : list Leaf)
      (pr : (merkle_core n e l).remaining = v :: r)
      (ind : P n e l), P n.succ e l)

: P n e l :=
begin
  induction n,
  case nat.zero { apply base },
  case nat.succ m ind {
    destruct (merkle_core ops m e l).remaining,
    { intro rl,
      exact ind1 m e l rl ind,
    },
    {
      intros v r rl,
      exact ind2 m e l v r rl ind,
    }
  }

end

parameters (n :ℕ) (e : Leaf) (l : list Leaf)

theorem merkle_core_paths_ne : (merkle_core n e l).paths ≠ [] :=
begin
  induction n,
  { simp [merkle_core], },
  case nat.succ n ind {
    simp [merkle_core],
    cases (merkle_core ops n e l).remaining,
    all_goals {
      simp [merkle_core],
      cases (merkle_core ops n e l).paths,
      { contradiction, },
      { simp, },
    },
  }
end

theorem merkle_core_remaining (n:ℕ) (e : Leaf) (l : list Leaf)
: (merkle_core n e l).remaining = l.drop (2^n-1) :=
begin
  revert e l,
  induction n,
  case nat.zero {
    intros e l,
    simp [merkle_core],
  },
  case nat.succ n ind {
    intros e l,
    simp only [merkle_core, ind],
    have h : (2^nat.succ n - 1) = (2^n-1) + 2^n,
    {
      simp [nat.pow, nat.succ_mul],
      simp [nat.add_sub_assoc, nat.one_le_pow, nat.succ_le_succ_iff
           , nat.zero_le],
    },
    rw [h, list.drop_add],
    cases (l.drop (2^n - 1)) with r rest,
    { simp [merkle_core], },
    { simp [merkle_core, ind, nat.pow_is_zero_iff], },
  },
end

theorem merkle_core_list_lengths (n:ℕ) (e : Leaf) (l : list Leaf)
: (merkle_core n e l).paths.length + (merkle_core n e l).remaining.length
   = l.length + 1 :=
begin
  revert e l,
  induction n,
  case nat.zero {
    intros e l,
    simp [merkle_core],
  },
  case nat.succ n ind {
    intros e l,
    simp only [merkle_core],
    destruct (merkle_core ops n e l).remaining,
    case list.nil {
      intro eq,
      rw [eq],
      simp only [merkle_core, list.length_map],
      have pr := ind e l, rw [eq] at pr,
      apply pr,
    },
    case list.cons {
      intros r rest eq, rw [eq],
      simp only [merkle_core, list.length_append, list.length_map],
      rw [ add_assoc, ind],
      have final := ind e l,
      rw [eq] at final,
      exact final,
    }
  },
end

end proofs

def merkle
     : Π (n : ℕ) (l : list Leaf), result Leaf Link Data n
| n [] :=
{ root := ops.empty_root
, paths := []
, remaining := []
}
| n (e::r) := merkle_core n e r

section merkel_proofs

parameters (n : ℕ) (l : list Leaf)

theorem merkle_paths_ne (pr : l ≠ []) : (merkle n l).paths ≠ [] :=
begin
  cases l,
  { contradiction, },
  case list.cons e r {
    simp [merkle],
    apply merkle_core_paths_ne,
  }
end

theorem merkle_paths_length (n:ℕ) (l : list Leaf)
: (merkle n l).paths.length = min (2^n) l.length :=
begin
  cases l,
  case list.nil { simp [merkle], },
  case list.cons e l {
    simp [merkle],
    have pr := merkle_core_list_lengths ops n e l,
    simp [merkle_core_remaining] at pr,
    admit,
  },
end

theorem merkel_paths_nth_leaf  {n:ℕ} {l : list Leaf}
   {idx : ℕ}
   {r : Leaf}
   (r_at_idx : l.nth idx = some r)
   {p : path Leaf Link n}
   (pr : (merkle n l).paths.nth idx = some p)
: p.leaf = r :=
begin
  admit
end


end merkel_proofs

end merkle

end merkle
