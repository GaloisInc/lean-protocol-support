import galois.data.bounded_list
import galois.list.take_drop_lemmas

universes u v

namespace ksi
namespace merkle

structure combine_result (Link Data : Type) :=
(root : Data)
(left : Link)
(right : Link)

/-- Operations needed to build a Merkle tree.-/
structure merkle_ops (Leaf Link Data : Type) :=
(empty_root : Data)
(leaf_data : Leaf → Data)
(apply_link : Link → Data → Data)
(combine_data : Data -> Data → combine_result Link Data)
(apply_left_correct
: ∀(x y : Data), apply_link (combine_data x y).left x = (combine_data x y).root)
(apply_right_correct
: ∀(x y : Data), apply_link (combine_data x y).right y = (combine_data x y).root)

section types

parameters {Leaf Link Data : Type}
parameter (s : merkle_ops Leaf Link Data)

/-- This stores information about a path from a leaf to a root.

 max_req_level bounds the length of the links.
-/
structure path (max_req_level : ℕ) (root : Data) :=
(leaf  : Leaf)
(links : bounded_list Link max_req_level)
-- Proof theat the
(root_valid : links.val.foldr s.apply_link (s.leaf_data leaf) = root)

/-- This represents-/
structure merkle_result (max_req_level : ℕ) (l : list Leaf) :=
-- what we are aggregating
(root : Data)
-- the paths through the tree to get to this point
(paths : list (path max_req_level root))
-- what we have not yet aggregated
(remaining : list Leaf)
-- Proof we include all the original paths.
(paths_valid : paths.map path.leaf ++ remaining = l)
-- The length of the paths
(remaining_valid : remaining = l.drop (2^max_req_level))

end types

section merkle

-- This contains the types for the leaves of the tree and link elements
parameters {Leaf Link Data : Type}
parameter (ops : merkle_ops Leaf Link Data)

def path.extend_none {n:ℕ} {root : Data} (p : path ops n root)
: path ops n.succ root :=
  { links := p.links.extend 1
  , leaf  := p.leaf
  , root_valid :=
    begin
      cases p,
      cases links,
      exact root_valid,
    end
  }

theorem path_extend_none (n : ℕ) (root : Data)
: path.leaf ∘ @path.extend_none n root = path.leaf :=
begin
  apply funext,
  intro p,
  cases p,
  simp [function.comp, path.extend_none],
end

def gpath.extend_sibling (n : ℕ) {r r' : Data}
    (l : Link)
    (eq : ops.apply_link l r = r')
    (p : path ops n r)
: path ops n.succ r' :=
{ links := p.links.cons l
, leaf  := p.leaf
, root_valid :=
  begin
    cases p,
    cases links,
    simp [bounded_list.cons, root_valid, eq],
  end
}

theorem path_extend_sibling (n : ℕ) (r r' : Data) (l : Link)
  (eq : ops.apply_link l r = r')
: path.leaf ∘ @gpath.extend_sibling n r r' l eq = path.leaf :=
begin
  apply funext,
  intro p,
  cases p,
  simp [function.comp, gpath.extend_sibling],
end

def dcases_on {T : Type u} {C : list T → Sort v}
  (n : list T)
  (base : n = [] → C [])
  (ind : Π (h : T) (r : list T), n = h::r → C (h :: r))
: C n :=
   @list.cases_on T (λl, n = l → C l) n base ind rfl

def merkle_core
     : Π (n : ℕ) (e : Leaf) (rest : list Leaf),
       merkle_result ops n (e::rest)
| 0 e rest :=
{ root := ops.leaf_data e
, paths := [{ leaf := e
            , links := bounded_list.nil
            , root_valid := rfl,
            }]
, remaining := rest
, paths_valid := rfl
, remaining_valid := rfl
}
| (nat.succ n) e rest := do
  let left_result := merkle_core n e rest in
  @dcases_on _ (λr, merkle_result ops n.succ (e::rest)) left_result.remaining
    (λ(eq : left_result.remaining = []),
      { root := left_result.root
      , paths := left_result.paths.map path.extend_none
      , remaining := left_result.remaining
      , paths_valid :=
        begin
          simp [path_extend_none, left_result.paths_valid],
        end
      , remaining_valid :=
        begin
          have h : (2^nat.succ n) = 2^n + 2^n,
          { simp [nat.pow, nat.succ_mul], },
          have g := left_result.remaining_valid,
          rw [h, list.drop_add, ← g, eq, list.drop_nil],
        end
      })
    (λ(e' : Leaf) (rest' : list Leaf) (eq : left_result.remaining = e' :: rest'),
      let right_result := merkle_core n e' rest' in
      let z := ops.combine_data left_result.root right_result.root in
      let l_eq := ops.apply_left_correct left_result.root right_result.root in
      let r_eq := ops.apply_right_correct left_result.root right_result.root in
      { root := z.root
      , paths := left_result.paths.map  (gpath.extend_sibling n z.left  l_eq)
              ++ right_result.paths.map (gpath.extend_sibling n z.right r_eq)
      , remaining := right_result.remaining
      , paths_valid :=
        begin
          simp [path_extend_sibling, right_result.paths_valid],
          rw [← eq],
          exact left_result.paths_valid,
        end
      , remaining_valid :=
        begin
          have h : (2^nat.succ n) = 2^n + 2^n,
          { simp [nat.pow, nat.succ_mul], },
          rw [h, list.drop_add, ← left_result.remaining_valid, eq],
          exact right_result.remaining_valid,
        end
      })

def merkle
     : Π (n : ℕ) (l : list Leaf), merkle_result ops n l
| n [] :=
{ root := ops.empty_root
, paths := []
, remaining := []
, paths_valid := rfl
, remaining_valid := by simp [list.drop_nil],
}
| n (e::r) := merkle_core n e r


end merkle

end merkle
end ksi