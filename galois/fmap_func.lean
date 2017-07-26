/- A simple implementation of key-value maps
   using functions
-/

universes u v w

def map {K : Type u} (V : K → Type v) : Type (max u v)
  := ∀ k, option (V k)

namespace map

section
parameters {K : Type u} [decidable_eq K] {V : K → Type v}

def empty : map V := fun _, none

def find (k : K) (m : map V) : option (V k) := m k

lemma empty_char (k : K) : find k empty = none := rfl

def insert (k : K) (v : V k) (m : map V) : map V := 
  λ k' : K, if H : k = k'
       then some (eq.rec_on H v)
       else find k' m

lemma insert_char (k : K) (v : V k) (m : map V) (k' : K) :
  find k' (insert k v m) = if H : k = k'
       then some (eq.rec_on H v)
       else find k' m
:= rfl

-- perhaps this is lazy, it should fail if not already there?
def update := insert

def remove (k : K) (m : map V) : map V :=
  λ k' : K, if H : k = k'
       then none
       else m k'

lemma remove_char (k : K) (m : map V) (k' : K) :
     find k' (remove k m) = if H : k = k'
       then none
       else find k' m
:= rfl

lemma eq_rel (m m' : map V) (H : ∀ k, find k m = find k m') : m = m'
:= funext H

attribute [irreducible] map
attribute [irreducible] find
attribute [irreducible] insert
attribute [irreducible] remove

def updatef (k : K) (f : V k → V k) (m : map V) : map V
  := 
  match find k m with
  | none := m
  | some v := insert k (f v) m
  end

def permutable (f : ∀ k : K, V k → map V → map V) :=
  ∀ (m : map V) (k k' : K) (v : V k) (v' : V k'), 
     k ≠ k' → f k v (f k' v' m) = f k' v' (f k v m)

lemma neq_symm {A : Type u} {x y : A}
  (H : x ≠ y) : y ≠ x
:= begin
intros contra,
apply H, symmetry, assumption
end

lemma insert_permutable : permutable insert
:= begin
unfold permutable, intros m k k' v v' Hne,
apply eq_rel,
intros z,
repeat {rw insert_char},
apply (if Hkz : k = z then _ else _),
{ rw (dif_pos Hkz),
  subst z,
  rw (dif_neg (neq_symm Hne)),
  rw (dif_pos (eq.refl k)) },
{ repeat {rw (dif_neg Hkz)},
}
end

end
end map