import data.hash_map
import galois.list.fpow

universes u v w

lemma neq_symm {A : Type u} {x y : A}
  (H : x ≠ y) : y ≠ x
:= begin
intros contra,
apply H, symmetry, assumption
end

namespace map

/- Key-value maps. Not necessarily with finite domain.
   For instance, we could implement this with just
   `K → option V`.
-/
class mapc (K : Type u) (V : K → Type v)
   (Map : Type w) :=
  (deceqK : decidable_eq K)
  (empty : Map)
  (find : ∀ (k : K) (m : Map), option (V k))
  (insert : ∀  (k : K) (v : V k), Map → Map)
  (remove : ∀ (k : K), Map → Map)
  (eq_rel : ∀ (m m' : Map), 
     (∀ k, find k m = find k m') → m = m')
  (insert_char : ∀ (m : Map) (k : K) (v : V k) 
    (k' : K),
     find k' (insert k v m) = if H : k = k'
       then some (eq.rec_on H v)
       else find k' m)
  (remove_char : ∀ (m : Map) (k k' : K),
     find k' (remove k m) = if H : k = k'
       then none
       else find k' m)

instance (K : Type u) (V : K → Type v)
   (Map : Type w) [mapc K V Map] : decidable_eq K
  := mapc.deceqK V Map

/- Key-value maps with finite domain, indicated
   by the fact that their entires can be summarized
   by a Kuratowski-finite powerset.-/
class fmapc (K : Type u) (V : K → Type v) (Map : Type w)
  [deceqK : decidable_eq K]
  [inst : mapc K V Map] :=
  (to_list : Map → fpow (sigma V))
  (to_list_char : ∀ k (v : V k) (m : Map),
     mapc.find V k m = some v ↔ sigma.mk k v ∈ to_list m)

section map_facts
parameters {K : Type u} {V : K → Type v}
  (Map : Type w)
  [mapM : mapc K V Map]

include mapM

def updatef (k : K) (f : V k → V k) (m : Map) : Map
  := 
  match mapc.find V k m with
  | none := m
  | some v := mapc.insert k (f v) m
  end

def permutable (f : ∀ k : K, V k → Map → Map) :=
  ∀ (m : Map) (k k' : K) (v : V k) (v' : V k'), 
     k ≠ k' → f k v (f k' v' m) = f k' v' (f k v m)

lemma insert_permutable : 
  permutable (@mapc.insert _ _ Map mapM)
:= begin
unfold permutable, intros m k k' v v' Hne,
apply (@mapc.eq_rel _ _ Map mapM),
intros z,
repeat {rw mapc.insert_char},
apply (if Hkz : k = z then _ else _),
{ rw (dif_pos Hkz),
  subst z,
  rw (dif_neg (neq_symm Hne)),
  rw (dif_pos (eq.refl k)) },
{ repeat {rw (dif_neg Hkz)},
}
end

end map_facts

end map

def hash_map_eq {K : Type u} {V : K → Type v} 
  [decidable_eq K]
  (m m' : hash_map K V) :=
  ∀ k, m.find k = m'.find k

def hash_map_q (K : Type u) (V : K → Type v) [decidable_eq K]
: Type (max u v) := quot (@hash_map_eq K V _)

namespace hash_map_q
section 
parameters {K : Type u} {V : K → Type v} [decidable_eq K]

def empty (hash : K → ℕ) : hash_map_q K V := 
  quot.mk _ (mk_hash_map hash)

def insert (k : K) (v : V k) (m : hash_map_q K V)
  : hash_map_q K V
  :=
begin
fapply (quot.lift_on m),
exact ((λ x, quot.mk _ (x.insert k v))),
intros m m' Heq,
apply quot.sound, unfold hash_map_eq,
intros k',
repeat {rw hash_map.find_insert},
apply (if H : k = k' then _ else _),
repeat {rw (dif_pos H)},
repeat {rw (dif_neg H)}, apply Heq
end

def remove (k : K) (m : hash_map_q K V)
  : hash_map_q K V
:=
begin
fapply (quot.lift_on m),
exact (λ x, quot.mk _ (x.erase k)),
intros m m' Heq, apply quot.sound,
unfold hash_map_eq,
intros k',
repeat {rw hash_map.find_erase},
apply (if H : k = k' then _ else _),
repeat {rw (if_pos H)},
repeat {rw (if_neg H)}, apply Heq
end

def find (k : K) (m : hash_map_q K V)
  : option (V k) :=
begin
fapply (quot.lift_on m),
exact (λ x, x.find k),
intros m m' Heq, apply Heq
end

def to_list (m : hash_map_q K V) : fpow (sigma V)
:= begin
fapply (quot.lift_on m),
exact (λ x, fpow.from_list x.entries),
intros m m' H, apply quot.sound,
unfold same_elements,
intros z, cases z,
repeat {rw <- hash_map.find_iff},
rw (H fst)
end

end
end hash_map_q

instance hash_map_map (K : Type u) (V : K → Type v)
  [decidable_eq K]
  (hash : K → ℕ)
  : map.mapc K V (hash_map_q K V) :=
{ deceqK := by apply_instance
, empty := hash_map_q.empty hash
, find := hash_map_q.find
, insert := hash_map_q.insert
, remove := hash_map_q.remove
, eq_rel := begin
  intros m m' Heq, induction m, induction m',
  apply quot.sound, apply Heq,
  reflexivity, reflexivity,
  end
, insert_char := begin
  intros,
  induction m, simp [hash_map_q.insert],
  simp [hash_map_q.find],
  simp [quot.lift_on], 
  apply hash_map.find_insert,
  reflexivity
  end
, remove_char := begin
  intros,
  induction m, simp [hash_map_q.remove],
  simp [hash_map_q.find],
  simp [quot.lift_on],
  apply (if H : k = k' then _ else _),
  repeat {rw (dif_pos H)},
  induction H,
  apply hash_map.find_erase_eq,
  repeat {rw (dif_neg H)},
  apply hash_map.find_erase_ne,
  assumption, reflexivity
  end
}

instance hash_map_fmap (K : Type u) (V : K → Type v)
  [deceqK : decidable_eq K]
  (hash : K → ℕ)
  : @map.fmapc K V (hash_map_q K V) deceqK
    (hash_map_map K V hash) :=
begin
tactic.fconstructor,
{ exact hash_map_q.to_list },
{ intros,
  induction m,
  simp [map.mapc.find, hash_map_q.find, 
        hash_map_q.to_list, quot.lift_on],
  apply hash_map.find_iff,
  reflexivity
 }

end