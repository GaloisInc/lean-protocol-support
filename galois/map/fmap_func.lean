/- An implementation of key-value maps
   using functions

  Includes a dependent map, allowing for mappings into multiple types,
  as well as a non-dependent map, with only a single value tyep
-/

universes u v w

/-- 
The type of Dependent maps. Takes a total mapping from keys to type and
represents a partial mapping from keys of type K to values of type defined by V -/
def mapd {K : Type u} (V : K → Type v) : Type (max u v)
  := ∀ k, option (V k)

/--
A non-dependent map type with a single value type.
-/
@[reducible]
def map (K : Type u) (V : Type v) : Type (max u v)
   := mapd (λ _ : K, V)

namespace mapd

section
/- We parameterize the key type and require decidable equality on it -/
parameter {K : Type u} 
parameter [decidable_eq K]
parameter {V : K → Type v}

/-- An empty map, all lookups return none-/
def empty : mapd V := fun _, none

/-- Function to make finds explicit.-/
def find (k : K) (m : mapd V) : option (V k) := m k

/-- All empty lookups are none -/
lemma empty_char (k : K) : find k empty = none := rfl

/-- Put an item into the map, shadowing any previous definitions-/
def insert (k : K) (v : V k) (m : mapd V) : mapd V := 
  λ k' : K, if H : k = k'
       then some (eq.rec_on H v)
       else find k' m

/--
Relationship between find and insert
-/
lemma insert_char (k : K) (v : V k) (m : mapd V) (k' : K) :
  find k' (insert k v m) = if H : k = k'
       then some (eq.rec_on H v)
       else find k' m
:= rfl

-- perhaps this is lazy, it should fail if not already there?
def update := insert

/-- Remove a mapping -/
def remove (k : K) (m : mapd V) : mapd V :=
  λ k' : K, if H : k = k'
       then none
       else m k'

/-- Relationship between remove and find-/
lemma remove_char (k : K) (m : mapd V) (k' : K) :
     find k' (remove k m) = if H : k = k'
       then none
       else find k' m
:= rfl

/-- Extensionality for maps-/
lemma eq_rel (m m' : mapd V) (H : ∀ k, find k m = find k m') : m = m'
:= funext H

/-- Map over all values contained in the map-/
def fmapd {V' : K → Type w} (f : ∀ k : K, V k → V' k) (m : mapd V) : mapd V'
:= λ k, option_map (f k) (find k m)
end

/--
Interaction between fmapd and find
-/
lemma fmapd_char {K : Type u} [decidable_eq K] {V : K → Type v}
  {V' : K → Type w} (f : ∀ k : K, V k → V' k) (m : mapd V)
  (k : K) : find k (fmapd f m) = option_map (f k) (find k m)
  := rfl

/-- Map over non-dependent maps-/
def fmap {K : Type u} [decidable_eq K] {V : Type v}
  {V' : Type w} (f : V → V') (m : map K V) : map K V'
:= λ k, option_map f (find k m)

/--
Interaction between fmap and find
-/
lemma fmap_char {K : Type u} [decidable_eq K] {V : Type v}
  {V' : Type w} (f : V → V') (m : map K V)
  (k : K) : find k (fmap f m) = option_map f (find k m)
  := rfl

attribute [irreducible] mapd
attribute [irreducible] find
attribute [irreducible] insert
attribute [irreducible] remove

section
parameter {K : Type u} 
parameter [decidable_eq K]
parameter {V : K → Type v}

/--
Update the value already contained at key k by function f.
Has no effect if there is no existing mapping for k
-/
def updatef (k : K) (f : V k → V k) (m : mapd V) : mapd V
  := 
  match find k m with
  | none := m
  | some v := insert k (f v) m
  end

/-- Definition of functions over maps that can be reordered, assuming they
     are about distinct keys
-/
def permutable (f : ∀ k : K, V k → mapd V → mapd V) :=
  ∀ (m : mapd V) (k k' : K) (v : V k) (v' : V k'), 
     k ≠ k' → f k v (f k' v' m) = f k' v' (f k v m)

lemma neq_symm {A : Type u} {x y : A}
  (H : x ≠ y) : y ≠ x
:= begin
intros contra,
apply H, symmetry, assumption
end

/-- We can reorder inserts over distinct keys -/
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

/-- 
Relationship between find and insert with the same key
-/
lemma find_insert_refl (m : mapd V)
  (k : K) (v : V k) : find k (insert k v m) = some v
:= begin
rw insert_char,
rw (dif_pos (eq.refl k))
end

/--
A membership structure to allow lookups that
come with a proof of membership
-/
structure member (m : mapd V) :=
  (key : K)
  (value : V key)
  (in_map : find key m = some value)

inductive is_member (k : K) (m : mapd V) : Prop
  | mk : ∀ value : V k, find k m = some value → is_member


instance member_decidable (m : mapd V) 
  : decidable_eq (member m)
:= begin
unfold decidable_eq, unfold decidable_rel,
intros k k', cases k with k v kv,
cases k' with k' v' kv',
apply (if H : k = k' then _ else _),
{ apply decidable.is_true,
  induction H,
  rw kv at kv',
  injection kv',
  induction h,
  apply congr_arg,
  admit 
  /- I should use a quotient on `member` that ignores the
     equality proof, but this will be annoying, and for
     now I'm too lazy
  -/
},
{ apply decidable.is_false,
  intros contra, injection contra, contradiction }
end

/--
Definition of when we say a key is in a map
-/
inductive key_in_map (k : K) (m : mapd V) : Prop
| mk : ∀ v : V k, find k m = some v → key_in_map

/-- 
Get the member, if there is a member at k
-/
def check_member (m : mapd V) (k : K) : option (member m) :=
begin
destruct (find k m); intros,
{ exact none },
{ apply some, constructor, assumption }
end

@[reducible]
def check_member_ty (m : mapd V) (k : K) (w : option (V k)) : Type (max u v) := match w with
  | some v := find k m = w → psigma (λ x : m.member, x.key = k)
  | none := punit
  end

--set_option pp.implicit true

def check_member2 (m : mapd V) (k : K) : check_member_ty m k (find k m) :=
begin
refine (
    @option.rec (V k) (λ (w : option (V k)), check_member_ty m k w)
    _
    _
    (find k m)
),
dsimp [check_member_ty],
exact punit.star,
dsimp [check_member_ty],
intros v H, fapply psigma.mk,
fapply member.mk, exact k, assumption, assumption,
reflexivity
end

--#print check_member2

--set_option pp.implicit true

-- def check_member' :=
-- λ (m : @mapd K V) (k : K),
--   @option.rec (V k) (λ (w : option (V k)), option (member m))
--     (λ (H : find k m = none), none)
--     (λ (v : V k) (H : find k m = some v), some (@member.mk m k v H))
--     (find k m)

-- #check check_member'

/--
If we get a member from a map, the key in the member should be the key
we used for the check_member
-/
lemma check_member_same_key {m : mapd V} {k : K} {x : m.member}
  (H : check_member m k = some x)
  : x.key = k
:= begin
admit,
end

lemma check_member_same {m : mapd V} {x x' : m.member}
  (H : check_member m (x.key) = some x')
  : x = x'
:= begin
admit
end

/--
We can do a total lookup if we know the key is in the map already
-/
def mfind (k : K) (m : mapd V) (mem : key_in_map k m) : V k
:= begin 
destruct (find k m); intros,
{ exfalso, induction mem,
  rw a at a_1,
  contradiction },
{ assumption }
end

/--

-/
def lookup_update {m : mapd V} {B} (k : K)
  (update : B → B)
  (f : m.member → B) : m.member → B
  := λ x, if x.key = k
    then update (f x)
    else f x

def lookup_modify {m : mapd V} {B : m.member → Type}
  (k : m.member) (v : B k) (f : ∀ x : m.member, B x)
  : ∀ x : m.member, B x
  := λ x, if H : k = x then eq.rec v H else f x

end

namespace is_member
def value {K : Type u} [decidable_eq K] {V : K → Type v}
   {k : K} {m : mapd V} (H : is_member k m)
   : V k :=
   begin
   destruct (mapd.find k m); intros,
   { exfalso, destruct H; intros, 
    rw a at a_1, contradiction
   },
   { assumption }
   end

lemma update {K : Type u} [decidable_eq K] {V : K → Type v}
  {k : K} {m : mapd V} (H : is_member k m)
  (k' : K) (v' : V k')
  : is_member k (update k' v' m)
:= begin
induction H,
unfold update,
apply (if H : k' = k then _ else _),
{ induction H, 
  existsi v', rw find_insert_refl },
{ apply (is_member.mk value),
  rw insert_char,
  rw (dif_neg H), assumption
}
end

end is_member 

def member_unfmap {K : Type u} 
  [decidable_eq K]
  {V : K → Type v}
  {V' : K → Type w} {f : ∀ k : K, V k → V' k} 
  (m : mapd V)
  (x : member (fmapd f m)) : member m
  :=
begin
cases x,
destruct (find key m); intros,
{ unfold fmapd at in_map,
  unfold find at in_map, unfold find at a,
  unfold option_map at in_map,
  rw a at in_map,
  simp [option_bind] at in_map,
  contradiction },
{ constructor, assumption } 
end

def member_fmap {K : Type u} 
  [decidable_eq K]
  {V : K → Type v}
  {V' : K → Type w} 
  (m : mapd V)
  (x : member m)
  (f : ∀ k : K, V k → V' k) : member (fmapd f m)
  :=
begin
constructor, rw fmapd_char,
rw x.in_map, simp [option_map],
simp [option_bind], 
end

namespace depv
section
parameters {K : Type u} [decidable_eq K] {V : Type v}
           {B : V → Type w}

def lookup_empty : ∀ x : (empty : map K V).member, B (x.value) :=
begin
intros x, cases x, rw empty_char at in_map,
contradiction
end

inductive liftProp (P : Prop) : Type
  | mk : P → liftProp

@[reducible]
def insert_member_invert (m : map K V)
  (k : K) (v : V)
  (x : (insert k v m).member)
  : (liftProp (k = x.key)) ⊕ m.member
:= begin
apply (if H : k = x.key then _ else _),
apply sum.inl, constructor, assumption,
apply sum.inr,
constructor,
have H' := x.in_map,
rw insert_char at H',
rw (dif_neg H) at H', assumption
end

def lookup_insert (m : map K V) (f : ∀ x : m.member, B x.value)
  (k : K) (v : V) (b : B v)
  (x : (insert k v m).member) : B x.value
:= begin
apply (if H : k = x.key then _ else _),
{ have H' : @eq.rec_on _ _ (λ _, V) _ H v = x.value, 
  { have in_map := x.in_map, 
  rw mapd.insert_char at in_map,
  rw (dif_pos H) at in_map,
  injection in_map,
  },
  { admit }
},
{ admit }
end

end
end depv


end mapd