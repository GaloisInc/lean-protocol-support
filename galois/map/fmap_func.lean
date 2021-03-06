/- An implementation of key-value maps
   using functions

  Includes a dependent map, allowing for mappings into multiple types,
  as well as a non-dependent map, with only a single value tyep
-/

universes u v w

namespace option

structure has_value {V : Type u} (x : option V) :=
  (value : V)
  (value_ok : x = some value)

def check_has_value {V : Type u} (x : option V) : option (has_value x) :=
begin
destruct x; intros,
{ exact none },
{ apply some, constructor, assumption }
end

end option

/--
The type of Dependent maps. Takes a total mapping from keys to type and
represents a partial mapping from keys of type K to values of type defined by V
-/
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
:= λ k, option.map (f k) (find k m)
end

/--
Interaction between fmapd and find
-/
lemma fmapd_char {K : Type u} [decidable_eq K] {V : K → Type v}
  {V' : K → Type w} (f : ∀ k : K, V k → V' k) (m : mapd V)
  (k : K) : find k (fmapd f m) = option.map (f k) (find k m)
  := rfl

/-- Map over non-dependent maps-/
def fmap {K : Type u} [decidable_eq K] {V : Type v}
  {V' : Type w} (f : V → V') (m : map K V) : map K V'
:= λ k, option.map f (find k m)

/--
Interaction between fmap and find
-/
lemma fmap_char {K : Type u} [decidable_eq K] {V : Type v}
  {V' : Type w} (f : V → V') (m : map K V)
  (k : K) : find k (fmap f m) = option.map f (find k m)
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


lemma find_insert_neq {m : mapd V}
  {k k' : K} (H : k ≠ k') (v : V k) : find k' (insert k v m) = find k' m
:= begin
rw insert_char,
rw (dif_neg H)
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

def has_value_to_member {m : mapd V} {k : K} (x : (find k m).has_value)
  : member m
:= { key := k, value := x.value, in_map := x.value_ok  }

/--
Get the member, if there is a member at k
-/
def check_member (m : mapd V) (k : K) : option (member m) :=
  option.map has_value_to_member (find k m).check_has_value

def check_member_same_key {m : mapd V} {k : K} {v : m.member}
(H : check_member m k = some v)
  : v.key = k :=
begin
dsimp [check_member] at H,
destruct ((find k m).check_has_value); intros,
{ rw a at H, contradiction },
{ rw a_1 at H,
  simp [option.map, option.bind, function.comp] at H,
  injection H with H', clear H,
  subst v, simp [has_value_to_member], }
end

lemma member_eq_value {m : mapd V} {k : K} {v v' : V k}
  (H : v = v')
  {in1 : find k m = some v} {in2 : find k m = some v'}
  : member.mk k v in1 = member.mk k v' in2 :=
begin
induction H,
trivial
end

lemma check_member_same {m : mapd V} {x x' : m.member}
  (H : check_member m (x.key) = some x')
  : x = x'
:= begin
dsimp [check_member] at H,
destruct ((find x.key m).check_has_value); intros,
{ rw a at H, contradiction },
{ rw a_1 at H,
  simp [option.map, option.bind, function.comp] at H,
  injection H with H', clear H, subst x',
  simp [has_value_to_member],
  have H2 := a.value_ok,
  have H3 := x.in_map, rw H2 at H3, clear H2,
  injection H3 with H, clear H3,
  induction x, dsimp, dsimp at H,
  apply member_eq_value, symmetry, assumption }
end

def mfind (k : K) (m : mapd V) (mem : is_member k m) : V k
:= begin
destruct (find k m); intros,
{ exfalso, induction mem,
  rw a at a_1,
  contradiction },
{ assumption }
end

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
  injection kv' with h,
  induction h,
  apply congr_arg, apply proof_irrel,
},
{ apply decidable.is_false,
  intros contra, injection contra, contradiction }
end

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
  unfold option.map at in_map,
  rw a at in_map,
  simp [option.bind] at in_map,
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
rw x.in_map, simp [option.map],
simp [option.bind],
end

def depv {K : Type u} [decidable_eq K] {V : Type v}
  (m : map K V) (B : V → Type w)
  := ∀ x : m.member, B x.value

namespace depv
section
parameters {K : Type u} [decidable_eq K] {V : Type v}
           {B : V → Type w}

def lookup_empty : depv (empty : map K V) B :=
begin
intros x, cases x, rw empty_char at in_map,
contradiction
end

inductive liftProp (P : Prop) : Type
  | mk : P → liftProp

@[reducible]
def insert_member_invert {m : map K V}
  {k : K} {v : V}
  (x : (insert k v m).member)
  : (liftProp (k = x.key)) ⊕
  ((find x.key m).has_value × liftProp (¬ k = x.key))
:= begin
apply (if H : k = x.key then _ else _),
{ apply sum.inl, constructor, assumption },
{ apply sum.inr,
  constructor, constructor,
  have H' := x.in_map,
  rw insert_char at H',
  rw (dif_neg H) at H', assumption,
  constructor, assumption
}
end

def lookup_insert {m : map K V}
  (k : K) (v : V) (b : B v) (f : depv m B)
  : depv (insert k v m) B
:= begin
intros x,
have H := insert_member_invert x,
induction H with H H,
{ induction H with H,
  induction x,
  dsimp, dsimp at H, induction H,
  rw mapd.insert_char at in_map,
  rw (dif_pos (eq.refl k)) at in_map,
  injection in_map with h, clear in_map,
  subst h, apply b,
},
{ induction H with H H1,
  induction H1 with H1,
  induction x,
  let H' := member.mk key H.value H.value_ok,
  dsimp, dsimp at H, dsimp at H1,
  rw (find_insert_neq H1) at in_map,
  rename in_map in_map',
  have H' := H.value_ok,
  rw H' at in_map',
  injection in_map' with H2,
  clear H1 H' in_map', subst value,
  apply (f H'),
 }
end

end
end depv


end mapd