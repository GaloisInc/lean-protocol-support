import galois.tactic

inductive ext (A : Type) : Type
| inj {} : A → ext
| inf {} : ext
| neg_inf {} : ext

namespace ext
section
parameters (A : Type) [decidable_linear_order A]

def le : ext A → ext A → Prop
| neg_inf   _      := true
| _        inf     := true
| (inj _)  neg_inf := false
| (inj x)  (inj y) := x ≤ y
| inf      (inj _) := false
| inf      neg_inf := false

instance : has_le (ext A) := ⟨ le ⟩

inductive lt (x y : ext A) : Prop
| mk : ∀ (le : x ≤ y) (not_rev_le : ¬ (y ≤ x)), lt

instance : has_lt (ext A) := ⟨ lt ⟩

instance le_decidable : decidable_rel (@has_le.le (ext A) _) :=
begin
intros x y,
induction x; induction y; simp [(≤), le];
  apply_instance,
end

lemma lt_equiv (a b : ext A) : a < b ↔ a ≤ b ∧ ¬b ≤ a
:= begin
split; intros H; induction H; split; assumption,
end

instance lt_decidable : decidable_rel (@has_lt.lt (ext A) _) :=
begin
intros x y, rw lt_equiv, apply_instance,
end

lemma le_refl (x : ext A) : x ≤ x :=
begin
simp only [(≤)], induction x; simp only [le],
end

lemma le_trans {x y z : ext A} (H : x ≤ y) (H' : y ≤ z)
  : x ≤ z :=
begin
simp only [(≤)] at *,
induction x; induction y; induction z; simp only [le] at *;
  try { contradiction },
apply le_trans; assumption
end

lemma le_antisymm (a b : ext A) : a ≤ b → b ≤ a → a = b
:= begin
simp only [(≤)], intros H H', induction a; induction b;
  simp only [le] at *; try { contradiction },
f_equal, apply le_antisymm; assumption
end

lemma le_total (a b : ext A) : a ≤ b ∨ b ≤ a
:= begin
simp only [(≤)], induction a; induction b;
  simp only [le]; try {cc},
  apply le_total,
end

lemma neg_inf_le (x : ext A) : neg_inf ≤ x
:= begin
simp only [(≤)], induction x; simp [le],
end

lemma le_inf (x : ext A) : x ≤ inf
:= begin
simp only [(≤)], induction x; simp [le],
end

instance eq_decidable : decidable_eq (ext A) :=
  by tactic.mk_dec_eq_instance

instance linear_order_decidable : decidable_linear_order (ext A) :=
begin
constructor, apply ext.le_decidable,
apply_instance, apply ext.lt_decidable,
apply le_refl, apply le_trans,
unfold auto_param, intros,
apply lt_equiv, apply le_antisymm,
apply le_total,
end

end
end ext

namespace list

def maximum_ext {α:Type _} [decidable_linear_order α] : list (ext α) → ext α
  := list.foldr max ext.neg_inf

def minimum_ext {α:Type _} [decidable_linear_order α] : list (ext α) → ext α
  := list.foldr min ext.inf

end list

lemma maximum_ext_le {α: Type _} [decidable_linear_order α]
  (xs : list (ext α)) (u : ext α)
  (H : ∀ x : ext α, x ∈ xs → x ≤ u)
  : xs.maximum_ext ≤ u
:= begin
unfold list.maximum_ext,
induction xs; dsimp [list.foldr],
apply ext.neg_inf_le,
apply max_le, apply H, rw list.mem_cons_eq,
left, reflexivity, apply ih_1, intros,
apply H,rw list.mem_cons_eq, right, assumption
end

lemma le_minimum_ext {α: Type _} [decidable_linear_order α]
  (xs : list (ext α)) (l : ext α)
  (H : ∀ x : ext α, x ∈ xs → l ≤ x)
  : l ≤ xs.minimum_ext
:= begin
unfold list.minimum_ext,
induction xs; dsimp [list.foldr],
apply ext.le_inf,
apply le_min, apply H, rw list.mem_cons_eq,
left, reflexivity, apply ih_1, intros,
apply H,rw list.mem_cons_eq, right, assumption
end

theorem le_ext_maximum_minimum {α: Type _} [decidable_linear_order α]
  (ll ul : list (ext α))
  (pr : ∀ (l u : ext α), l ∈ ll → u ∈ ul → l ≤ u)
  : ll.maximum_ext ≤ ul.minimum_ext
:= begin
apply maximum_ext_le,
intros, apply le_minimum_ext, intros, apply pr; assumption
end