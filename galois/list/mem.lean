import galois.tactic

universes u

namespace list
def mem_induction {A : Type u}
  (P : A → list A → Prop)
  (Phere : ∀ x xs, P x (x :: xs))
  (Pthere : ∀ x y ys, P x ys → P x (y :: ys))
  (x : A) (xs : list A) (H : x ∈ xs)
  : P x xs
:= begin
induction xs, cases H,
dsimp [has_mem.mem, list.mem] at H,
induction H, subst a, apply Phere,
apply Pthere, apply ih_1, assumption,
end

lemma mem_map' {A B} (f : A → B) (xs : list A)
  (x : A) (y : B) (H : f x = y)
  (H' : x ∈ xs)
  : y ∈ xs.map f
:= begin
subst H, apply mem_induction _ _ _ _ _ H'; intros,
left, reflexivity, right, assumption,
end

end list

lemma list.mem_bind' {A B} (xs : list A) (f : A → list B)
  (y : B) (H : y ∈ xs >>= f)
  : ∃ x : A, x ∈ xs ∧ y ∈ f x
:= begin
dsimp [(>>=), list.bind, list.join] at H,
induction xs; dsimp [list.map, list.join] at H,
rw list.mem_nil_iff at H, contradiction,
rw list.mem_append at H,
induction H with H H',
existsi a, split, constructor, reflexivity, assumption,
specialize (ih_1 H'),
induction ih_1 with x H,
induction H with H1 H2,
existsi x, split,
dsimp [has_mem.mem, list.mem],
right, assumption, assumption,
end

lemma list.mem_bind_iff' {A B} (xs : list A) (f : A → list B)
  (y : B)
  : y ∈ xs >>= f
  ↔ ∃ x : A, x ∈ xs ∧ y ∈ f x
:= begin
split; intros H, apply list.mem_bind', assumption,
induction H with x Hx, induction Hx with H1 H2,
dsimp [(>>=), list.bind, list.join],
induction xs; dsimp [list.map, list.join],
rw list.mem_nil_iff at H1, contradiction,
rw list.mem_append, dsimp [has_mem.mem, list.mem] at H1,
induction H1 with H1 H1, subst a,
left, assumption, right, apply ih_1, assumption,
end