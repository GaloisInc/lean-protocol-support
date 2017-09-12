import galois.tactic
       galois.fin

universes u

structure vector_ind_succ {A : Type u} {n : ℕ} (xs : vector A n.succ)
  : Type u :=
  (head : A)
  (tail : vector A n)
  (equiv : xs = head :: tail)

namespace vector

def generate {A : Type _} : ∀ (n : ℕ) (f : ℕ → A),
  vector A n
| 0 _ := nil
| (nat.succ n) f := f 0 :: generate n (f ∘ nat.succ)

def invert_succ {A : Type _} {n : ℕ} (xs : vector A n.succ)
  : vector_ind_succ xs
  := ⟨ xs.head, xs.tail, eq.symm (cons_head_tail _) ⟩

lemma map₂_nil {A B C} (f : A → B → C)
  : map₂ f nil nil = nil
  := rfl

lemma map₂_cons {A B C} (f : A → B → C)
  (a : A) (b : B) {n : ℕ} (as : vector A n) (bs : vector B n)
  : map₂ f (a :: as) (b :: bs) = f a b :: map₂ f as bs
:= begin
induction as, induction bs, reflexivity,
end

lemma repeat_unfold {A} (n : ℕ) (x : A)
  : repeat x n.succ = x :: repeat x n
:= rfl


lemma nth_cons_nz {A} {n : ℕ} (i : fin n.succ)
  (H : i ≠ 0)
  (x : A) (xs : vector A n)
  : nth (x :: xs) i = nth xs (fin.pred i H)
:= begin
induction xs, induction i,
dsimp [cons, nth, fin.pred],
have H : val_1 ≠ 0, intros contra,
apply H, unfold has_zero.zero, subst val_1,
cases val_1, contradiction,
dsimp [list.nth_le], reflexivity,
end

lemma nth_0 {A : Type _} {n : ℕ} (x : A) (xs : vector A n)
  {i : fin n.succ} (Hi : i.val = 0)
  : nth (x :: xs) i = x
:= begin
induction i, dsimp at Hi,
subst val, induction xs,
dsimp [nth, cons], reflexivity
end

lemma nth_cons_zero {A} {n : ℕ}
  (x : A) (xs : vector A n)
  : nth (x :: xs) 0 = x
:= begin
apply nth_0, reflexivity,
end

lemma map₂_comm {A B} (f : A → A → B)
  (f_comm : ∀ x y, f x y = f y x)
  {n : ℕ} (xs ys : vector A n)
  : map₂ f xs ys = map₂ f ys xs
:= begin
induction n,
{ rw (vector.eq_nil xs), rw (vector.eq_nil ys), },
{ have Hx := xs.invert_succ, induction Hx with x xs' Hx, subst xs,
  have Hy := ys.invert_succ, induction Hy with y ys' Hy, subst ys,
  repeat { rw map₂_cons }, rw f_comm,
  f_equal, apply ih_1,
}
end

lemma generate_const_repeat {A} (n : ℕ) (c : A)
  : generate n (λ _, c)
  = repeat c n
:= begin
induction n; dsimp [repeat, generate],
reflexivity,
rw ih_1, reflexivity,
end

lemma nth_of_fn {A} {n : ℕ} (f : fin n → A)
  (i : fin n)
  : nth (of_fn f) i = f i
:= begin
revert f i,
induction n; intros; dsimp [of_fn],
{ exfalso, apply fin.fin_0_empty, assumption, },
{ apply (if H : i = 0 then _ else _),
  { subst i, rw vector.nth_cons_zero, },
  { rw vector.nth_cons_nz, tactic.swap, assumption,
    rw ih_1, rw fin.succ_pred_id, }
}
end

lemma nil_of_fn {A} : @vector.nil A = vector.of_fn (begin
  intros i, exfalso, apply fin.fin_0_empty, assumption,
  end)
:= eq.symm (vector.eq_nil _)


end vector