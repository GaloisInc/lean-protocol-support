import data.rat
       galois.logic
       galois.vector.lemmas

def dot_product {n : ℕ} (x y : vector ℚ n) : ℚ
  := list.foldr (+) 0 (vector.map₂ (*) x y).to_list

lemma dot_product_cons {n : ℕ} (x y : ℚ) (xs ys : vector ℚ n)
  : dot_product (x :: xs) (y :: ys)
  = x * y + dot_product xs ys
:= begin
induction xs, induction ys,
reflexivity,
end

lemma dot_product_nil : dot_product vector.nil vector.nil = 0
  := rfl

lemma dot_product_0_len (xs ys : vector ℚ 0)
  : dot_product xs ys = 0
:= begin
rw vector.eq_nil xs, rw vector.eq_nil ys, reflexivity,
end


lemma dot_product_0 {n : ℕ} (xs : vector ℚ n)
  : dot_product (vector.generate n (λ _, 0)) xs = 0
:= begin
induction n,
rw vector.eq_nil xs,
rw dot_product_0_len,
dsimp [vector.generate],
have Hxs := xs.invert_succ, induction Hxs with x xs' Hxs,
subst xs, rw dot_product_cons,
rw ih_1, simp,
end


lemma dot_product_unit (n : ℕ) (i : fin n) (c : ℚ) (v : vector ℚ n)
  : dot_product (vector.generate n (λj, if i.val = j then c else 0)) v
  = c * v.nth i
:= begin
induction n; dsimp [vector.generate],
exfalso, apply fin.fin_0_empty, assumption,
have Hv := v.invert_succ,
induction Hv with x xs Hv, subst Hv,
rw dot_product_cons,
apply (if H : i.val = 0 then _ else _),
{ rw (if_pos H), rw (vector.nth_0 _ _ H),
  dsimp [function.comp],
  rw H,
  have Hf : (λ (x : ℕ), ite (0 = nat.succ x) c 0) = λ _, 0,
  apply funext; intros x,
  rw if_neg, intros contra, cases contra,
  rw Hf, clear Hf,
  rw dot_product_0, simp,
},
{ rw (if_neg H), simp,
  have H' : i ≠ 0,
  intros contra, apply H, rw contra, reflexivity,
  rw vector.nth_cons_nz _ H', dsimp [function.comp],
  rw ← ih_1, f_equal, f_equal,
  apply funext, intros n,
  f_equal, apply ite_iff,
  apply fin.succ_pred_equiv, }
end

lemma dot_product_scale_l {n : ℕ} (c : ℚ) (xs ys : vector ℚ n)
  : dot_product (vector.map (λ x, c * x) xs) ys
  = c * dot_product xs ys
:= begin
induction n,
{ rw (vector.eq_nil xs), rw (vector.eq_nil ys),
  rw vector.map_nil,
  rw dot_product_nil, simp, },
{ have Hx := xs.invert_succ, induction Hx with x xs' Hx, subst xs,
  have Hy := ys.invert_succ, induction Hy with y ys' Hy, subst ys,
  rw vector.map_cons, repeat { rw dot_product_cons },
  rw mul_add, rw ih_1, simp,
}
end

lemma dot_product_comm {n : ℕ} (x y : vector ℚ n)
  : dot_product x y = dot_product y x
:= begin
unfold dot_product,
rw vector.map₂_comm, apply mul_comm,
end

lemma dot_product_sum_r {n : ℕ} (x y z : vector ℚ n)
  : dot_product x (vector.map₂ (+) y z)
  = dot_product x y + dot_product x z
:= begin
induction n,
{ repeat {rw dot_product_0_len },
  rw add_zero, },
{ have Hx := x.invert_succ, induction Hx with x' xs Hx, subst x,
  have Hy := y.invert_succ, induction Hy with y' ys Hy, subst y,
  have Hz := z.invert_succ, induction Hz with z' zs Hz, subst z,
  rw vector.map₂_cons, repeat { rw dot_product_cons },
  rw ih_1, rw mul_add, simp,
}
end

lemma dot_product_sum_l {n : ℕ} (x y z : vector ℚ n)
  : dot_product (vector.map₂ (+) x y) z
  = dot_product x z + dot_product y z
:= begin
rw dot_product_comm, rw dot_product_sum_r,
rw dot_product_comm z x, rw dot_product_comm z y,
end