import data.rat
       galois.tactic
       .dense_linear_lemmas
       galois.list
       galois.list.fpow

universes u

namespace rat

def to_string (q:ℚ) : string :=
 if q.denom = 1 then
   to_string (q.num)
 else
   to_string (q.num) ++ "/" ++ to_string q.denom

instance : has_to_string ℚ := ⟨ to_string ⟩

end rat

structure vector_ind_succ {A : Type u} {n : ℕ} (xs : vector A n.succ)
  : Type u :=
  (head : A)
  (tail : vector A n)
  (equiv : xs = head :: tail)

namespace vector

def generate {A : Type _} : ∀ (n : ℕ) (f : ℕ → A),
  vector A n
| 0 _ := vector.nil
| (nat.succ n) f := f 0 :: generate n (f ∘ nat.succ)

def invert_succ {A : Type _} {n : ℕ} (xs : vector A n.succ)
  : vector_ind_succ xs
  := ⟨ xs.head, xs.tail, eq.symm (vector.cons_head_tail _) ⟩

end vector

-- denotes the inequality coef <= bound
structure linear_expr (n:ℕ) : Type :=
(coef : vector ℚ n)
(offset : ℚ)

namespace linear_expr

def to_string_core (off : ℚ) : ℕ → list ℚ → string
| _ [] := to_string off
| i (h::r) :=
 if h = 0 then
   to_string_core (i+1) r
 else
   let ppc (c : ℚ) (i:ℕ)  : string :=
        if c = 1 then
          "x" ++ to_string i
        else
          to_string c ++ "× x" ++ to_string i in
   let f (p:string × ℕ) (c : ℚ) : string × ℕ :=
         if c = 0 then
           (p.fst, p.snd + 1)
         else
           (p.fst ++ " " ++ ppc c p.snd, p.snd + 1) in
   (r.foldl f (ppc h (i+1), i+1)).fst ++ to_string off

def to_string {n:ℕ} (l : linear_expr n) : string :=
 to_string_core l.offset 0  l.coef.to_list

def var {n:ℕ} (c : ℚ) (i : fin n) : linear_expr n :=
 { coef := vector.generate n (λj, if i.val = j then c else 0)
 , offset := 0
 }

def const (n:ℕ) (c : ℚ) : linear_expr n :=
 { coef := vector.repeat 0 n
 , offset := c
 }

/-- Return the expression with the last variable removed and the coefficient. -/
def drop_head {n:ℕ} (e:linear_expr (n+1)) : linear_expr n :=
 { coef := e.coef.tail, offset := e.offset }

def instantiate_head {n : ℕ} (e : linear_expr (n + 1)) (c : ℚ) : linear_expr n :=
 { coef := e.coef.tail, offset := c * e.coef.head + e.offset}

def extend {n : ℕ} (x : ℚ) (e : linear_expr n) : linear_expr (n + 1)
  := ⟨ x :: e.coef , e.offset ⟩

def scale_mul {n:ℕ} (c:ℚ) (e:linear_expr n) : linear_expr n :=
 { coef := e.coef.map (λ x, c * x), offset := c * e.offset }

def add_expr {n:ℕ} (e e':linear_expr n) : linear_expr n :=
 { coef := vector.map₂ (+) e.coef e'.coef , offset := e.offset + e'.offset}


lemma vector.map₂_nil {A B C} (f : A → B → C)
  : vector.map₂ f vector.nil vector.nil = vector.nil
  := rfl

lemma vector.map₂_cons {A B C} (f : A → B → C)
  (a : A) (b : B) {n : ℕ} (as : vector A n) (bs : vector B n)
  : vector.map₂ f (a :: as) (b :: bs) = f a b :: vector.map₂ f as bs
:= begin
induction as, induction bs, reflexivity,
end

lemma instantiate_head_add_expr
  {n : ℕ} (e e' : linear_expr (n + 1)) (c : ℚ)
  : instantiate_head (add_expr e e') c
  = add_expr (instantiate_head e c) (instantiate_head e' c)
:= begin
induction e with e eoff,
induction e' with e' e'off,
dsimp [instantiate_head, add_expr],
have He := e.invert_succ, induction He with ehd etl eprf,
have He' := e'.invert_succ, induction He' with e'hd e'tl e'prf,
subst e, subst e',
f_equal,
{ rw vector.map₂_cons, repeat { rw vector.tail_cons }, },
{ rw vector.map₂_cons, repeat { rw vector.head_cons },
  rw mul_add, simp }
end


inductive bound_expr (n : ℕ)
| lower_bound : ℚ → linear_expr n → bound_expr
| upper_bound : ℚ → linear_expr n → bound_expr
| uninvolved  : linear_expr n → bound_expr

def combine {n : ℕ} (lb : ℚ) (lbe : linear_expr n) (ub : ℚ)
  (ube : linear_expr n) : linear_expr n
:= add_expr (scale_mul (-lb) ube) (scale_mul ub lbe)

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

lemma vector.generate_const_repeat {A} (n : ℕ) (c : A)
  : vector.generate n (λ _, c)
  = vector.repeat c n
:= begin
induction n; dsimp [vector.repeat, vector.generate],
reflexivity,
rw ih_1, reflexivity,
end

lemma vector.repeat_unfold {A} (n : ℕ) (x : A)
  : vector.repeat x n.succ = x :: vector.repeat x n
:= rfl

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

lemma vector.nth_cons_nz {A} {n : ℕ} (i : fin n.succ)
  (H : i ≠ 0)
  (x : A) (xs : vector A n)
  : vector.nth (x :: xs) i = vector.nth xs (fin.pred i H)
:= begin
induction xs, induction i,
dsimp [vector.cons, vector.nth, fin.pred],
have H : val_1 ≠ 0, intros contra,
apply H, unfold has_zero.zero, subst val_1,
cases val_1, contradiction,
dsimp [list.nth_le], reflexivity,
end

lemma vector.nth_cons_zero {A} {n : ℕ}
  (x : A) (xs : vector A n)
  : vector.nth (x :: xs) 0 = x
:= begin
apply vector.nth_0, reflexivity,
end

lemma succ_pred_equiv {k : ℕ} (i : fin k.succ)
  (H : i ≠ 0)
  (n : ℕ)
 : (i.val = nat.succ n) ↔ ((fin.pred i H).val = n)
:= begin
induction i, dsimp [fin.pred],
cases val, exfalso, apply H,
unfold has_zero.zero,
dsimp [nat.pred], split; intros H',
injection H', subst H',
end

lemma fin.val_inj {n : ℕ} (i j : fin n)
  (H : i.val = j.val) : i = j
:= begin
induction i, induction j, dsimp at H, induction H,
reflexivity,
end

lemma fin.succ_pred_id {k : ℕ} (i : fin k.succ)
  (H : i ≠ 0)
  : fin.succ (fin.pred i H) = i
:= begin
induction i,
dsimp [fin.pred, fin.succ],
cases val, exfalso, apply H, unfold has_zero.zero,
dsimp [nat.pred], reflexivity,
end

lemma vector.nth_of_fn {A} {n : ℕ} (f : fin n → A)
  (i : fin n)
  : vector.nth (vector.of_fn f) i = f i
:= begin
revert f i,
induction n; intros; dsimp [vector.of_fn],
{ exfalso, apply fin_0_empty, assumption, },
{ apply (if H : i = 0 then _ else _),
  { subst i, rw vector.nth_cons_zero, },
  { rw vector.nth_cons_nz, tactic.swap, assumption,
    rw ih_1, rw fin.succ_pred_id, }
}
end

lemma ite_iff {P Q : Prop}
  [decP : decidable P] [decQ : decidable Q]
  (H : P ↔ Q) {A}
  : @ite P _ A = ite Q
:= begin
apply funext, intros x, apply funext, intros y,
have decP' := decP,
cases decP' with HP HP, rw (if_neg HP),
rw if_neg, rw ← H, assumption,
rw (if_pos HP), rw if_pos, rw ← H, assumption,
end

lemma dot_product_unit (n : ℕ) (i : fin n) (c : ℚ) (v : vector ℚ n)
  : dot_product (vector.generate n (λj, if i.val = j then c else 0)) v
  = c * v.nth i
:= begin
induction n; dsimp [vector.generate],
exfalso, apply fin_0_empty, assumption,
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
  apply succ_pred_equiv, }
end

lemma vector.map₂_comm {A B} (f : A → A → B)
  (f_comm : ∀ x y, f x y = f y x)
  {n : ℕ} (xs ys : vector A n)
  : vector.map₂ f xs ys = vector.map₂ f ys xs
:= begin
induction n,
{ rw (vector.eq_nil xs), rw (vector.eq_nil ys), },
{ have Hx := xs.invert_succ, induction Hx with x xs' Hx, subst xs,
  have Hy := ys.invert_succ, induction Hy with y ys' Hy, subst ys,
  repeat { rw vector.map₂_cons }, rw f_comm,
  f_equal, apply ih_1,
}
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


def evaluate {n : ℕ} (e:linear_expr n) (a: vector ℚ n) : ℚ :=
dot_product e.coef a + e.offset

def satisfiable {n : ℕ} (es : list (linear_expr n))
  := ∃ (a : vector ℚ n), es.Forall (λ e, evaluate e a ≤ 0)

structure focused (n : ℕ) :=
  (lbs : list ({ q : ℚ // q < 0} × linear_expr n))
  (ubs : list ({ q : ℚ // q > 0} × linear_expr n))
  (uninvolved : list (linear_expr n))

def minimum_opt (default : ℚ) : list ℚ → ℚ
| [] := default
| (x :: xs) := list.foldr min x xs

def maximum_opt (default : ℚ) : list ℚ → ℚ
| [] := default
| (x :: xs) := list.foldr max x xs

lemma maximum_opt_in (default : ℚ)
  {x : ℚ} {xs : list ℚ} (H : x ∈ xs)
  : x ≤ maximum_opt default xs
:= begin
cases xs; dsimp [maximum_opt],
rw list.mem_nil_iff at H, contradiction,
induction a_1; dsimp [list.foldr],
dsimp [has_mem.mem, list.mem] at H,
cases H, subst a, contradiction,
dsimp [has_mem.mem, list.mem] at H,
induction H, subst a,
apply le_trans, tactic.swap, apply le_max_right,
apply ih_1, constructor, reflexivity,
induction a_3, subst a_1, apply le_max_left,
apply le_trans, tactic.swap, apply le_max_right,
apply ih_1, dsimp [has_mem.mem, list.mem], right,
assumption
end

lemma minimum_opt_in (default : ℚ)
  {x : ℚ} {xs : list ℚ} (H : x ∈ xs)
  : minimum_opt default xs ≤ x
:= begin
cases xs; dsimp [minimum_opt],
rw list.mem_nil_iff at H, contradiction,
induction a_1; dsimp [list.foldr],
dsimp [has_mem.mem, list.mem] at H,
cases H, subst a, contradiction,
dsimp [has_mem.mem, list.mem] at H,
induction H, subst a,
apply le_trans, apply min_le_right,
apply ih_1, constructor, reflexivity,
induction a_3, subst a_1, apply min_le_left,
apply le_trans, apply min_le_right,
apply ih_1, dsimp [has_mem.mem, list.mem], right,
assumption
end

def focused_soln_ub_map {n : ℕ} (soln : vector ℚ n)
  : { q : ℚ // q > 0} × linear_expr n → ℚ
| (ub, ube) := -ub.val⁻¹ * (dot_product (ube.coef) soln + ube.offset)

def focused_soln {n : ℕ} (prob : focused n)
  (soln : vector ℚ n)
  : ℚ
:= minimum_opt
   (maximum_opt 0
     (prob.lbs.map (λ p : { q : ℚ // q < 0} × linear_expr n,
     let (⟨ lb, _ ⟩, lbe) := p in
  (-lb⁻¹ * (dot_product (lbe.coef) soln + lbe.offset)))))
    $
   prob.ubs.map (focused_soln_ub_map soln)

lemma list.mem_map {A B} (f : A → B) (xs : list A)
  (x : A) (y : B) (H : f x = y)
  (H' : x ∈ xs)
  : y ∈ xs.map f
:= begin
subst H, apply list.mem_induction _ _ _ _ _ H'; intros,
left, reflexivity, right, assumption,
end

lemma focused_soln_ubs_empty {n : ℕ} (prob : focused n)
  (soln : vector ℚ n)
  (Hubs_empty : prob.ubs = [])
  {lb : _} {lbe : _} (Hlb : (lb, lbe) ∈ prob.lbs)
  : (-lb.val⁻¹ * (dot_product (lbe.coef) soln + lbe.offset)) ≤
    focused_soln prob soln
:= begin
unfold focused_soln, rw Hubs_empty,
dsimp [maximum_opt],
apply maximum_opt_in,
apply list.mem_map, tactic.swap, assumption,
induction lb, dsimp [focused_soln], reflexivity
end

lemma focused_soln_ubs_inhabited {n : ℕ} (prob : focused n)
  (soln : vector ℚ n)
  {ub : _} {ube : _}
  (Hubs_inh : (ub, ube) ∈ prob.ubs)
  : focused_soln prob soln ≤ (-ub.val⁻¹ * (dot_product (ube.coef) soln + ube.offset))
:= begin
unfold focused_soln,
apply minimum_opt_in,
apply list.mem_map, tactic.swap, assumption,
induction ub, dsimp [focused_soln], reflexivity
end

lemma Forall_equiv_list {A : Type _}
  (P : A → Prop) (xs ys : list A)
  (H : same_elements xs ys)
  : xs.Forall P ↔ ys.Forall P
:= begin
unfold same_elements at H,
repeat { rw list.Forall_mem_equiv },
split; intros H' x, rw ← H, apply H',
rw H, apply H',
end

def focused_linear_exprs {n : ℕ} (prob : focused n)
  : list (linear_expr (n + 1))
  :=    prob.lbs.map (λ p, extend p.fst.val p.snd)
     ++ prob.ubs.map (λ p, extend p.fst.val p.snd)
     ++ prob.uninvolved.map (extend 0)

def focused_satisfiable {n : ℕ} (prob : focused n)
  := satisfiable (focused_linear_exprs prob)

lemma gt_of_not_eq_lt
  {x : ℚ}
  (Heq : x ≠ 0) (Hlt : ¬ x < 0)
  : x > 0
:= begin
unfold gt,
rw lt_iff_not_ge,
intros contra,
apply Hlt,
intros contra, apply Heq,
rw le_antisymm_iff, split; assumption,
end

def focus_problem {n : ℕ} : list (linear_expr (n + 1))
  → focused n
| [] := ⟨ [], [], [] ⟩
| (e :: es) := let prob := focus_problem es in
  let x := e.coef.head in let rest := drop_head e in
  if Heq : x = 0
    then { prob with uninvolved := rest :: prob.uninvolved }
    else if Hlt : x < 0
      then { prob with lbs := (⟨ x, Hlt⟩ , rest) :: prob.lbs }
      else  { prob with ubs := (⟨ x, gt_of_not_eq_lt Heq Hlt⟩ , rest) :: prob.ubs }


lemma focus_problem_equiv {n : ℕ}
  (xs : list (linear_expr (n + 1)))
  : same_elements xs (focused_linear_exprs (focus_problem xs))
:= begin
induction xs; dsimp [focus_problem, focused_linear_exprs],
case list.nil
{ apply same_elements_refl },
case list.cons x xs IH
{ induction x with xcoef xoffset,
  have Hx := xcoef.invert_succ, induction Hx with c cs Hcs, subst xcoef,
  dsimp [drop_head],
  simp only [vector.head_cons, vector.tail_cons],
  dsimp,
  apply (if Heq : vector.head (c :: cs) = 0 then _ else _),
  { rw (dif_pos Heq), dsimp, rw list.append_assoc,
    apply same_elements_trans, tactic.swap,
    apply same_elements_app_comm,
    apply same_elements_trans, tactic.swap,
    apply same_elements_app,
    apply same_elements_app_comm, apply same_elements_refl,
    dsimp [list.append],
    rw list.append_assoc,
    dsimp [list.append],
    apply cons_same, dsimp [extend],
    rw vector.head_cons at Heq, subst c,
    apply same_elements_trans, apply IH,
    dsimp [focus_problem, focused_linear_exprs],
    apply same_elements_trans,
    apply same_elements_app_comm,
    apply same_elements_app, apply same_elements_refl,
    apply same_elements_app_comm,
  },
  { rw (dif_neg Heq),
    apply (if Hlt : vector.head (c :: cs) < 0 then _ else _),
    { rw (dif_pos Hlt), dsimp,
      apply cons_same, reflexivity,
      apply IH, },
    { rw (dif_neg Hlt), dsimp,
      rw list.append_assoc,
      apply same_elements_trans, tactic.swap,
      apply same_elements_app_comm,
      rw list.append_assoc,
      dsimp [list.append],
      apply cons_same, reflexivity,
      apply same_elements_trans, assumption, clear IH,
      dsimp [focus_problem, focused_linear_exprs],
      apply same_elements_trans,
      rw list.append_assoc,
      apply same_elements_app_comm,
      rw list.append_assoc,
      apply same_elements_refl,
     }
  }
}
end

lemma same_elements_satisfiable {n : ℕ}
  {xs ys : list (linear_expr n)}
  (H : same_elements xs ys)
  : satisfiable xs ↔ satisfiable ys
:= begin
split; intros H'; induction H' with a Ha;
  existsi a, rw Forall_equiv_list, assumption,
  apply same_elements_symm, assumption,
  rw Forall_equiv_list, assumption, assumption,
end

def bounds_list {n : ℕ} (prob : focused n)
  : list (linear_expr n)
:= do (lb, lbe) ← prob.lbs, (ub, ube) ← prob.ubs,
       return (combine lb.val lbe ub.val ube)

def eliminate_aux {n : ℕ} (prob : focused n)
  : list (linear_expr n)
:= bounds_list prob ++ prob.uninvolved

def eliminate {n : ℕ} (es : list (linear_expr (n + 1)))
  : list (linear_expr n)
:= eliminate_aux (focus_problem es)

lemma add_zero_l (n : ℚ) : 0 + n = n
:= by simp

lemma evaluate_extend {n : ℕ} (x : linear_expr n)
  (c q : ℚ) (cs : vector ℚ n)
  : evaluate (extend q x) (c :: cs) = q * c + evaluate x cs
:= begin
dsimp [evaluate, extend],
rw dot_product_cons,
rw add_assoc,
end

lemma evaluate_extend_zero {n : ℕ} (x : linear_expr n)
  (c : ℚ) (cs : vector ℚ n)
  : evaluate (extend 0 x) (c :: cs) = evaluate x cs
:= begin
rw evaluate_extend,
rw mul_comm, rw mul_zero,
rw add_zero_l,
end

lemma list.mem_bind {A B} (xs : list A) (f : A → list B)
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

lemma list.mem_bind_iff {A B} (xs : list A) (f : A → list B)
  (y : B)
  : y ∈ xs >>= f
  ↔ ∃ x : A, x ∈ xs ∧ y ∈ f x
:= begin
split; intros H, apply list.mem_bind, assumption,
induction H with x Hx, induction Hx with H1 H2,
dsimp [(>>=), list.bind, list.join],
induction xs; dsimp [list.map, list.join],
rw list.mem_nil_iff at H1, contradiction,
rw list.mem_append, dsimp [has_mem.mem, list.mem] at H1,
induction H1 with H1 H1, subst a,
left, assumption, right, apply ih_1, assumption,
end

lemma list.mem_singleton {A} (x y : A)
  : x ∈ [y] ↔ x = y
:= begin
split; intros H, apply_in H list.eq_or_mem_of_mem_cons,
induction H with H H, assumption, cases H,
constructor, assumption,
end

def minimal_list {A} (xs : list A) (f : A → ℚ)
  (H : xs ≠ [])
  : ∃ x : A, x ∈ xs ∧ (∀ y : A, y ∈ xs → f x ≤ f y)
:= begin
cases xs, contradiction,
rename a x, rename a_1 xs, clear H,
induction xs,
{ existsi x, split, constructor, reflexivity,
  intros y Hy, dsimp [has_mem.mem, list.mem] at Hy,
  cases Hy, subst y, contradiction, },
{ induction ih_1 with x' Hx', induction Hx' with H H',
  apply (if Hxa : f x' ≤ f a then _ else _),
  { existsi x', split,
    dsimp [has_mem.mem, list.mem] at H, cases H,
    subst x, left, reflexivity, right, right, assumption,
    intros y Hy, dsimp [has_mem.mem, list.mem] at Hy,
    cases Hy, subst y,
    dsimp [has_mem.mem, list.mem] at H, cases H,
    subst x', apply H', left, reflexivity,
    cases a_2, subst a, assumption, apply H',
    right, assumption,
   },
  { existsi a, split, right, left, reflexivity,
    have Hax : f a ≤ f x',
    cases (rat.le_total (f a) (f x')), assumption, contradiction,
    clear Hxa,
    intros y Hy, dsimp [has_mem.mem, list.mem] at Hy,
    cases Hy, subst y,  dsimp [has_mem.mem, list.mem] at H,
    cases H, subst x', assumption,
    apply le_trans, assumption, apply H', left, reflexivity,
    cases a_2, subst a, apply le_trans, assumption,
    apply H', right, assumption,
   }
 }
end

def minimal_list_opt {A} (xs : list A) (default : ℚ) (f : A → ℚ)
  (H : xs ≠ [])
  : ∃ x : A, x ∈ xs ∧ f x = minimum_opt default (xs.map f)
:= begin
have H' := minimal_list xs f H,
induction H' with x Hx, induction Hx with H1 H2,
existsi x, split, assumption,
cases xs, rw list.mem_nil_iff at H1, contradiction,
clear H, rename a y, rename a_1 ys,
rw le_antisymm_iff, split,
{ dsimp [minimum_opt, list.map], clear H1,
  revert x y,
  induction ys; intros,
  dsimp [list.foldr, list.map], apply H2, left, reflexivity,
  dsimp [list.foldr, list.map],
  apply le_min, apply H2, right, left, reflexivity,
  apply ih_1, intros, apply H2,
  dsimp [has_mem.mem, list.mem] at a_2,
  induction a_2 with H H, left, assumption,
  right, right, assumption,
 },
{ apply minimum_opt_in,
  apply list.mem_map, reflexivity, assumption,
}
end

lemma id_rhs_list {A} (x : A) :
  id_rhs (list A) (return x) = [x] := rfl


lemma mul_le_zero_pos (c x : ℚ) (Hc : 0 < c)
  : x ≤ 0 ↔ c * x ≤ 0
:= begin
split; intros H,
{ apply mul_nonpos_of_nonneg_of_nonpos,
  apply le_of_lt, assumption, assumption, },
{ apply nonpos_of_mul_nonpos_left; assumption, }
end

lemma lt_zero_neg (c : ℚ)
  : c < 0 ↔ - c > 0
:= begin
split; intros H,
{ rw ← neg_zero,
  apply neg_lt_neg _, assumption, },
{ rw ← neg_zero,
  rw ← (neg_neg c),
  apply neg_lt_neg _, assumption }
end

lemma mul_le_zero_neg (c x : ℚ) (Hc : c < 0)
  : x ≤ 0 ↔ c * x ≥ 0
:= begin
split; intros H,
{ apply mul_nonneg_of_nonpos_of_nonpos,
  apply le_of_lt, assumption, assumption, },
{ apply nonpos_of_mul_nonpos_left, tactic.swap,
  rw lt_zero_neg at Hc, apply Hc,
  rw ← neg_mul_eq_neg_mul,
  apply neg_le_of_neg_le, rw neg_zero, assumption,
 }
end

lemma mul_le_zero_neg_le (c x : ℚ) (Hc : c < 0)
  : x ≤ 0 ↔ 0 ≤ c * x
:= mul_le_zero_neg c x Hc

lemma neg_le_neg_opp (x y : ℚ)
  : - y ≤ - x → x ≤ y
:= begin
intros H, rw ← (neg_neg x), rw ← (neg_neg y),
apply neg_le_neg, assumption,
end

lemma add_reassoc (lb ub : ℚ) (ube1 ube2 lbe1 lbe2 : ℚ)
  : lb * ube1 + ub * lbe1 + (lb * ube2 + ub * lbe2)
  = lb * (ube1 + ube2) + ub * (lbe1 + lbe2)
:= begin
repeat { rw mul_add }, simp,
end

lemma add_neg_le_r (x y : ℚ)
  : x + y ≥ 0 ↔ x ≥ - y
:= begin
dsimp [ge],
split; intros H,
{ apply (@le_of_add_le_add_left _ _ y),
  rw add_comm y,
  rw neg_add_self, rw add_comm, assumption, },
{ apply @le_of_add_le_add_left _ _ (-y),
  rw add_zero, rw add_comm, rw add_assoc,
  rw add_comm y, rw neg_add_self,
  rw add_zero, assumption,
}
end

lemma add_neg_le_l (x y : ℚ)
  : x + y ≤ 0 ↔ x ≤ - y
:= begin
split; intros H,
{ apply (@le_of_add_le_add_left _ _ y),
  rw add_comm _ (-y),
  rw neg_add_self, rw add_comm, assumption, },
{ apply @le_of_add_le_add_left _ _ (-y),
  rw add_zero, rw add_comm, rw add_assoc,
  rw add_comm y, rw neg_add_self,
  rw add_zero, assumption,
}
end

lemma add_le_zero1 (x y : ℚ)
  : 0 ≤ y - x ↔ x ≤ y
:= begin
split; intros H,
{ rw ← (add_zero x), apply le_trans,
  apply add_le_add_left, assumption,
  rw ← add_sub_assoc, rw add_comm,
  rw add_sub_cancel, },
{ apply le_trans, tactic.swap, apply add_le_add_right,
  assumption, rw add_comm, rw neg_add_self }
end

lemma add_le_zero2 (x y : ℚ)
  : x - y ≤ 0 ↔ x ≤ y
:= begin
rw ← add_le_zero1,
rw sub_eq_add_neg,
rw neg_sub, rw add_zero_l,
rw add_le_zero1,
end

lemma mul_le_mono_neg (c x y : ℚ) (Hc : c < 0)
  (H : x ≤ y) : c * y ≤ c * x
:= begin
rw ← add_le_zero1, rw ← mul_sub,
rw ← mul_le_zero_neg_le, rw add_le_zero2, assumption,
assumption,
end

lemma mul_le_mono_pos (c x y : ℚ) (Hc : c > 0)
  (H : x ≤ y) : c * x ≤ c * y
:= begin
rw ← add_le_zero1, rw ← mul_sub,
apply mul_nonneg, apply le_of_lt, assumption,
unfold ge, rw add_le_zero1, assumption,
end

lemma eliminate_aux_combine_sat {n : ℕ}
  (c : ℚ)
  (cs : vector ℚ n)
  (lbe ube : linear_expr n)
  (lb : ℚ)
  (lblt0 : lb < 0)
  (ub : ℚ)
  (ubgt0 : ub > 0)
  (H1 : evaluate (extend lb lbe) (c :: cs) ≤ 0)
  (H2 : evaluate (extend ub ube) (c :: cs) ≤ 0)
  : evaluate (combine lb lbe ub ube) cs ≤ 0
:= begin
  dsimp [evaluate] at *,
  dsimp [combine, add_expr, scale_mul],
  dsimp [extend] at H1 H2,
  rw dot_product_cons at H1 H2,
  rw dot_product_sum_l,
  repeat { rw dot_product_scale_l },
  rw (mul_le_zero_neg _ _ lblt0) at H2,
  rw (mul_le_zero_pos _ _ ubgt0) at H1,
  rw add_assoc at H1 H2,
  rw mul_add at H1 H2,
  rw add_reassoc,
  rw add_neg_le_r at H2,
  rw add_neg_le_l at H1,
  rw ← mul_assoc at H1 H2,
  rw mul_comm ub at H1,
  rw add_neg_le_l,
  rw ← neg_mul_eq_neg_mul,
  apply le_trans, apply H2, apply H1,
end

lemma rat.inv_pos (x : ℚ) (Hx : 0 < x) : 0 < x⁻¹
:= begin
have H : 0 < x * x⁻¹,
rw mul_inv_cancel, exact_dec_trivial,
apply ne_of_gt, assumption,
have H' := pos_and_pos_or_neg_and_neg_of_mul_pos H,
induction H' with H' H'; induction H' with H1 H2, assumption,
exfalso, clear H H2,
rw lt_iff_not_ge at Hx, apply Hx,
apply le_of_lt, assumption,
end

lemma eliminate_aux_preserves_sat {n : ℕ} (prob : focused n)
  : focused_satisfiable prob
  ↔ satisfiable (eliminate_aux prob)
:= begin
split; intros H,
{ induction H with a Ha,
  unfold satisfiable,
  have Hx := a.invert_succ, induction Hx with c cs Hcs, subst a,
  existsi cs,
  unfold eliminate_aux,
  unfold focused_linear_exprs at Ha,
  rw list.Forall_app_iff at Ha,
  induction Ha with H1 H3,
  rw list.Forall_app_iff at H1,
  induction H1 with H1 H2,
  rw list.map_Forall_iff at H3 H2 H1,
  apply list.concat_Forall,
  { clear H3,
    rw list.Forall_mem_equiv at H2 H1,
    rw list.Forall_mem_equiv,
    intros x Hx,
    apply_in Hx list.mem_bind,
    induction Hx with lbp Hx,
    induction Hx with HA HB,
    specialize (H1 lbp HA),
    induction lbp with lb lbe,
    dsimp [bounds_list] at HB,
    apply_in HB list.mem_bind,
    induction HB with ubp HB,
    induction HB with HB HC,
    specialize (H2 ubp HB),
    induction ubp with ub ube,
    dsimp at HC,
    rw id_rhs_list at HC,
    induction lb with lb lblt0,
    rw list.mem_singleton at HC,
    subst x,
    induction ub with ub ubgt0,
    dsimp at H2 H1,
    dsimp,
    apply eliminate_aux_combine_sat; assumption,
    },
  { apply list.impl_Forall, assumption,
    intros x He,
    rw evaluate_extend_zero at He, assumption }
},
{ unfold focused_satisfiable,
  induction H with a Ha,
  unfold satisfiable,
  existsi (focused_soln prob a :: a),
  unfold focused_linear_exprs,
  unfold eliminate_aux at Ha,
  rw list.Forall_app_iff at Ha,
  induction Ha with H1 H2,
  repeat { apply list.concat_Forall };
    apply list.map_Forall,
  { clear H2,
    rw list.Forall_mem_equiv,
    intros x xlbs, induction x with lb lbe,
    dsimp,
    rw evaluate_extend,
    destruct (prob.ubs),
    { intros Hnil,
      have H := focused_soln_ubs_empty prob a Hnil xlbs,
      apply le_trans, apply add_le_add,
      apply mul_le_mono_neg, apply lb.property,
      assumption, apply le_refl,
      rw ← mul_assoc, rw ← neg_mul_eq_mul_neg,
      rw mul_inv_cancel, rw ← neg_mul_eq_neg_mul,
      rw [mul_comm, mul_one],
      unfold evaluate,
      rw neg_add_self, apply ne_of_lt, apply lb.property,
    },
    { intros ub ubs Hubs, rw list.Forall_mem_equiv at H1,
      have Hubs' : prob.ubs ≠ [],
      rw Hubs, contradiction, clear Hubs ubs ub,
      have Hubs := minimal_list_opt _ _ (focused_soln_ub_map a) Hubs',
      induction Hubs with ub Hub, induction Hub with Hub Hub',
      induction ub with ub ube,
      -- NO! The following line is a mistake. I should use the
      -- "minimal" (- ube / ub)
      specialize (H1 (combine lb.val lbe ub.val ube)),
      have H2 : combine (lb.val) lbe (ub.val) ube ∈ bounds_list prob,
      unfold bounds_list,
      rw list.mem_bind_iff,
      existsi (lb, lbe), split, assumption,
      dsimp [bounds_list], rw list.mem_bind_iff,
      existsi (ub, ube), split, assumption,
      dsimp [bounds_list], constructor, reflexivity,
      specialize (H1 H2), clear H2,
      dsimp [evaluate, combine, add_expr, scale_mul] at H1,
      rw dot_product_sum_l at H1,
      repeat { rw dot_product_scale_l at H1 },
      rw add_reassoc at H1,
      have Hubinv : ub.val⁻¹ > 0,
      apply rat.inv_pos, apply ub.property,
      rw (mul_le_zero_pos _ _ Hubinv) at H1,
      rw mul_add at H1,
      rw ← mul_assoc _ ub.val at H1,
      rw [mul_comm _ ub.val, mul_inv_cancel] at H1,
      rw mul_comm (1 : ℚ) at H1, rw mul_one at H1,
      apply le_trans, tactic.swap, apply H1,
      apply add_le_add_right,
      have Hub : (ub, ube) ∈ prob.ubs, assumption,
      unfold focused_soln, rw ← Hub',
      dsimp [focused_soln_ub_map], simp,
      apply ne_of_gt, apply ub.property,
    }
  },
  { clear H2,
    rw list.Forall_mem_equiv,
    intros x xubs, induction x with ub ube,
    dsimp,
    rw evaluate_extend,
    apply_in xubs (focused_soln_ubs_inhabited prob a),
    apply le_trans, apply add_le_add_right,
    apply mul_le_mono_pos, apply ub.property,
    assumption, rw ← mul_assoc,
    rw ← neg_mul_eq_mul_neg, rw mul_inv_cancel,
    rw ← neg_mul_eq_neg_mul, rw [mul_comm, mul_one],
    unfold evaluate,
    rw neg_add_self, apply ne_of_gt, apply ub.property,
  },
  { apply list.impl_Forall, assumption,
    intros x He,
    rw evaluate_extend_zero, assumption }
   }
end

lemma satsfiable_elim {n : ℕ} (lb : ℚ)
  (lblt0 : lb < 0)
  (lbe : linear_expr n) (ub : ℚ)
  (ubgt0 : 0 < ub)
  (ube : linear_expr n)
  : satisfiable [⟨ lb :: lbe.coef, lbe.offset ⟩,⟨ ub :: ube.coef, ube.offset ⟩ ]
  ↔ satisfiable [combine lb lbe ub ube]
:= begin
split; intros H,
{ dsimp [satisfiable] at H, induction H with a Ha,
  cases Ha,
  case list.Forall.cons H1 H2 { cases H2, clear H2,
  case list.Forall.cons H2 H3 { clear H3,
  have Ha := a.invert_succ,
  induction Ha with x xs Ha, subst a,
  existsi xs, constructor,
  any_goals { constructor },
  apply eliminate_aux_combine_sat; assumption,
  } }
 },
{ dsimp [satisfiable] at H, induction H with a Ha,
  cases Ha,
  case list.Forall.cons H1 H2 { clear Ha H2,
  dsimp [satisfiable],
  dsimp [evaluate] at *,
  existsi ( (-ub⁻¹ * (dot_product (ube.coef) a + ube.offset)) :: a),
  rw dot_product_sum_l at H1,
  dsimp [scale_mul] at H1,
  repeat {rw dot_product_scale_l at H1},
  rw add_reassoc at H1,
  constructor,
  { dsimp,
    rw dot_product_cons,
    rw (mul_le_zero_pos _ _ ubgt0),
    rw add_assoc,
    rw mul_add,
    rw ← mul_assoc,
    rw mul_comm ub,
    rw ← mul_assoc,
    rw mul_assoc lb,
    rw ← neg_mul_eq_mul_neg,
    rw mul_inv_cancel,
    rw ← neg_mul_eq_mul_neg,
    rw mul_one, assumption,
    apply ne_of_gt, assumption,
  },
  { constructor, any_goals { constructor },
    dsimp,
    rw dot_product_cons,
    rw ← neg_mul_eq_neg_mul,
    rw ← neg_mul_eq_mul_neg,
    rw ← mul_assoc,
    rw mul_inv_cancel, rw mul_comm,
    rw mul_one, rw add_assoc, rw neg_add_self,
    apply ne_of_gt, assumption, }
}
}
end

theorem satsfiable_eliminate {n : ℕ}
  (xs : list (linear_expr (n + 1)))
  : satisfiable xs
  ↔ satisfiable (eliminate xs)
:= begin
unfold eliminate,
rw ← eliminate_aux_preserves_sat,
apply same_elements_satisfiable,
apply focus_problem_equiv,
end

lemma vector_nil_exists
  {A : Type _}
  (P : vector A 0 → Prop)
  : Exists P ↔ P vector.nil
:= begin
split; intros, induction a,
rw ← (vector.eq_nil a), assumption,
constructor, assumption
end

def satisfiable_constant_dec
  (xs : list (linear_expr 0))
  : decidable (satisfiable xs)
:= begin
unfold satisfiable,
rw vector_nil_exists,
apply_instance,
end

def eval_no_vars (e : linear_expr 0) : ℚ
  := e.evaluate vector.nil

def eliminate_all : ∀ {n : ℕ},
  list (linear_expr n) → list (linear_expr 0)
| 0 xs := xs
| (nat.succ n) xs := eliminate_all (eliminate xs)

lemma eliminate_all_equiv {n : ℕ}
  (xs : list (linear_expr n))
  : satisfiable xs ↔ satisfiable (eliminate_all xs)
:= begin
induction n; dsimp [eliminate_all],
trivial, rw satsfiable_eliminate, apply ih_1,
end

instance satisfiable_dec {n : ℕ}
  (xs : list (linear_expr n))
  : decidable (satisfiable xs)
:= begin
rw eliminate_all_equiv, apply satisfiable_constant_dec,
end

def satisfiable_bool {n : ℕ}
  (xs : list (linear_expr n))
  : bool
:= decidable.to_bool (satisfiable xs)

def satisfiable_bool' {n : ℕ}
  (xs : list (linear_expr n))
  : bool
:= list.band ((eliminate_all xs).map (λ e, e.evaluate vector.nil ≤ 0))

lemma decidable.to_bool_equiv {P Q : Prop}
  [decP : decidable P] [decQ : decidable Q]
  (H : P ↔ Q)
  : decidable.to_bool P = decidable.to_bool Q
:= begin
dsimp [decidable.to_bool],
induction decP; induction decQ;
try { reflexivity }; exfalso,
apply a, rw H, assumption,
apply a_1, rw ← H, assumption,
end

lemma band_tt_left (b : bool) : tt && b = b
:= begin
induction b; reflexivity
end

lemma to_bool_Forall {A} (xs : list A) (P : A → Prop) [decidable_pred P] :
  to_bool (list.Forall P xs) = list.band (xs.map (λ x, to_bool (P x)))
:= begin
unfold to_bool,
cases (list.Forall_decidable P xs) with no yes,
{ induction xs; dsimp [list.band, list.all],
  exfalso, apply no, constructor,
  cases (_inst_1 a); dsimp, reflexivity,
  rw band_tt_left, apply ih_1, intros contra,
  apply no, constructor; assumption },
{ dsimp, induction xs; dsimp [list.band, list.all],
  reflexivity,
  apply_in yes list.Forall_invert, dsimp at yes, induction yes with yes yes',
  cases (_inst_1 a); dsimp,
  contradiction, rw band_tt_left, apply ih_1, assumption,
}
end

lemma satisfiable_bool_equiv {n : ℕ} (xs : list (linear_expr n))
  : satisfiable_bool xs = satisfiable_bool' xs
:= begin
unfold satisfiable_bool satisfiable_bool',
rw (decidable.to_bool_equiv (eliminate_all_equiv _)),
unfold satisfiable,
rw (decidable.to_bool_equiv (vector_nil_exists _)),
apply to_bool_Forall, apply_instance,
end

inductive aexpr (vTy : Type) : Type
| var {} : ℚ → vTy → aexpr
| const {} : ℚ → aexpr
| add {} : aexpr → aexpr → aexpr

inductive eqn (vTy : Type) : Type
| le {} : aexpr vTy → aexpr vTy → eqn

lemma var_offset_0
  {n : ℕ} (c : ℚ) (i : fin n)
  : (linear_expr.var c i).offset = 0
  := rfl

lemma var_evaluate {n : ℕ} (c : ℚ) (i : fin n) (x : vector ℚ n) :
  (var c i).evaluate x = c * x.nth i
:= begin
dsimp [evaluate, var],
rw add_zero,
rw dot_product_unit,
end

namespace aexpr
def interp {vTy : Type} (ctxt : vTy → ℚ)
  : aexpr vTy → ℚ
| (var c x) := c * ctxt x
| (const q) := q
| (add x y) := interp x + interp y

def to_linear_expr {n : ℕ}
  : aexpr (fin n) → linear_expr n
| (var c x) := linear_expr.var c x
| (const q) := linear_expr.const _ q
| (add x y) := add_expr (to_linear_expr x) (to_linear_expr y)

def var_map {vTy vTy' : Type} (f : vTy → vTy')
  : aexpr vTy → aexpr vTy'
| (var c x) := var c (f x)
| (const q) := const q
| (add x y) := add (var_map x) (var_map y)

def var_map_default {vTy vTy' : Type} (f : vTy → option vTy')
  (default : ℚ)
  : aexpr vTy → aexpr vTy'
| (var c x) := match f x with
   | some y := var c y
   | none := const default
   end
| (const q) := const q
| (add x y) := add (var_map_default x) (var_map_default y)

def list.nth_def {α : Type u} (xs : list α) (default : α) (n : ℕ) : α
:= match xs.nth n with
| (some x) := x
| none := default
end

lemma to_linear_expr_sound {n : ℕ}
  (e : aexpr (fin n))
  (ctxt : fin n → ℚ)
  : e.interp ctxt = e.to_linear_expr.evaluate (vector.of_fn ctxt)
:= begin
induction e; dsimp [interp, to_linear_expr],
case var c i
{ rw var_evaluate, rw vector.nth_of_fn, },
{ unfold evaluate, dsimp [linear_expr.const],
  rw ← vector.generate_const_repeat,
  rw dot_product_0, simp,
},
{ rw [ih_1, ih_2],
  dsimp [evaluate, linear_expr.add_expr],
  rw dot_product_sum_l, simp,
}
end
end aexpr

namespace eqn
def interp {vTy : Type} (ctxt : vTy → ℚ)
  : eqn vTy → Prop
| (le e e') := e.interp ctxt ≤ e'.interp ctxt
end eqn


def nat_to_fin_option (k n : ℕ) : option (fin k)
  := if H : n < k then some ⟨ _, H ⟩ else none

namespace aexpr
def interp_expr_context (hyp : aexpr ℕ)
  (n : ℕ) : linear_expr n
  := (aexpr.var_map_default (nat_to_fin_option _) 0 hyp).to_linear_expr
def instantiate_head (c' : ℚ) : aexpr ℕ → aexpr ℕ
| (var c n) := match n with
  | 0 := const (c * c')
  | (nat.succ n') := var c n'
  end
| (const q) := const q
| (add x y) := add (instantiate_head x) (instantiate_head y)

def no_big_vars_bool (nvars : ℕ) : aexpr ℕ → bool
| (var c x) := decidable.to_bool (x < nvars)
| (const q) := tt
| (add x y) := band (no_big_vars_bool x) (no_big_vars_bool y)

def no_big_vars (nvars : ℕ) : aexpr ℕ → Prop
| (var c x) := x < nvars
| (const q) := true
| (add x y) := no_big_vars x ∧ no_big_vars y

instance no_big_vars_decidable (nvars : ℕ)
  : decidable_pred (no_big_vars nvars)
:= begin
intros x, induction x; dsimp [no_big_vars]; apply_instance,
end

lemma to_bool_and (P Q : Prop) [decP : decidable P]
  [decQ : decidable Q]
  : to_bool P && to_bool Q = to_bool (P ∧ Q)
:= begin
unfold to_bool, cases (@and.decidable _ _ decP decQ) with H H;
cases decP with HP HP; cases decQ with HQ HQ;
dsimp;
try {reflexivity}; exfalso, apply H, split; assumption,
{ induction H with H H', apply HP, assumption },
{ induction H with H H', apply HP, assumption },
{ induction H with H H', apply HQ, assumption },
end

lemma no_big_vars_equiv (nvars : ℕ)
  : no_big_vars_bool nvars = λ e, to_bool (no_big_vars nvars e)
:= begin
apply funext; intros e,
induction e; dsimp [no_big_vars, no_big_vars_bool],
reflexivity, rw to_bool_tt, trivial,
rw [ih_1, ih_2], rw to_bool_and,
end

end aexpr

def interp_list_exprs (hyps : list (aexpr ℕ))
  (n : ℕ) : list (linear_expr n)
:= hyps.map (λ hyp : aexpr ℕ, hyp.interp_expr_context n)

end linear_expr

open linear_expr

def linear_expr_negation_statement_0
  : list (linear_expr 0) → Prop
| [] := false
| (e :: es) := e.evaluate vector.nil ≤ 0 → linear_expr_negation_statement_0 es

def linear_expr_negation_statement :
  ∀ {n : ℕ}, list (linear_expr n) → Prop
| 0 := linear_expr_negation_statement_0
| (nat.succ n) := λ es, ∀ x : ℚ, linear_expr_negation_statement
    (es.map (λ e, e.instantiate_head x))

def aexpr_negation_statement_0
  : list (aexpr ℕ) → Prop
| [] := false
| (e :: es) := e.interp (λ _, 0) ≤ 0 → aexpr_negation_statement_0 es

def aexpr_negation_statement :
  ∀ nvars : ℕ, list (aexpr ℕ) → Prop
| 0 := aexpr_negation_statement_0
| (nat.succ n) := λ es, ∀ x : ℚ, aexpr_negation_statement n
    (es.map (λ e, e.instantiate_head x))

lemma satisfiable_bool_correct_linear {n : ℕ} (e : list (linear_expr n))
  : satisfiable_bool' e = ff →
    linear_expr_negation_statement e
:= begin
rw ← satisfiable_bool_equiv,
unfold satisfiable_bool,
rw to_bool_ff_iff,
intros H,
revert e,
induction n; intros; dsimp [linear_expr_negation_statement],
{ induction e; dsimp [linear_expr_negation_statement],
  { exfalso, apply H, unfold satisfiable,
    rw vector_nil_exists, constructor,
  },
  { intros H', apply ih_1, intros contra,
    apply H, unfold satisfiable at contra,
    rw vector_nil_exists at contra,
    unfold satisfiable,
    rw vector_nil_exists, constructor;
    assumption, }
},
{ intros x, apply ih_1, intros contra, apply H,
  induction contra with asn Hasn,
  existsi (x :: asn), rw list.map_Forall_iff at Hasn,
  apply list.impl_Forall, assumption,
  intros expr H, dsimp [evaluate, instantiate_head] at H,
  dsimp [evaluate],
  apply le_trans, tactic.swap, apply H_1,
  rw ← add_assoc, apply add_le_add, clear H_1,
  generalize Hys : expr.coef = ys,
  have Hys' := ys.invert_succ, induction Hys',
  rw equiv, rw dot_product_cons,
  rw vector.tail_cons, rw vector.head_cons, simp,
  apply le_refl,
}
end

lemma to_bool_tt_iff (P : Prop) [decP : decidable P]
  : to_bool P = tt ↔ P
:= begin
unfold to_bool, cases decP; dsimp,
split; intros; contradiction,
split; intros H, assumption, reflexivity,
end

lemma vector_nil_of_fn {A} : @vector.nil A = vector.of_fn (begin
  intros i, exfalso, apply fin_0_empty, assumption,
  end)
:= eq.symm (vector.eq_nil _)

lemma  no_vars_nil_interp (e : aexpr ℕ)
  (H : e.no_big_vars 0)
  : e.interp (λ _, 0) = evaluate (e.interp_expr_context 0) vector.nil
:= begin
dsimp [aexpr.interp_expr_context],
rw vector_nil_of_fn,
rw ← aexpr.to_linear_expr_sound,
induction e; dsimp [aexpr.interp, aexpr.var_map_default];
  dsimp [aexpr.no_big_vars] at H,
{ exfalso, apply nat.not_lt_zero, assumption },
{ reflexivity },
{ induction H with H1 H2,
  specialize (ih_1 H1), specialize (ih_2 H2),
  rw [ih_1, ih_2], }
end

lemma no_big_vars_instantiate_head {n : ℕ} {e : aexpr ℕ} (x : ℚ)
  : aexpr.no_big_vars (nat.succ n) e
  → (e.instantiate_head x).no_big_vars n
:= begin
induction e with;
  dsimp [aexpr.no_big_vars, aexpr.instantiate_head];
  intros H,
{ induction a_1; dsimp [aexpr.instantiate_head, aexpr.no_big_vars],
  { constructor },
  { rw ← nat.succ_lt_succ_iff, assumption }
},
{ assumption },
{ induction H with H1 H2,
  split, apply ih_1, assumption, apply ih_2, assumption,
}
end

lemma nat_to_fin_option_pred_none {n i : ℕ}
  : nat_to_fin_option n.succ i.succ = none
  → nat_to_fin_option n i = none
:= begin
unfold nat_to_fin_option,
apply (if Hlt : i.succ < n.succ then _ else _),
{ rw (dif_pos Hlt), intros H,
  contradiction,
},
{ rw (dif_neg Hlt), intros H', clear H',
  have H : ¬ (i < n),
  intros contra, apply Hlt,
  apply nat.succ_lt_succ, assumption,
  rw (dif_neg H),
}
end

lemma nat_to_fin_option_succ_nz {n k : ℕ} {i : fin n.succ}
  : nat_to_fin_option n.succ k.succ = some i
  → i ≠ 0
:= begin
dsimp [nat_to_fin_option],
apply (if H : (nat.succ k < nat.succ n) then _ else _),
{ rw (dif_pos H), intros H', injection H' with H'', clear H',
  intros contra, subst i, injection contra,
  injection h,
},
{ rw (dif_neg H), intros contra, contradiction, }
end

lemma nat_to_fin_option_pred_some {n k : ℕ} (i : fin n.succ)
  : ∀ H : nat_to_fin_option n.succ k.succ = some i
  , nat_to_fin_option n k = some (i.pred (nat_to_fin_option_succ_nz H))
:= begin
dsimp [nat_to_fin_option],
intros H,
apply (if H' : (nat.succ k < nat.succ n) then _ else _),
{ rw (dif_pos H') at H, injection H with H2, clear H,
  rw nat.succ_lt_succ_iff at H',
  rename H' H'1,
  rw (dif_pos H'1), f_equal, subst i,
  dsimp [fin.pred], reflexivity,
},
{ rw (dif_neg H') at H, contradiction, }
end

lemma instantiate_head_var_0 (n : ℕ) (a x : ℚ)
  (i : fin n.succ) (Hi : i.val = 0)
  : instantiate_head (var a i) x = const n (a * x)
:= begin
dsimp [var, const, instantiate_head], f_equal,
{ dsimp [vector.generate], rw vector.tail_cons,
  rw ← vector.generate_const_repeat,
  f_equal, apply funext, intros x,
  dsimp [function.comp], rw Hi,
  rw (if_neg), contradiction,
 },
{ dsimp [vector.generate], rw vector.head_cons,
  rw (if_pos), simp, assumption,
}
end

lemma instantiate_head_var_succ {n : ℕ} (a x : ℚ)
  (i : fin n.succ) (H : i ≠ 0)
  :
  instantiate_head (var a i) x = var a (fin.pred i H)
:= begin
dsimp [var, const, instantiate_head], f_equal,
{ dsimp [vector.generate], rw vector.tail_cons,
  f_equal, apply funext, intros x,
  dsimp [function.comp], rw (ite_iff (succ_pred_equiv _ _ _)),
 },
{ dsimp [vector.generate], rw vector.head_cons,
  rw (if_neg), simp, intros contra, apply H,
  apply fin.val_inj, rw contra, reflexivity,
}
end

lemma nat_to_fin_option_val {n k : ℕ} {i : fin n}
  (H : nat_to_fin_option n k = some i)
  : i.val = k
:= begin
dsimp [nat_to_fin_option] at H,
apply (if H' : k < n then _ else _),
{ rw (dif_pos H') at H, injection H with H2,
  clear H, subst i,
},
{ rw (dif_neg H') at H, contradiction }
end

lemma instantiate_head_commutes {n : ℕ} (x : ℚ)
  (e : aexpr ℕ)
  (Hnobigvars : e.no_big_vars n.succ)
  : (e.interp_expr_context n.succ).instantiate_head x
  = (e.instantiate_head x).interp_expr_context n
:= begin
dsimp [aexpr.interp_expr_context],
induction e; dsimp [aexpr.instantiate_head
  , aexpr.var_map_default],
{ destruct (nat_to_fin_option n.succ a_1),
  { intros Hnone, rw Hnone, dsimp [aexpr.var_map_default],
    cases a_1; dsimp [aexpr.instantiate_head],
    dsimp [nat_to_fin_option] at Hnone,
    rw (dif_pos (nat.zero_lt_succ _)) at Hnone, contradiction,
    dsimp [aexpr.var_map_default],
    dsimp [aexpr.no_big_vars] at Hnobigvars,
    apply_in Hnone nat_to_fin_option_pred_none,
    rw Hnone,
    dsimp [aexpr.var_map_default],
    dsimp [aexpr.to_linear_expr],
    dsimp [instantiate_head, const],
    repeat { rw vector.repeat_unfold },
    rw vector.head_cons, rw vector.tail_cons,
    f_equal, simp, },
  { intros i Hi, rw Hi, dsimp [aexpr.var_map_default],
    cases a_1; dsimp [aexpr.instantiate_head, aexpr.var_map_default],
    { dsimp [aexpr.to_linear_expr],
      rw instantiate_head_var_0,
      apply nat_to_fin_option_val, assumption,
    },
    { rw nat_to_fin_option_pred_some, tactic.swap, assumption,
      dsimp [aexpr.var_map_default],
      dsimp [aexpr.to_linear_expr],
      apply instantiate_head_var_succ,
    }
  },
},
{ dsimp [instantiate_head, aexpr.to_linear_expr, const],
  repeat { rw vector.repeat_unfold }, rw vector.tail_cons,
  rw vector.head_cons, f_equal, simp, },
{ dsimp [aexpr.no_big_vars] at Hnobigvars,
  induction Hnobigvars with H1 H2,
  specialize (ih_1 H1), specialize (ih_2 H2),
  dsimp [aexpr.to_linear_expr],
  rw instantiate_head_add_expr, f_equal; assumption, }
end

lemma instantiate_head_commutes_list {n : ℕ} (x : ℚ)
  (es : list (aexpr ℕ))
  (Hnobigvars : list.Forall (aexpr.no_big_vars (nat.succ n)) es)
  : list.map (λ e, instantiate_head e x) (interp_list_exprs es (nat.succ n))
  = list.map (λ e, aexpr.interp_expr_context (aexpr.instantiate_head x e) n) es
:= begin
induction Hnobigvars; dsimp [interp_list_exprs, list.map],
reflexivity,
f_equal, rw instantiate_head_commutes, assumption,
apply ih_1,
end

lemma linear_implies_aexpr_negation (es : list (aexpr ℕ))
  (nvars : ℕ)
  (H : list.Forall (λ (x : aexpr ℕ), aexpr.no_big_vars nvars x) es)
  : linear_expr_negation_statement (interp_list_exprs es nvars)
  → aexpr_negation_statement nvars es
:= begin
revert es,
induction nvars;
  dsimp [linear_expr_negation_statement, aexpr_negation_statement];
  intros,
{ induction es; dsimp [aexpr_negation_statement_0],
    dsimp [interp_list_exprs, linear_expr_negation_statement_0] at a,
  { assumption },
  { intros H', apply_in H list.Forall_invert,
    dsimp at H, induction H with H1 H2, apply ih_1, assumption,
    apply a, dsimp, rw ← no_vars_nil_interp; assumption
  }
},
{ apply ih_1; clear ih_1, apply list.map_Forall,
  apply list.impl_Forall, assumption,
  intros e He, apply no_big_vars_instantiate_head, assumption,
  specialize (a_1 x), unfold interp_list_exprs,
  rw list.map_map, dsimp [function.comp],
  rw ← instantiate_head_commutes_list; assumption,
}
end


lemma satisfiable_bool_correct  (es : list (aexpr ℕ))
  (nvars : ℕ)
  : list.band (es.map (aexpr.no_big_vars_bool nvars)) = tt →
    satisfiable_bool' (interp_list_exprs es nvars) = ff →
    aexpr_negation_statement nvars es
:= begin
rw aexpr.no_big_vars_equiv,
rw ← to_bool_Forall,
rw to_bool_tt_iff,
intros H1 H2, apply linear_implies_aexpr_negation,
assumption,
apply satisfiable_bool_correct_linear, assumption,
end



namespace tactic.interactive

open tactic lean lean.parser
open interactive interactive.types expr

meta def intern_var (xs : list expr) (e : expr) : list expr × ℕ
  := (if e ∈ xs then xs else xs ++ [e], xs.index_of e)

meta def reify_constant_helper
  : expr → option (expr ff)
| `(has_one.one %%TT) := pure (``(has_one.one %%TT))
| `(has_zero.zero %%TT) := pure (``(has_zero.zero %%TT))
| `(bit0 %%x) := do
  x' ← reify_constant_helper x,
  pure (``(bit0 %%x))
| `(has_neg.neg %%x) := do
  x' ← reify_constant_helper x,
  pure (``(has_neg.neg %%x))
| `(bit1 %%x) := do
  x' ← reify_constant_helper x,
  pure (``(bit1 %%x))
| _ := none

meta def reify_axpr_helper
  : list expr → expr → tactic (expr ff × list expr)
| xs `(%%P + %%Q) := do
    (P', xs') ← reify_axpr_helper xs P,
    (Q', xs'') ← reify_axpr_helper xs' Q,
    pure (``(aexpr.add %%P' %%Q'), xs'')
| xs `(%%P * %%Q) := do
  P' ← reify_constant_helper P,
  let (xs', n) := intern_var xs Q in
  pure (``(aexpr.var %%P' %%(n.reflect)), xs')
| xs P := (do
  C ← reify_constant_helper P,
  pure (``(aexpr.const %%C), xs)
  ) <|>
  let (xs', n) := intern_var xs P in pure (``(aexpr.var 1 %%(n.reflect)), xs')

meta def reify_formula_helper
  : list expr → expr → tactic (option (expr ff × list expr))
| xs `(has_le.le %%ee (has_zero.zero _)) := some <$> reify_axpr_helper xs ee
| xs other := pure none

meta def reify_all_helper
  : list expr → list expr → tactic (list (expr ff) × list expr)
| ctxt [] := pure ([], ctxt)
| ctxt (x :: xs) := do
  r ← reify_formula_helper ctxt x,
  match r with
  | some (x', ctxt') := do
    (xs', ctxt'') ← reify_all_helper ctxt' xs,
    pure (x' :: xs', ctxt'')
  | none := reify_all_helper ctxt xs
  end

meta def my_reify (es : list expr)
  : tactic (list (expr ff) × list expr)
  := reify_all_helper [] es


meta def make_list : list expr → expr ff
| [] := ``(list.nil)
| (x :: xs) := ``(list.cons %%x %%(make_list xs))

meta def make_nat : ℕ → expr ff
| 0 := ``(0)
| (nat.succ n) := ``(nat.succ %%(make_nat n))

def list.nth_def {α : Type u} (xs : list α) (default : α) (n : ℕ) : α
:= match xs.nth n with
| (some x) := x
| none := default
end

meta def whole_thing : tactic unit := do
    ctx ← local_context,
    ctx_types ← ctx.mmap infer_type,
    (hyps, ctxt) ← my_reify ctx_types,
    hyps' ← mmap i_to_expr hyps,
    let ctxt' := make_list ctxt,
    let num_vars := make_nat ctxt.length,
    let hyps'' := make_list hyps',
    hyps''' ← i_to_expr hyps'',
    --res ← i_to_expr ``(interp_list_exprs %%hyps''' %%num_vars),
    --tactic.trace res,
    --ans ← i_to_expr ``(satisfiable_bool %%res),
    --ans' ← tactic.eval_expr bool ans,
    --whnf ans >>= tactic.trace,
    ap_expr ← i_to_expr ``(satisfiable_bool_correct %%hyps''' %%num_vars),
    tactic.apply ap_expr

end tactic.interactive

lemma my_lemma
  (x y z : ℚ)
  (Hx : 1 * x + 3 ≤ 0)
  (Hy : -2 * x + (-5) ≤ 0)
  (Hz : (0 : ℚ) ≤ 0)
  : false
:= begin
whole_thing; reflexivity <|> assumption,
end