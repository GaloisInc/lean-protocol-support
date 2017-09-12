import data.rat
       galois.tactic
       .dense_linear_lemmas
       galois.list
       galois.list.fpow
       galois.vector.lemmas
       galois.vector.dot_product
       galois.list.mem
       galois.fin

universes u

namespace rat

def to_string (q:ℚ) : string :=
 if q.denom = 1 then
   to_string (q.num)
 else
   to_string (q.num) ++ "/" ++ to_string q.denom

instance : has_to_string ℚ := ⟨ to_string ⟩

end rat

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

def combine {n : ℕ} (lb : ℚ) (lbe : linear_expr n) (ub : ℚ)
  (ube : linear_expr n) : linear_expr n
:= add_expr (scale_mul (-lb) ube) (scale_mul ub lbe)

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
apply list.mem_map', tactic.swap, assumption,
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
apply list.mem_map', tactic.swap, assumption,
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
  apply list.mem_map, assumption,
}
end

lemma id_rhs_list {A} (x : A) :
  id_rhs (list A) (return x) = [x] := rfl


lemma add_reassoc (lb ub : ℚ) (ube1 ube2 lbe1 lbe2 : ℚ)
  : lb * ube1 + ub * lbe1 + (lb * ube2 + ub * lbe2)
  = lb * (ube1 + ube2) + ub * (lbe1 + lbe2)
:= begin
repeat { rw mul_add }, simp,
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
    apply_in Hx list.mem_bind',
    induction Hx with lbp Hx,
    induction Hx with HA HB,
    specialize (H1 lbp HA),
    induction lbp with lb lbe,
    dsimp [bounds_list] at HB,
    apply_in HB list.mem_bind',
    induction HB with ubp HB,
    induction HB with HB HC,
    specialize (H2 ubp HB),
    induction ubp with ub ube,
    dsimp at HC,
    rw id_rhs_list at HC,
    induction lb with lb lblt0,
    rw list.mem_singleton_iff at HC,
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
      rw list.mem_bind_iff',
      existsi (lb, lbe), split, assumption,
      dsimp [bounds_list], rw list.mem_bind_iff',
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

lemma band_tt_left (b : bool) : tt && b = b
:= begin
induction b; reflexivity
end

lemma to_bool_Forall {A} (xs : list A) (P : A → Prop) [decP : decidable_pred P] :
  to_bool (list.Forall P xs) = list.band (xs.map (λ x, to_bool (P x)))
:= begin
unfold to_bool,
cases (list.Forall_decidable P xs) with no yes,
{ induction xs; dsimp [list.band, list.all],
  exfalso, apply no, constructor,
  cases (decP a); dsimp, reflexivity,
  rw band_tt_left, apply ih_1, intros contra,
  apply no, constructor; assumption },
{ dsimp, induction xs; dsimp [list.band, list.all],
  reflexivity,
  apply_in yes list.Forall_invert, dsimp at yes, induction yes with yes yes',
  cases (decP a); dsimp,
  contradiction, rw band_tt_left, apply ih_1, assumption,
}
end

lemma satisfiable_bool_equiv {n : ℕ} (xs : list (linear_expr n))
  : satisfiable_bool xs = satisfiable_bool' xs
:= begin
unfold satisfiable_bool satisfiable_bool',
rw (to_bool_congr (eliminate_all_equiv _)),
unfold satisfiable,
rw (to_bool_congr (vector_nil_exists _)),
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

lemma  no_vars_nil_interp (e : aexpr ℕ)
  (H : e.no_big_vars 0)
  : e.interp (λ _, 0) = evaluate (e.interp_expr_context 0) vector.nil
:= begin
dsimp [aexpr.interp_expr_context],
rw vector.nil_of_fn,
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
  dsimp [function.comp], rw (ite_iff (fin.succ_pred_equiv _ _ _)),
 },
{ dsimp [vector.generate], rw vector.head_cons,
  rw (if_neg), simp, intros contra, apply H,
  apply fin.val_inj, rw contra, reflexivity,
}
end

lemma instantiate_head_commutes {n : ℕ} (x : ℚ)
  (e : aexpr ℕ)
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
{ dsimp [aexpr.to_linear_expr],
  rw instantiate_head_add_expr, f_equal; assumption, }
end

lemma instantiate_head_commutes_list {n : ℕ} (x : ℚ)
  (es : list (aexpr ℕ))
  : list.map (λ e, instantiate_head e x) (interp_list_exprs es (nat.succ n))
  = list.map (λ e, aexpr.interp_expr_context (aexpr.instantiate_head x e) n) es
:= begin
dsimp [interp_list_exprs, list.map],
rw list.map_map, f_equal, dsimp [function.comp],
apply funext, intros e,
rw instantiate_head_commutes,
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