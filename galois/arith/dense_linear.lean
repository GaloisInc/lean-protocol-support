import data.rat
       galois.list.preds
       galois.list.fpow
       galois.tactic
       .dense_linear_lemmas

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

lemma vector.map₂_nil {A B C} (f : A → B → C)
  : vector.map₂ f vector.nil vector.nil = vector.nil
  := rfl

lemma vector.map₂_cons {A B C} (f : A → B → C)
  (a : A) (b : B) {n : ℕ} (as : vector A n) (bs : vector B n)
  : vector.map₂ f (a :: as) (b :: bs) = f a b :: vector.map₂ f as bs
:= begin
induction as, induction bs, reflexivity,
end

lemma dot_product_nil : dot_product vector.nil vector.nil = 0
  := rfl

lemma dot_product_unit (n : ℕ) (i : fin n) (c : ℚ) (v : vector ℚ n) :
  dot_product
  (vector.generate n (λj, if i.val = j then c else 0))
  v
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
  admit },
{ rw (if_neg H), admit }
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
{ rw (vector.eq_nil x),
  rw (vector.eq_nil y),
  rw (vector.eq_nil z),
  rw dot_product_nil,
  rw vector.map₂_nil, rw dot_product_nil,
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

lemma Forall_mem_equiv {A : Type u}
  (P : A → Prop) (xs : list A)
  : xs.Forall P ↔ (∀ x, x ∈ xs → P x)
:= begin
split; intros H,
{ induction H,
  intros, rw list.mem_nil_iff at a, contradiction,
  intros, apply_in a_2 list.eq_or_mem_of_mem_cons,
  induction a_2, subst x_1, assumption, apply ih_1,
  assumption,
},
{ induction xs, constructor, constructor,
  apply H, constructor, reflexivity,
  apply ih_1, intros, apply H,
  right, assumption,
}
end

lemma Forall_equiv_list {A : Type _}
  (P : A → Prop) (xs ys : list A)
  (H : same_elements xs ys)
  : xs.Forall P ↔ ys.Forall P
:= begin
unfold same_elements at H,
repeat { rw Forall_mem_equiv },
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

def eliminate_aux {n : ℕ} (prob : focused n)
  : list (linear_expr n)
:= (do (lb, lbe) ← prob.lbs, (ub, ube) ← prob.ubs,
       return (combine lb lbe ub ube)) ++ prob.uninvolved

def eliminate {n : ℕ} (es : list (linear_expr (n + 1)))
  : list (linear_expr n)
:= eliminate_aux (focus_problem es)

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
  dsimp [evaluate] at *,
  dsimp [combine, add_expr, scale_mul],
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
split; intros H,
{ induction H with a Ha,
  admit },
{ admit }
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
dsimp [evaluate],
admit
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
induction e; dsimp [interp, to_linear_expr, evaluate],
case var c i
{ rw var_offset_0,
  rw add_zero,
  admit },
{ admit },
{ admit }
end
end aexpr

namespace eqn
def interp {vTy : Type} (ctxt : vTy → ℚ)
  : eqn vTy → Prop
| (le e e') := e.interp ctxt ≤ e'.interp ctxt
end eqn


def nat_to_fin_option {k : ℕ} (n : ℕ) : option (fin k)
  := if H : n < k then some ⟨ _, H ⟩ else none

namespace aexpr
def interp_expr_context (hyp : aexpr ℕ)
  (n : ℕ) : linear_expr n
  := (aexpr.var_map_default nat_to_fin_option 0 hyp).to_linear_expr
def instantiate_head (c' : ℚ) : aexpr ℕ → aexpr ℕ
| (var c n) := match n with
  | 0 := const (c * c')
  | (nat.succ n') := var c n'
  end
| (const q) := const q
| (add x y) := add (instantiate_head x) (instantiate_head y)

def no_big_vars (nvars : ℕ) : aexpr ℕ → bool
| (var c x) := decidable.to_bool (x < nvars)
| (const q) := tt
| (add x y) := band (no_big_vars x) (no_big_vars y)
end aexpr

def interp_list_exprs (hyps : list (aexpr ℕ))
  (n : ℕ) : list (linear_expr n)
:= hyps.map (λ hyp : aexpr ℕ, hyp.interp_expr_context n)

end linear_expr

open linear_expr

-- The pattern matching compiler could not determine that
-- this definition was well-founded, so I wrote it with
-- the recursor
def linear_expr_negation_statement :
  ∀ {n : ℕ}, list (linear_expr n) → Prop
:= begin
intros n, induction n,
{ intros es, induction es,
  { exact false },
  { exact a.evaluate vector.nil ≤ 0 → ih_1 } },
{ intros es, exact (∀ x : ℚ, ih_1 (es.map (λ e, e.instantiate_head x))) }
end

def aexpr_negation_statement :
  ∀ nvars : ℕ, list (aexpr ℕ) → Prop
:= begin
intros n, induction n,
{ intros es, induction es,
  { exact false },
  { exact a.interp (λ _, 0) ≤ 0 → ih_1 } },
{ intros es, exact (∀ x : ℚ, ih_1 (es.map (λ e, e.instantiate_head x))) }
end

lemma satisfiable_bool_correct_linear {n : ℕ} (e : list (linear_expr n))
  : satisfiable_bool' e = ff →
    linear_expr_negation_statement e
:= begin
admit
end


lemma satisfiable_bool_correct  (es : list (aexpr ℕ))
  (nvars : ℕ)
  : list.band (es.map (λ e, e.no_big_vars nvars)) = tt →
    satisfiable_bool' (interp_list_exprs es nvars) = ff →
    aexpr_negation_statement nvars es
:= begin
admit
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
    --tactic.trace ctxt,
    let hyps'' := make_list hyps',
    hyps''' ← i_to_expr hyps'',
    res ← i_to_expr ``(interp_list_exprs %%hyps''' %%num_vars),
    tactic.trace res,
    ans ← i_to_expr ``(satisfiable_bool %%res),
    ans' ← tactic.eval_expr bool ans,
    whnf ans >>= tactic.trace,
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