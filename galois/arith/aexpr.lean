import .dense_linear

universes u v

open linear_expr

inductive aexpr (A : Type u) (vTy : Type) : Type u
| var {} : A → vTy → aexpr
| const {} : A → aexpr
| add {} : aexpr → aexpr → aexpr

inductive eqn (A : Type u) (vTy : Type) : Type u
| le {} : aexpr A vTy → aexpr A vTy → eqn

namespace aexpr
def map {A : Type u} {B : Type v} (f : A → B) {vTy : Type}
  : aexpr A vTy → aexpr B vTy
| (var c x) := var (f c) x
| (const q) := const (f q)
| (add x y) := add (map x) (map y)

def interp {A : Type u} [semiring A] {vTy : Type} (ctxt : vTy → A)
  : aexpr A vTy → A
| (var c x) := c * ctxt x
| (const q) := q
| (add x y) := interp x + interp y

def to_linear_expr {n : ℕ}
  : aexpr ℚ (fin n) → linear_expr n
| (var c x) := linear_expr.var c x
| (const q) := linear_expr.const _ q
| (add x y) := add_expr (to_linear_expr x) (to_linear_expr y)

def var_map {A : Type u} {vTy vTy' : Type} (f : vTy → vTy')
  : aexpr A vTy → aexpr A vTy'
| (var c x) := var c (f x)
| (const q) := const q
| (add x y) := add (var_map x) (var_map y)

def var_map_default {A : Type u} {vTy vTy' : Type} (f : vTy → option vTy')
  (default : A)
  : aexpr A vTy → aexpr A vTy'
| (var c x) := match f x with
   | some y := var c y
   | none := const default
   end
| (const q) := const q
| (add x y) := add (var_map_default x) (var_map_default y)

lemma to_linear_expr_sound {n : ℕ}
  (e : aexpr ℚ (fin n))
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
  : eqn ℚ vTy → Prop
| (le e e') := e.interp ctxt ≤ e'.interp ctxt
end eqn


namespace aexpr
def interp_expr_context (hyp : aexpr ℚ ℕ)
  (n : ℕ) : linear_expr n
  := (aexpr.var_map_default (nat_to_fin_option _) 0 hyp).to_linear_expr

def instantiate_head {A} [semiring A]
  (c' : A) : aexpr A ℕ → aexpr A ℕ
| (var c n) := match n with
  | 0 := const (c * c')
  | (nat.succ n') := var c n'
  end
| (const q) := const q
| (add x y) := add (instantiate_head x) (instantiate_head y)

def no_big_vars_bool {A} (nvars : ℕ) : aexpr A ℕ → bool
| (var c x) := decidable.to_bool (x < nvars)
| (const q) := tt
| (add x y) := band (no_big_vars_bool x) (no_big_vars_bool y)

def no_big_vars {A} (nvars : ℕ) : aexpr A ℕ → Prop
| (var c x) := x < nvars
| (const q) := true
| (add x y) := no_big_vars x ∧ no_big_vars y

instance no_big_vars_decidable {A} (nvars : ℕ)
  : decidable_pred (@no_big_vars A nvars)
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

lemma no_big_vars_equiv {A} (nvars : ℕ)
  : @no_big_vars_bool A nvars = λ e, to_bool (no_big_vars nvars e)
:= begin
apply funext; intros e,
induction e; dsimp [no_big_vars, no_big_vars_bool],
reflexivity, rw to_bool_tt, trivial,
rw [ih_1, ih_2], rw to_bool_and,
end

end aexpr

def interp_list_exprs (hyps : list (aexpr ℚ ℕ))
  (n : ℕ) : list (linear_expr n)
:= hyps.map (λ hyp : aexpr ℚ ℕ, hyp.interp_expr_context n)

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

def aexpr_negation_statement_0 {A} [linear_ordered_comm_ring A]
  : list (aexpr A ℕ) → Prop
| [] := false
| (e :: es) := e.interp (λ _, 0) ≤ 0 → aexpr_negation_statement_0 es

def aexpr_negation_statement {A} [linear_ordered_comm_ring A] :
  ∀ nvars : ℕ, list (aexpr A ℕ) → Prop
| 0 := aexpr_negation_statement_0
| (nat.succ n) := λ es, ∀ x : A, aexpr_negation_statement n
    (es.map (λ e, e.instantiate_head x))

lemma coe_rat_of_int (x : ℤ)
  : ↑ x = rat.of_int x := rfl

lemma rat.coe_int_mul (x y : ℤ)
  : (↑ (x * y) : ℚ) = (↑ x) * (↑ y)
:= begin
repeat { rw coe_rat_of_int },
dsimp [rat.of_int, has_mul.mul, rat.mul],
dsimp [rat.mk_pnat],
apply rat.coe_int_eq_mk,
end

lemma rat.coe_int_neg (x : ℤ)
  : (↑ (- x) : ℚ) = - ↑ x
:= rfl

lemma nonneg_rat_nonneg (x : ℤ)
  (H : 0 ≤ x) : rat.nonneg (↑ x)
:= begin
rw coe_rat_of_int, dsimp [rat.nonneg, rat.of_int],
assumption,
end


lemma Z_to_Q_le_iff (x y : ℤ)
  : x ≤ y ↔ (↑ x : ℚ) ≤ ↑ y
:= begin
split; intros H,
{ dsimp [has_le.le, rat.le],
  rw ← rat.coe_int_neg, rw ← rat.coe_int_add,
  apply nonneg_rat_nonneg,
  rw ← sub_eq_add_neg,
  apply sub_nonneg_of_le, assumption,
 },
{ apply rat.le_of_of_int_le_of_int, assumption, }
end

lemma Z_to_Q_interp (e : aexpr ℤ ℕ) (ctxt : ℕ → ℤ)
  : (↑ (e.interp ctxt) : ℚ)
  = (e.map coe).interp (λ x, ↑ (ctxt x))
:= begin
induction e; dsimp [aexpr.interp, aexpr.map],
rw rat.coe_int_mul, reflexivity,
rw [rat.coe_int_add, ih_1, ih_2],
end

lemma rat.coe_int_zero
  : ↑ (0 : ℤ) = (0 : ℚ)
:= rfl

lemma instantiate_head_Z_to_Q
  (c : ℤ)
  : aexpr.map coe ∘ aexpr.instantiate_head c = aexpr.instantiate_head (↑ c : ℚ) ∘ aexpr.map coe
:= begin
apply funext; intros e; dsimp [function.comp],
induction e; dsimp [aexpr.instantiate_head, aexpr.map],
cases a_1; dsimp [aexpr.instantiate_head, aexpr.map],
rw rat.coe_int_mul, reflexivity, reflexivity,
rw [ih_1, ih_2],
end


lemma Z_to_Q_sound (nvars : ℕ) (xs : list (aexpr ℤ ℕ))
  : aexpr_negation_statement nvars (xs.map (aexpr.map coe) : list (aexpr ℚ ℕ))
  → aexpr_negation_statement nvars xs
:= begin
revert xs,
induction nvars; intros xs; dsimp [aexpr_negation_statement],
{ induction xs; dsimp [aexpr_negation_statement_0],
  { intros H, assumption },
  { intros H H', apply ih_1, apply H,
    rw Z_to_Q_le_iff at H', rw Z_to_Q_interp at H',
    repeat { rw rat.coe_int_zero }, assumption,
  }
},
{ intros H x, specialize (H x), rw list.map_map at H,
  rw ← instantiate_head_Z_to_Q at H,
  apply ih_1, rw list.map_map, assumption }
end

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

lemma  no_vars_nil_interp (e : aexpr ℚ ℕ)
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

lemma no_big_vars_instantiate_head {n : ℕ} {e : aexpr ℚ ℕ} (x : ℚ)
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
  (e : aexpr ℚ ℕ)
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
  (es : list (aexpr ℚ ℕ))
  : list.map (λ e, instantiate_head e x) (interp_list_exprs es (nat.succ n))
  = list.map (λ e, aexpr.interp_expr_context (aexpr.instantiate_head x e) n) es
:= begin
dsimp [interp_list_exprs, list.map],
rw list.map_map, f_equal, dsimp [function.comp],
apply funext, intros e,
rw instantiate_head_commutes,
end

lemma linear_implies_aexpr_negation (es : list (aexpr ℚ ℕ))
  (nvars : ℕ)
  (H : list.Forall (λ (x : aexpr ℚ ℕ), aexpr.no_big_vars nvars x) es)
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


lemma satisfiable_bool_correct  (es : list (aexpr ℚ ℕ))
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

lemma satisfiable_bool_correct_Z  (es : list (aexpr ℤ ℕ))
  (nvars : ℕ)
  : list.band ((es.map (aexpr.map coe) : list (aexpr ℚ ℕ)).map (aexpr.no_big_vars_bool nvars)) = tt →
    satisfiable_bool' (interp_list_exprs (es.map (aexpr.map coe)) nvars) = ff →
    aexpr_negation_statement nvars es
:= begin
intros H H',
apply Z_to_Q_sound,
apply satisfiable_bool_correct; assumption,
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

meta def reify_hyps_numvars : tactic (expr × expr ff) := do
    ctx ← local_context,
    ctx_types ← ctx.mmap infer_type,
    (hyps, ctxt) ← my_reify ctx_types,
    hyps' ← mmap i_to_expr hyps,
    let ctxt' := make_list ctxt,
    let num_vars := make_nat ctxt.length,
    let hyps'' := make_list hyps',
    hyps''' ← i_to_expr hyps'',
    return (hyps''', num_vars)

meta def fourier_Q_core : tactic unit := do
    (hyps''', num_vars) ← reify_hyps_numvars,
    ap_expr ← i_to_expr ``(satisfiable_bool_correct %%hyps''' %%num_vars),
    tactic.apply ap_expr

meta def fourier_Z_core : tactic unit := do
    (hyps''', num_vars) ← reify_hyps_numvars,
    ap_expr ← i_to_expr ``(satisfiable_bool_correct_Z %%hyps''' %%num_vars),
    tactic.apply ap_expr

end tactic.interactive

lemma my_lemma
  (x y z : ℚ)
  (Hx : 1 * x + 3 ≤ 0)
  (Hy : -2 * x + (-5) ≤ 0)
  (Hz : (0 : ℚ) ≤ 0)
  : false
:= begin
fourier_Q_core; reflexivity <|> assumption,
end

lemma my_lemma2
  (x y z : ℤ)
  (Hx : 1 * x + 3 ≤ 0)
  (Hy : -2 * x + (-5) ≤ 0)
  (Hz : (0 : ℤ) ≤ 0)
  : false
:= begin
fourier_Z_core; reflexivity <|> assumption,
end