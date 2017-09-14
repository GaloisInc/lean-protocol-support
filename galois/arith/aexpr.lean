import .dense_linear

universes u v

class discrete_order_ring (α : Type u) extends semiring α, decidable_linear_order α :=
(lt_iff_add_one_le : ∀ (a b : α), a < b ↔ a + 1 ≤ b)
(gt_iff_add_one_le : ∀ (a b : α), a > b ↔ b + 1 ≤ a)

lemma int.gt_iff_add_one_le (a b : ℤ) : a > b ↔ b + 1 ≤ a  := iff.refl _

instance discrete_order_ring_ℤ : discrete_order_ring ℤ :=
begin
constructor, apply int.lt_iff_add_one_le, apply int.gt_iff_add_one_le
end

instance discrete_order_ring_ℕ : discrete_order_ring ℕ :=
begin
constructor, intros a b, reflexivity, intros a b, reflexivity,
apply_instance,
end

open linear_expr

inductive aexpr (A : Type u) (vTy : Type) : Type u
| var {} : A → vTy → aexpr
| var1 {} : vTy → aexpr
| const {} : A → aexpr
| add {} : aexpr → aexpr → aexpr

inductive eqn (A : Type u) (vTy : Type) : Type u
| le {} : aexpr A vTy → aexpr A vTy → eqn

namespace aexpr
def map {A : Type u} {B : Type v} (f : A → B) {vTy : Type}
  : aexpr A vTy → aexpr B vTy
| (var c x) := var (f c) x
| (var1 x) := var1 x
| (const q) := const (f q)
| (add x y) := add (map x) (map y)

def scale {A : Type u} [semiring A] {vTy : Type}
  (c : A)
  : aexpr A vTy → aexpr A vTy
| (var c' x) := var (c * c') x
| (var1 x) := var c x
| (const q) := const (c * q)
| (add x y) := add (scale x) (scale y)

def interp {A : Type u} [semiring A] {vTy : Type} (ctxt : vTy → A)
  : aexpr A vTy → A
| (var c x) := c * ctxt x
| (var1 x) := ctxt x
| (const q) := q
| (add x y) := interp x + interp y

lemma interp_scale {A : Type u} [semiring A] {vTy : Type} (ctxt : vTy → A)
  (c : A)
  (e : aexpr A vTy) : (e.scale c).interp ctxt = c * e.interp ctxt
:= begin
induction e; simp [scale, interp],
rw [ih_1, ih_2], rw mul_add,
end

def to_linear_expr {n : ℕ}
  : aexpr ℚ (fin n) → linear_expr n
| (var c x) := linear_expr.var c x
| (var1 x) := linear_expr.var 1 x
| (const q) := linear_expr.const _ q
| (add x y) := add_expr (to_linear_expr x) (to_linear_expr y)

def var_map {A : Type u} {vTy vTy' : Type} (f : vTy → vTy')
  : aexpr A vTy → aexpr A vTy'
| (var c x) := var c (f x)
| (var1 x) := var1 (f x)
| (const q) := const q
| (add x y) := add (var_map x) (var_map y)

def var_map_default {A : Type u} {vTy vTy' : Type} (f : vTy → option vTy')
  (default : A)
  : aexpr A vTy → aexpr A vTy'
| (var c x) := match f x with
   | some y := var c y
   | none := const default
   end
| (var1 x) := match f x with
   | some y := var1 y
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
{ rw var_evaluate, rw vector.nth_of_fn, rw [mul_comm, mul_one], },
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
def interp {A} [semiring A] [decidable_linear_order A] {vTy : Type} (ctxt : vTy → A)
  : eqn A vTy → Prop
| (le e e') := e.interp ctxt ≤ e'.interp ctxt

def map_aexpr {A B} {vTy : Type} (f : aexpr A vTy → aexpr B vTy)
  : eqn A vTy → eqn B vTy
| (le e e') := le (f e) (f e')

lemma map_aexpr_compose {A B C} {vTy : Type} (f : aexpr A vTy → aexpr B vTy)
  (g : aexpr B vTy → aexpr C vTy)
  : map_aexpr g ∘ map_aexpr f = map_aexpr (g ∘ f)
:= begin
apply funext, intros e,
induction e with e e', simp [function.comp, map_aexpr],
end

def to_aexpr {vTy : Type} {A} [ring A]
  : eqn A vTy → aexpr A vTy
| (le e e') := aexpr.add e (aexpr.scale (-1) e')
end eqn


inductive eqnd (Z : Type) (vTy : Type) : Type u
| le {} : aexpr Z vTy → aexpr Z vTy → eqnd
| lt {} : aexpr Z vTy → aexpr Z vTy → eqnd
| eq {} : aexpr Z vTy → aexpr Z vTy → eqnd
| gt {} : aexpr Z vTy → aexpr Z vTy → eqnd
| ge {} : aexpr Z vTy → aexpr Z vTy → eqnd

namespace eqnd
def interp {Z : Type} {vTy : Type}
  [semiring Z] [decidable_linear_order Z]
   (ctxt : vTy → Z)
  : eqnd Z vTy → Prop
| (le e e') := e.interp ctxt ≤ e'.interp ctxt
| (lt e e') := e.interp ctxt < e'.interp ctxt
| (eq e e') := e.interp ctxt = e'.interp ctxt
| (gt e e') := e.interp ctxt > e'.interp ctxt
| (ge e e') := e.interp ctxt ≥ e'.interp ctxt

def to_eqns {Z} {vTy : Type}
  [has_one Z]
  : eqnd Z vTy → list (eqn Z vTy)
| (le e e') := [eqn.le e e']
| (lt e e') := [eqn.le (aexpr.add e (aexpr.const 1)) e']
| (eq e e') := [eqn.le e e', eqn.le e' e]
| (ge e e') := [eqn.le e' e]
| (gt e e') := [eqn.le (aexpr.add e' (aexpr.const 1)) e]

def map_aexpr {Z Z'} {vTy : Type} (f : aexpr Z vTy → aexpr Z' vTy)
  : eqnd Z vTy → eqnd Z' vTy
| (le e e') := le (f e) (f e')
| (lt e e') := lt (f e) (f e')
| (eq e e') := eq (f e) (f e')
| (gt e e') := gt (f e) (f e')
| (ge e e') := ge (f e) (f e')

lemma map_aexpr_compose {A B C} {vTy : Type} (f : aexpr A vTy → aexpr B vTy)
  (g : aexpr B vTy → aexpr C vTy)
  : map_aexpr g ∘ map_aexpr f = map_aexpr (g ∘ f)
:= begin
apply funext, intros e,
induction e with e e'; simp [function.comp, map_aexpr],
end

lemma to_eqns_interp {A} [discrete_order_ring A]
  {vTy} (x : eqnd A vTy) (ctxt : vTy → A)
  : x.interp ctxt ↔ list.foldr (∧) true (x.to_eqns.map (eqn.interp ctxt))
:= begin
induction x; dsimp [to_eqns, interp, eqn.interp],
case le e e' { simp, },
case lt e e' {
  dsimp [aexpr.interp],
  rw discrete_order_ring.lt_iff_add_one_le, simp,
 },
case eq e e' {
  rw le_antisymm_iff, simp,
},
case gt e e' {
  dsimp [aexpr.interp],
  rw discrete_order_ring.gt_iff_add_one_le, simp,
 },
case ge e e' { simp, },
end

end eqnd


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
| (var1 n) := match n with
  | 0 := const c'
  | (nat.succ n') := var1 n'
  end
| (const q) := const q
| (add x y) := add (instantiate_head x) (instantiate_head y)

def no_big_vars_bool {A} (nvars : ℕ) : aexpr A ℕ → bool
| (var c x) := decidable.to_bool (x < nvars)
| (var1 x) := decidable.to_bool (x < nvars)
| (const q) := tt
| (add x y) := band (no_big_vars_bool x) (no_big_vars_bool y)

def no_big_vars {A} (nvars : ℕ) : aexpr A ℕ → Prop
| (var c x) := x < nvars
| (var1 x) := x < nvars
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
reflexivity, reflexivity, rw to_bool_tt, trivial,
rw [ih_1, ih_2], rw to_bool_and,
end

end aexpr

def interp_list_exprs (hyps : list (aexpr ℚ ℕ))
  (n : ℕ) : list (linear_expr n)
:= hyps.map (λ hyp : aexpr ℚ ℕ, hyp.interp_expr_context n)

open linear_expr

def negation_statement_0 {A} (f : A → Prop)
  : list A → Prop
| [] := false
| (e :: es) := f e → negation_statement_0 es

def linear_expr_negation_statement :
  ∀ {n : ℕ}, list (linear_expr n) → Prop
| 0 := negation_statement_0 (λ e, e.evaluate vector.nil ≤ 0)
| (nat.succ n) := λ es, ∀ x : ℚ, linear_expr_negation_statement
    (es.map (λ e, e.instantiate_head x))

def aexpr_negation_statement {A} [semiring A] [decidable_linear_order A] :
  ∀ nvars : ℕ, list (aexpr A ℕ) → Prop
| 0 := negation_statement_0 (λ e, e.interp (λ _, 0) ≤ 0)
| (nat.succ n) := λ es, ∀ x : A, aexpr_negation_statement n
    (es.map (λ e, e.instantiate_head x))

def eqn_negation_statement {A} [semiring A] [decidable_linear_order A]
  : ∀ nvars : ℕ, list (eqn A ℕ) → Prop
| 0 := negation_statement_0 (λ e, e.interp (λ _, (0 : A)))
| (nat.succ n) := λ es, ∀ x : A, eqn_negation_statement n
    (es.map (λ e, e.map_aexpr (aexpr.instantiate_head x)))

def eqnd_negation_statement {Z} [semiring Z] [decidable_linear_order Z]
  : ∀ nvars : ℕ, list (eqnd Z ℕ) → Prop
| 0 := negation_statement_0 (λ e, e.interp (λ _, (0 : Z)))
| (nat.succ n) := λ es, ∀ x : Z, eqnd_negation_statement n
    (es.map (λ e, e.map_aexpr (aexpr.instantiate_head x)))

def eqnd_negation_statement_nonneg {Z} [semiring Z] [decidable_linear_order Z]
  : ∀ nvars : ℕ, list (eqnd Z ℕ) → Prop
| 0 := negation_statement_0 (λ e, e.interp (λ _, (0 : Z)))
| (nat.succ n) := λ es, ∀ x : Z, 0 ≤ x → eqnd_negation_statement_nonneg n
    (es.map (λ e, e.map_aexpr (aexpr.instantiate_head x)))

def nonzero_constraints {Z : Type} [has_zero Z]
  : ℕ → list (eqn Z ℕ)
| 0 := []
| (nat.succ n) := eqn.le (aexpr.const 0) (aexpr.var1 n)
               :: nonzero_constraints n



lemma coe_rat_of_int (x : ℤ)
  : ↑ x = rat.of_int x := rfl

lemma rat.coe_int_mul (x y : ℤ)
  : (↑ (x * y) : ℚ) = (↑ x) * (↑ y)
:= begin
simp [rat.coe_int_eq_mk],
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
rw rat.coe_int_mul, reflexivity, reflexivity,
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
rw rat.coe_int_mul, reflexivity,
cases a; dsimp [aexpr.instantiate_head, aexpr.map],
reflexivity,
reflexivity, reflexivity,
rw [ih_1, ih_2],
end

lemma instantiate_head_N_to_Z
  (c : ℕ)
  : aexpr.map coe ∘ aexpr.instantiate_head c = aexpr.instantiate_head (↑ c : ℤ) ∘ aexpr.map coe
:= begin
apply funext; intros e; dsimp [function.comp],
induction e; dsimp [aexpr.instantiate_head, aexpr.map],
cases a_1; dsimp [aexpr.instantiate_head, aexpr.map],
rw int.coe_nat_mul, reflexivity,
cases a; dsimp [aexpr.instantiate_head, aexpr.map],
reflexivity,
reflexivity, reflexivity,
rw [ih_1, ih_2],
end

lemma nonneg_sub2 {A} [linear_ordered_comm_ring A] (x y : A)
  : x ≤ y ↔ x - y ≤ 0
:= begin
rw sub_eq_add_neg,
rw add_neg_le_l x (-y),
rw neg_neg,
end

lemma eqn_aexpr_interp {vTy} (e : eqn ℚ vTy)
  (ctxt : _) :
  eqn.interp ctxt e ↔ aexpr.interp ctxt e.to_aexpr ≤ 0
:= begin
induction e with e e',
dsimp [eqn.interp, eqn.to_aexpr, aexpr.interp],
rw aexpr.interp_scale,
rw ← neg_mul_eq_neg_mul,
rw mul_comm, rw mul_one,
rw ← sub_eq_add_neg,
rw nonneg_sub2,
end

lemma aexpr_instantiate_head_add {A} [semiring A] (x : A) (e e' : _)
  : aexpr.instantiate_head x (aexpr.add e e')
  = aexpr.add (aexpr.instantiate_head x e) (aexpr.instantiate_head x e')
:= rfl

lemma aexpr_instantiate_head_scale {A} [semiring A] (x c : A) (e : _)
  : aexpr.instantiate_head x (aexpr.scale c e)
  = aexpr.scale c (aexpr.instantiate_head x e)
:= begin
induction e; dsimp [aexpr.instantiate_head, aexpr.scale],
cases a_1; dsimp [aexpr.instantiate_head, aexpr.scale],
rw mul_assoc, reflexivity,
cases a; dsimp [aexpr.instantiate_head, aexpr.scale],
reflexivity,
reflexivity, reflexivity,
rw [ih_1, ih_2],
end

lemma eqn_aexpr_instantiate_head {A} [ring A] (x : A) :
   aexpr.instantiate_head x ∘ eqn.to_aexpr
 = eqn.to_aexpr ∘ eqn.map_aexpr (aexpr.instantiate_head x)
:= begin
dsimp [function.comp], apply funext, intros e,
induction e with e e',
dsimp [eqn.to_aexpr, eqn.map_aexpr],
rw aexpr_instantiate_head_add,
rw aexpr_instantiate_head_scale,
end

lemma eqn_to_aexpr_sound (nvars : ℕ) (xs : list (eqn ℚ ℕ))
  : aexpr_negation_statement nvars (xs.map (eqn.to_aexpr))
  → eqn_negation_statement nvars xs
:= begin
revert xs,
induction nvars; intros xs; dsimp [aexpr_negation_statement],
{ induction xs; dsimp [negation_statement_0],
  { intros H, assumption },
  { intros H H', apply ih_1, apply H,
    rw ← eqn_aexpr_interp, assumption,
  }
},
{ intros H, dsimp [eqn_negation_statement], intros x,
  specialize (H x), rw list.map_map at H,
  rw eqn_aexpr_instantiate_head at H,
  apply ih_1, rw list.map_map, assumption
}
end

def eqnd_to_aexprs {Z} [has_one Z]
  : list (eqnd Z ℕ) → list (eqn Z ℕ)
| [] := []
| (x :: xs) := x.to_eqns ++ eqnd_to_aexprs xs

lemma eqnd_map_aexpr_commute {Z} [has_one Z] [semiring Z]
  (x : Z) (a : eqnd Z ℕ) :
  list.map (eqn.map_aexpr (aexpr.instantiate_head x)) (eqnd.to_eqns a) =
    (eqnd.to_eqns (eqnd.map_aexpr (aexpr.instantiate_head x) a))
:= begin
induction a; reflexivity
end

lemma eqnd_to_aexprs_map_aexpr_commutes {Z}
  [has_one Z] [semiring Z]
   (x : Z) (xs : list (eqnd Z ℕ))
  : list.map (eqn.map_aexpr (aexpr.instantiate_head x)) (eqnd_to_aexprs xs)
  = eqnd_to_aexprs (list.map (eqnd.map_aexpr (aexpr.instantiate_head x)) xs)
:= begin
induction xs; dsimp [eqnd_to_aexprs, list.map],
{ reflexivity },
{ rw ← ih_1, rw list.map_append, f_equal,
  rw eqnd_map_aexpr_commute,
}
end

lemma negation_statement_0_app_conjunction {A}
  (f : A → Prop) (xs ys : list A)
  : negation_statement_0 f (xs ++ ys)
  ↔ (list.foldr and true (list.map f xs) → negation_statement_0 f ys)
:= begin
induction xs; dsimp [list.foldr, negation_statement_0],
{ rw true_implies_iff, },
{ split; intros H,
  { intros H', induction H' with H1 H2,
    revert H2, rw ← ih_1, apply H, assumption,
  },
  { intros H', rw ih_1, intros H'',
    apply H, split; assumption }
}
end

lemma eqn_interp_map_aexpr_Z_Q
  : eqn.interp (λ (_x : ℕ), (0 : ℤ))
  = eqn.interp (λ (_x : ℕ), (0 : ℚ)) ∘ eqn.map_aexpr (aexpr.map coe)
:= begin
apply funext, intros e,
induction e with e e'; dsimp [function.comp, eqn.interp, eqn.map_aexpr],
rw Z_to_Q_le_iff,
rw Z_to_Q_interp, rw Z_to_Q_interp,
rw rat.coe_int_zero,
end

lemma eqnd_to_eqn_sound {A} [discrete_order_ring A]
  (nvars : ℕ) (xs : list (eqnd A ℕ))
  : eqn_negation_statement nvars (eqnd_to_aexprs xs)
  ↔ eqnd_negation_statement nvars xs
:= begin
revert xs,
induction nvars; intros xs; dsimp [eqn_negation_statement, eqnd_negation_statement],
{ induction xs; dsimp [negation_statement_0],
  { reflexivity },
  { rw eqnd.to_eqns_interp,
    dsimp [eqnd_to_aexprs],
    rw ← ih_1, rw negation_statement_0_app_conjunction,
  }
},
{ split; intros H,
  { intros x, specialize (H x),
    rw ← ih_1, rw ← eqnd_to_aexprs_map_aexpr_commutes,
    assumption, },
  { intros x, specialize (H x),
    rw ← ih_1 at H, rw ← eqnd_to_aexprs_map_aexpr_commutes at H,
    assumption }
 }
end

lemma Z_to_Q_sound_eqn (nvars : ℕ) (xs : list (eqn ℤ ℕ))
  : eqn_negation_statement nvars (xs.map (eqn.map_aexpr (aexpr.map coe)) : list (eqn ℚ ℕ))
  → eqn_negation_statement nvars xs
:= begin
revert xs,
induction nvars; intros xs; dsimp [eqn_negation_statement],
{ induction xs; dsimp [negation_statement_0],
  { intros H, assumption },
  { intros H H', apply ih_1, apply H,
    induction a with e e',
    dsimp [eqn.interp] at *,
    rw Z_to_Q_le_iff at H', repeat { rw Z_to_Q_interp at H' },
    dsimp [eqn.map_aexpr, eqn.interp],
    repeat { rw ← rat.coe_int_zero },
    assumption,
  }
},
{ intros H x, specialize (H x), rw list.map_map at H,
  rw eqn.map_aexpr_compose at H,
  rw ← instantiate_head_Z_to_Q at H,
  apply ih_1, rw list.map_map,
  rw eqn.map_aexpr_compose, assumption }
end

lemma aexpr_interp_N_Z (e : aexpr ℕ ℕ) (ctxt : ℕ → ℕ)
  : (↑(aexpr.interp ctxt e) : ℤ)
  = aexpr.interp (λ (x : ℕ), ↑(ctxt x)) (aexpr.map coe e)
:= begin
induction e; dsimp [aexpr.map, aexpr.interp],
rw int.coe_nat_mul, reflexivity, reflexivity,
rw int.coe_nat_add, rw [ih_1, ih_2],
end

lemma gt_lt {A} [has_lt A] (x y : A)
  : x > y = (y < x)
  := rfl

lemma ge_le {A} [has_le A] (x y : A)
  : x ≥ y = (y ≤ x)
  := rfl

lemma eqn_interp_N_Z (a : eqn ℕ ℕ) (ctxt : ℕ → ℕ)
  : eqn.interp ctxt a
  ↔ eqn.interp (λ x, (↑ (ctxt x) : ℤ)) (eqn.map_aexpr (aexpr.map coe) a)
:= begin
induction a with e e'; simp [eqn.interp, eqn.map_aexpr, aexpr.map],
{ rw ← int.coe_nat_le_coe_nat_iff,
  repeat {rw aexpr_interp_N_Z}, },
end

lemma eqnd_interp_N_Z (a : eqnd ℕ ℕ) (ctxt : ℕ → ℕ)
  : eqnd.interp ctxt a
  ↔ eqnd.interp (λ x, (↑ (ctxt x) : ℤ)) (eqnd.map_aexpr (aexpr.map coe) a)
:= begin
induction a; simp [eqnd.interp, eqnd.map_aexpr, aexpr.map],
{ rw ← int.coe_nat_le_coe_nat_iff,
  repeat {rw aexpr_interp_N_Z}, },
{ rw ← int.coe_nat_lt_coe_nat_iff,
  repeat {rw aexpr_interp_N_Z}, },
{ rw ← int.coe_nat_eq_coe_nat_iff,
  repeat {rw aexpr_interp_N_Z}, },
{ repeat { rw gt_lt },
  rw ← int.coe_nat_lt_coe_nat_iff,
  repeat {rw aexpr_interp_N_Z}, },
{ repeat { rw ge_le },
  rw ← int.coe_nat_le_coe_nat_iff,
  repeat {rw aexpr_interp_N_Z}, },
end

lemma Z_nonneg_roundtrip_N {x : ℤ}
  (H : 0 ≤ x)
  : ↑(int.to_nat x) = x
:= begin
induction x, reflexivity,
cases H,
end

lemma N_to_Z_sound_eqn (nvars : ℕ) (xs : list (eqn ℕ ℕ))
  : eqn_negation_statement nvars (xs.map (eqn.map_aexpr (aexpr.map coe)) : list (eqn ℤ ℕ))
  → eqn_negation_statement nvars xs
:= begin
revert xs,
induction nvars; intros xs; dsimp [eqn_negation_statement],
{ induction xs; dsimp [negation_statement_0],
  { intros H, assumption },
  { intros H H', apply ih_1, apply H,
    rw eqn_interp_N_Z at H',
    rw ← int.coe_nat_zero, assumption,
  }
},
{ intros H x, specialize (H x), rw list.map_map at H,
  rw eqn.map_aexpr_compose at H,
  rw ← instantiate_head_N_to_Z at H,
  apply ih_1, rw list.map_map,
  rw eqn.map_aexpr_compose, apply H,
}
end

lemma N_to_Z_sound_eqnd (nvars : ℕ) (xs : list (eqnd ℕ ℕ))
  : eqnd_negation_statement_nonneg nvars (xs.map (eqnd.map_aexpr (aexpr.map coe)) : list (eqnd ℤ ℕ))
  ↔ eqnd_negation_statement nvars xs
:= begin
revert xs,
induction nvars; intros xs; dsimp [eqnd_negation_statement_nonneg, eqnd_negation_statement],
{ induction xs; dsimp [negation_statement_0],
  { reflexivity },
  { rw ih_1,
    rw eqnd_interp_N_Z,
    rw ← int.coe_nat_zero,
  }
},
{ split,
  { intros H x, specialize (H x), rw list.map_map at H,
    rw eqnd.map_aexpr_compose at H,
    rw ← instantiate_head_N_to_Z at H,
    rw ← ih_1, rw list.map_map,
    rw eqnd.map_aexpr_compose, apply H,
    apply int.coe_zero_le
  },
  { intros H x x0,
    specialize (H x.to_nat),
    rw ← ih_1 at H,
    rw list.map_map at H, rw list.map_map,
    rw eqnd.map_aexpr_compose at H, rw eqnd.map_aexpr_compose,
    rw instantiate_head_N_to_Z at H,
    rw Z_nonneg_roundtrip_N at H, assumption, assumption,
  }
}
end

def always_true {A} [decidable_linear_order A] [semiring A]
  (e : eqn A ℕ)
  := ∀ ctxt, e.interp ctxt

def ctxt_extend {A} (f : ℕ → A) (x : A) : ℕ → A
| 0 := x
| (nat.succ n) := f n

lemma aexpr_interp_instantiate_head
  {A} [semiring A] (ctxt : ℕ → A)
  (e : aexpr A ℕ) (x : A)
  : (e.instantiate_head x).interp ctxt
  = e.interp (ctxt_extend ctxt x)
:= begin
induction e; dsimp [aexpr.instantiate_head, aexpr.interp],
{ cases a_1; reflexivity },
{ cases a; reflexivity },
{ reflexivity },
{ rw [ih_1, ih_2] }
end

lemma eqn_interp_instantiate_head
  {A} [semiring A] [decidable_linear_order A] (ctxt : ℕ → A)
  (e : eqn A ℕ) (x : A)
  : (e.map_aexpr (aexpr.instantiate_head x)).interp ctxt
  = e.interp (ctxt_extend ctxt x)
:= begin
induction e; dsimp [eqn.map_aexpr, eqn.interp],
repeat { rw aexpr_interp_instantiate_head },
end

lemma eqnd_interp_instantiate_head
  {A} [linear_ordered_comm_ring A] [decidable_linear_order A] (ctxt : ℕ → A)
  (e : eqnd A ℕ) (x : A)
  : (e.map_aexpr (aexpr.instantiate_head x)).interp ctxt
  = e.interp (ctxt_extend ctxt x)
:= begin
induction e; dsimp [eqnd.map_aexpr, eqnd.interp];
repeat { rw aexpr_interp_instantiate_head },
end

lemma always_true_instantiate_head
  {A} [semiring A] [decidable_linear_order A]
  (e : eqn A ℕ) (H : always_true e) (x : A)
  : always_true (e.map_aexpr (aexpr.instantiate_head x))
:= begin
dsimp [always_true] at *, intros ctxt,
rw eqn_interp_instantiate_head, apply H,
end

lemma eqn_negation_statement_always_true
  {A} [semiring A] [decidable_linear_order A]
  (nvars : ℕ) (xs : list (eqn A ℕ))
  (x : eqn A ℕ) (Hx : always_true x)
  : eqn_negation_statement nvars (x :: xs)
  → eqn_negation_statement nvars xs
:= begin
intros H, revert xs Hx x,
induction nvars;
  dsimp [eqn_negation_statement];
  intros xs x Hx H,
{ dsimp [negation_statement_0] at H,
  apply H, apply Hx },
{ intros x, specialize (H x),
  apply ih_1, tactic.swap, assumption,
  apply always_true_instantiate_head,
  assumption
}
end

lemma nonzero_constraints_nat_no_op (nvars nvars' : ℕ) (xs : list (eqn ℕ ℕ))
  : eqn_negation_statement nvars (nonzero_constraints nvars' ++ xs)
  → eqn_negation_statement nvars xs
:= begin
revert xs;
induction nvars'; dsimp [nonzero_constraints]; intros xs H,
{ apply H },
{ apply ih_1, apply eqn_negation_statement_always_true _ _ _ _ _,
  tactic.rotate 2, assumption,
  dsimp [always_true], intros ctxt,
  dsimp [eqn.interp, aexpr.interp], apply nat.zero_le,
}
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
{ induction a; dsimp [aexpr.instantiate_head, aexpr.no_big_vars],
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
{ destruct (nat_to_fin_option n.succ a),
  { intros Hnone, rw Hnone, dsimp [aexpr.var_map_default],
    cases a; dsimp [aexpr.instantiate_head],
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
    cases a; dsimp [aexpr.instantiate_head, aexpr.var_map_default],
    { dsimp [aexpr.to_linear_expr],
      rw instantiate_head_var_0,
      rw [mul_comm, mul_one],
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
{ induction es; dsimp [negation_statement_0],
    dsimp [interp_list_exprs, negation_statement_0] at a,
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

lemma satisfiable_bool_correct_eqn  (es : list (eqn ℚ ℕ))
  (nvars : ℕ)
  : list.band ((es.map eqn.to_aexpr).map (aexpr.no_big_vars_bool nvars)) = tt →
    satisfiable_bool' (interp_list_exprs (es.map eqn.to_aexpr) nvars) = ff →
    eqn_negation_statement nvars es
:= begin
intros H H',
apply eqn_to_aexpr_sound,
apply satisfiable_bool_correct; assumption,
end

lemma satisfiable_bool_correct_eqn_Z  (es : list (eqn ℤ ℕ))
  (nvars : ℕ)
  : list.band (((es.map (eqn.map_aexpr (aexpr.map coe)) : list (eqn ℚ ℕ)).map eqn.to_aexpr).map (aexpr.no_big_vars_bool nvars)) = tt →
    satisfiable_bool' (interp_list_exprs ((es.map (eqn.map_aexpr (aexpr.map coe))).map eqn.to_aexpr) nvars) = ff →
    eqn_negation_statement nvars es
:= begin
intros H H',
apply Z_to_Q_sound_eqn,
apply eqn_to_aexpr_sound,
apply satisfiable_bool_correct; assumption,
end

def eqn_Z_to_aexprs (es : list (eqnd ℤ ℕ))
  : list (aexpr ℚ ℕ)
  := ((eqnd_to_aexprs es).map (eqn.map_aexpr (aexpr.map coe))).map eqn.to_aexpr

lemma satisfiable_bool_correct_eqn_Z' (es : list (eqnd ℤ ℕ))
  (nvars : ℕ)
  : list.band ((eqn_Z_to_aexprs es).map (aexpr.no_big_vars_bool nvars)) = tt →
    satisfiable_bool' (interp_list_exprs (eqn_Z_to_aexprs es) nvars) = ff →
    eqnd_negation_statement nvars es
:= begin
intros H H',
rw ← eqnd_to_eqn_sound,
apply satisfiable_bool_correct_eqn_Z; assumption,
end

def eqn_N_to_aexprs (nvars : ℕ) (es : list (eqnd ℕ ℕ))
  : list (aexpr ℚ ℕ)
  := (((nonzero_constraints nvars ++ eqnd_to_aexprs es).map
       (eqn.map_aexpr (aexpr.map coe)) : list (eqn ℤ ℕ)).map
       (eqn.map_aexpr (aexpr.map coe)) : list (eqn ℚ ℕ)).map
        eqn.to_aexpr

lemma satisfiable_bool_correct_eqn_N (es : list (eqnd ℕ ℕ))
  (nvars : ℕ)
  : list.band ((eqn_N_to_aexprs nvars es).map (aexpr.no_big_vars_bool nvars)) = tt →
    satisfiable_bool' (interp_list_exprs (eqn_N_to_aexprs nvars es) nvars) = ff →
    eqnd_negation_statement nvars es
:= begin
intros H H',
rw ← eqnd_to_eqn_sound nvars es,
apply nonzero_constraints_nat_no_op,
apply N_to_Z_sound_eqn,
apply satisfiable_bool_correct_eqn_Z;
assumption,
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
  let (xs', n) := intern_var xs P in pure (``(aexpr.var1 %%(n.reflect)), xs')

meta def reify_formula_helper
  : list expr → expr → tactic (option (expr ff × list expr))
| xs `(has_le.le %%ee (has_zero.zero _)) := some <$> reify_axpr_helper xs ee
| xs other := pure none

meta def reify_eqn_helper
  : list expr → expr → tactic (option (expr ff × list expr))
| xs `(has_le.le %%ee %%ee') := do
  (e, xs') ← reify_axpr_helper xs ee,
  (e', xs'') ← reify_axpr_helper xs' ee',
  pure (``(eqn.le %%e %%e'), xs'')
| xs other := pure none

meta def reify_eqnd_helper
  : list expr → expr → tactic (option (expr ff × list expr))
| xs `(has_le.le %%ee %%ee') := do
  (e, xs') ← reify_axpr_helper xs ee,
  (e', xs'') ← reify_axpr_helper xs' ee',
  pure (``(eqnd.le %%e %%e'), xs'')
| xs `(has_lt.lt %%ee %%ee') := do
  (e, xs') ← reify_axpr_helper xs ee,
  (e', xs'') ← reify_axpr_helper xs' ee',
  pure (``(eqnd.lt %%e %%e'), xs'')
| xs `(eq %%ee %%ee') := do
  (e, xs') ← reify_axpr_helper xs ee,
  (e', xs'') ← reify_axpr_helper xs' ee',
  pure (``(eqnd.eq %%e %%e'), xs'')
| xs `(gt %%ee %%ee') := do
  (e, xs') ← reify_axpr_helper xs ee,
  (e', xs'') ← reify_axpr_helper xs' ee',
  pure (``(eqnd.gt %%e %%e'), xs'')
| xs `(ge %%ee %%ee') := do
  (e, xs') ← reify_axpr_helper xs ee,
  (e', xs'') ← reify_axpr_helper xs' ee',
  pure (``(eqnd.ge %%e %%e'), xs'')
| xs other := pure none

meta def reify_all_helper (f : list expr → expr → tactic (option (expr ff × list expr)))
  : list expr → list expr → tactic (list (expr ff) × list expr)
| ctxt [] := pure ([], ctxt)
| ctxt (x :: xs) := do
  r ← f ctxt x,
  match r with
  | some (x', ctxt') := do
    (xs', ctxt'') ← reify_all_helper ctxt' xs,
    pure (x' :: xs', ctxt'')
  | none := reify_all_helper ctxt xs
  end

meta def my_reify (f : list expr → expr → tactic (option (expr ff × list expr))) (es : list expr)
  : tactic (list (expr ff) × list expr)
  := reify_all_helper f [] es

meta def make_list : list expr → expr ff
| [] := ``(list.nil)
| (x :: xs) := ``(list.cons %%x %%(make_list xs))

meta def make_nat : ℕ → expr ff
| 0 := ``(0)
| (nat.succ n) := ``(nat.succ %%(make_nat n))

meta def reify_hyps_numvars (f : list expr → expr → tactic (option (expr ff × list expr)))
   : tactic (expr × expr ff) := do
    ctx ← local_context,
    ctx_types ← ctx.mmap infer_type,
    (hyps, ctxt) ← my_reify f ctx_types,
    hyps' ← mmap i_to_expr hyps,
    let ctxt' := make_list ctxt,
    let num_vars := make_nat ctxt.length,
    let hyps'' := make_list hyps',
    hyps''' ← i_to_expr hyps'',
    return (hyps''', num_vars)

meta def fourier_Q_core : tactic unit := do
    (hyps, num_vars) ← reify_hyps_numvars reify_formula_helper,
    ap_expr ← i_to_expr ``(satisfiable_bool_correct %%hyps %%num_vars),
    tactic.apply ap_expr

meta def fourier_Q_core_eqn : tactic unit := do
    (hyps, num_vars) ← reify_hyps_numvars reify_eqn_helper,
    ap_expr ← i_to_expr ``(satisfiable_bool_correct_eqn %%hyps %%num_vars),
    tactic.apply ap_expr

meta def fourier_Z_core_eqn : tactic unit := do
    (hyps, num_vars) ← reify_hyps_numvars reify_eqn_helper,
    ap_expr ← i_to_expr ``(satisfiable_bool_correct_eqn_Z %%hyps %%num_vars),
    tactic.apply ap_expr

meta def fourier_Z_core_eqn' : tactic unit := do
    (hyps, num_vars) ← reify_hyps_numvars reify_eqnd_helper,
    ap_expr ← i_to_expr ``(satisfiable_bool_correct_eqn_Z' %%hyps %%num_vars),
    tactic.apply ap_expr

meta def fourier_N_core_eqn : tactic unit := do
    (hyps, num_vars) ← reify_hyps_numvars reify_eqnd_helper,
    ap_expr ← i_to_expr ``(satisfiable_bool_correct_eqn_N %%hyps %%num_vars),
    tactic.apply ap_expr

end tactic.interactive

lemma my_lemma
  (x y z : ℚ)
  (Hx : 1 * x + 3 ≤ 0)
  (Hy : -5 ≤ 2 * x)
  (Hz : (0 : ℚ) ≤ 0)
  : false
:= begin
fourier_Q_core_eqn; reflexivity <|> assumption,
end

lemma my_lemma2
  (x y z : ℤ)
  (Hx : 1 * x + 3 ≤ 0)
  (Hy : -2 * x ≤ 5)
  (Hz : (0 : ℤ) ≤ 0)
  : false
:= begin
fourier_Z_core_eqn; reflexivity <|> assumption,
end

lemma my_lemma3
  (x y z : ℤ)
  (Hx : 1 * x + 3 < 0)
  (Hy : -2 * x ≤ 5)
  (Hz : (0 : ℤ) ≤ 0)
  : false
:= begin
fourier_Z_core_eqn'; reflexivity <|> assumption,
end

lemma my_lemma4
  (x : ℤ)
  (Hx : x < 3)
  (Hy : x ≥ 3)
  : false
:= begin
fourier_Z_core_eqn'; reflexivity <|> assumption,
end

lemma my_lemma5
  (n : ℕ)
  (H : n < 0)
  : false
:= begin
fourier_N_core_eqn; reflexivity <|> assumption,
end