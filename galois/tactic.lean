import .option
import galois.list.member

universes u v

open tactic lean lean.parser
open interactive interactive.types expr

local postfix *:9001 := many

namespace tactic.interactive

private
meta def specialize_get_name : expr → tactic name
| (app f _) := specialize_get_name f
| (local_const _ n _ _) := pure n
| _ := fail "Not an application of a local constant"

/-- The analogue of Coq's `specialize` tactic -/
meta def specialize (H : parse texpr) : tactic unit :=
  do result ← i_to_expr H,
     id ← specialize_get_name result,
     n ← get_unused_name id none,
     note n none result,
     to_remove ← get_local id, 
     tactic.clear to_remove,
     tactic.rename n id

def congr_arg_f_equal {A : Sort u} {B : Sort v} {f f' : A → B}
  {x x' : A} : f = f' → x = x' → f x = f' x'
:= begin
intros H, induction H, intros H, induction H, reflexivity
end

/-- The analogue of Coq's `f_equal` tactic -/
meta def f_equal : tactic unit :=
  tactic.focus1 $
  try (do apply ``(@congr_arg_f_equal),
  tactic.focus [ reflexivity <|> f_equal, try reflexivity ])

meta def apply_in_aux : expr → tactic expr
| (pi x info ty e) := do
     x' ← mk_meta_var ty,
     apply_in_aux (e.instantiate_var x')
| e := pure e

/-- The analogue of Coq's `apply _ in _` tactic.
    Usage: `apply e in H` in Coq corresponds to
           `apply_in H e` using this tactic in Lean
 -/
meta def apply_in (H : parse ident) (e : parse texpr) 
  : tactic unit := focus1 $ do
  e' ← i_to_expr e,
  ty_e ← infer_type e' >>= whnf,
  goal ← apply_in_aux ty_e,
  n ← get_unused_name H,
  tactic.assert n goal,
  tactic.apply e',
  He ← get_local H,
  any_goals (tactic.apply He),
  any_goals (do clear [H], rename n H)

end tactic.interactive

/- I'm trying to make a decidable equality tactic -/
def hlist : list (Type u) → Type (u+1)
| [] := punit
| (x :: xs) := x × hlist xs

instance decidable_eq_unit : decidable_eq punit 
:= begin 
intros x y, induction x, induction y,
apply decidable.is_true, reflexivity
end

def decidable_eq_prod {A : Type u} {B : Type v}
  (HA : decidable_eq A) (HB : decidable_eq B)
  : decidable_eq (A × B)
:= begin
apply_instance,
end

namespace hlist
def decidable_eq_args {xs : list (Type u)} (H : ∀ x : xs.member, decidable_eq (x.value) )
  : decidable_eq (hlist xs)
:= begin
induction xs; simp [hlist],
apply_instance, apply decidable_eq_prod,
specialize (H list.member.here), apply H,
apply ih_1, intros,
apply (H x.there)
end
end hlist

def simp_function : list (Type u) → Type u → Type u
| [] ret := ret
| (a :: args) ret := a → simp_function args ret

namespace simp_function
def ap : ∀ {args : list (Type u)} {ret : Type u}
  (f : simp_function args ret) (xs : hlist args), ret
| [] ret f _ := f
| (a :: args) ret f (x, xs) := ap (f x) xs

end simp_function

lemma decidable_eq_inj {A : Sort u} {B : Sort v} (f : A → B)
  (f_inj : ∀ x y : A, f x = f y → x = y)
  (decA : decidable_eq A) : ∀ x y : A, decidable (f x = f y)
:= begin
intros x y,
have H := decA x y, induction H with H H,
{ apply decidable.is_false, intros contra,
  apply H, apply f_inj, assumption },
{ apply decidable.is_true, f_equal, assumption }
end

lemma decidable_eq_ap {args : list (Type u)} {ret : Type u}
  (f : simp_function args ret) 
  (f_inj : ∀ xs ys, f.ap xs = f.ap ys → xs = ys)
  (dec_args : ∀ x : args.member, decidable_eq (x.value))
  (xs ys : hlist args)
  : decidable (f.ap xs = f.ap ys)
:= begin
apply decidable_eq_inj, apply f_inj,
apply hlist.decidable_eq_args dec_args
end

namespace tactic.interactive
meta def constructor_inj : tactic unit := do
  x ← tactic.get_unused_name "x" none,
  y ← tactic.get_unused_name "y" none,
  H ← tactic.get_unused_name "H" none,
  tactic.interactive.intros [x, y, H],
  Hexpr ← tactic.get_local H,
  tactic.injection Hexpr,
  return unit.star
end tactic.interactive