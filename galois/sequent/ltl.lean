import .core galois.temporal.temporal order.complete_lattice

universes u

open temporal lattice

namespace sequent

instance subset_complete_lattice {A : Type u} : complete_lattice (subset A)
:= begin
apply lattice.complete_lattice_fun,
end

instance subset_cha {A : Type u} : cha (subset A)
:= begin
constructor, tactic.rotate 2, apply_instance,
constructor,
intros P Q, exact (λ x, P x → Q x),
intros, intros x Γx Px,
apply a, split; assumption,
intros, intros x ΓPx, induction ΓPx with Γx Px,
apply a; assumption
end

instance tProp_cha {T : Type u} : cha (tProp T)
  := sequent.subset_cha

lemma tautology {T : Type u} {A : tProp T}
  (H : rlist.nil ⊢ A)
  : ⊩ A
:= begin
intros tr, apply H, constructor,
end

lemma tautology_iff {T : Type u} {A : tProp T}
  : (rlist.nil ⊢ A) ↔ (⊩ A)
:= begin
split; intros H,
intros tr, apply H, constructor,
intros x Hx, apply H,
end

inductive formula (T : Type) (vTy : Type) : Type
| var {} : vTy → formula
| top {} : formula
| bot {} : formula
| and {} : formula → formula → formula
| or {} : formula → formula → formula
| always {} : formula → formula
| eventually {} : formula → formula

namespace formula
def interp {T : Type} {vTy : Type} (ctxt : vTy → tProp T)
  : formula T vTy → tProp T
| (var x) := ctxt x
| top := ⊤
| bot := ⊥
| (and P Q) := interp P ⊓ interp Q
| (or P Q) := interp P ⊔ interp Q
| (always P) := □ (interp P)
| (eventually P) := ◇ (interp P)
end formula

instance formula_decidable_eq {T : Type} {vTy : Type}
  [decidable_eq vTy] : decidable_eq (formula T vTy)
  := by tactic.mk_dec_eq_instance

def formula_entails {T : Type} {vTy : Type}
  (Γ : rlist (formula T vTy)) (A : formula T vTy)
  := ∀ ctxt, Γ.map (formula.interp ctxt) ⊢ A.interp ctxt

def interp_impl {T : Type} {vTy : Type}
  (Γ : rlist (formula T vTy)) (A : formula T vTy) (ctxt : vTy → tProp T)
  : formula_entails Γ A → Γ.map (formula.interp ctxt) ⊢ A.interp ctxt
:= begin
intros H, apply H,
end

def formula_entails_auto {T : Type} {vTy : Type}
  [decidable_eq vTy]
  (Γ : rlist (formula T vTy))
  : ∀ A : formula T vTy, option (plift (formula_entails Γ A))
| formula.top := some (plift.up
  begin
  dsimp [formula_entails, formula.interp], intros ctxt,
  apply @entails_top _ sequent.tProp_cha,
   end)
| formula.bot := none
| (formula.and P Q) := do
  plift.up HP ← formula_entails_auto P,
  plift.up HQ ← formula_entails_auto Q,
  some (plift.up begin
  unfold formula_entails, intros,
  dsimp [formula.interp],
  apply @split _ sequent.tProp_cha, apply HP, apply HQ,
  end)
| (formula.or P Q) := (do
  plift.up HP ← formula_entails_auto P,
  some (plift.up (begin
     intros x, dsimp [formula.interp],
     apply @left _ sequent.tProp_cha, apply HP
     end)))
  <|>
  (do
  plift.up HQ ← formula_entails_auto Q,
  some (plift.up (begin
     intros x, dsimp [formula.interp],
     apply @right _ sequent.tProp_cha, apply HQ
     end)))
| x := if H : x ∈ Γ then some (plift.up begin
     intros ctxt, apply @assumption _ sequent.tProp_cha,
     apply rlist.map_mem, assumption
  end) else none

meta def intern_var (xs : list expr) (e : expr) : list expr × ℕ
  := (if e ∈ xs then xs else xs ++ [e], xs.index_of e)

meta def reify_helper
  : list expr → expr → tactic (expr ff × list expr)
| xs `((⊤ : tProp %%T)) := pure (``(formula.top), xs)
| xs `((⊥ : tProp %%T)) := pure (``(formula.bot), xs)
| xs `(always %%P) := do
    (P', xs') ← reify_helper xs P,
    pure (``(formula.always %%P'), xs')
| xs `(eventually %%P) := do
    (P', xs') ← reify_helper xs P,
    pure (``(formula.eventually %%P'), xs')
| xs `(%%P ⊓ %%Q) := do
    (P', xs') ← reify_helper xs P,
    (Q', xs'') ← reify_helper xs' Q,
    pure (``(formula.and %%P' %%Q'), xs'')
| xs `(%%P ⊔ %%Q) := do
    (P', xs') ← reify_helper xs P,
    (Q', xs'') ← reify_helper xs' Q,
    pure (``(formula.or %%P' %%Q'), xs'')
| xs P := let (xs', n) := intern_var xs P in pure (``(formula.var %%(n.reflect)), xs')

meta def reify_all_helper (e : expr)
  : list expr → list expr → tactic (list (expr ff) × expr ff × list expr)
| ctxt [] := do
  (e', ctxt') ← reify_helper ctxt e,
  pure ([], e', ctxt')
| ctxt (x :: xs) := do
  (x', ctxt') ← reify_helper ctxt x,
  (xs', e', ctxt'') ← reify_all_helper ctxt' xs,
  pure (x' :: xs', e', ctxt'')

meta def reify (es : list expr) (e : expr)
  : tactic (list (expr ff) × expr ff × list expr)
  := reify_all_helper e [] es

end sequent

namespace tactic.interactive
namespace sequent

open tactic lean lean.parser
open interactive interactive.types expr

meta def get_rlist : expr → tactic (list expr)
| `(rlist.snoc %%xs %%x) := do
   xs' ← get_rlist xs,
   pure (x :: xs')
| `(rlist.nil) := pure []
| _ := tactic.fail "uh-oh"

meta def make_list : list expr → expr ff
| [] := ``(list.nil)
| (x :: xs) := ``(list.cons %%x %%(make_list xs))

meta def make_rlist : list (expr ff) → expr ff
| [] := ``(rlist.nil)
| (x :: xs) := ``(rlist.snoc %%(make_rlist xs) %%x)

def list.nth_def {α : Type u} (xs : list α) (default : α) (n : ℕ) : α
:= match xs.nth n with
| (some x) := x
| none := default
end

meta def on_sequent_goal {A} (f : expr → expr → tactic A)
  : tactic A := do
  tgt ← target,
  tgt' ← instantiate_mvars tgt,
  match tgt' with
  | `(%%Γ ⊢ %%P) := f Γ P
  | _ := tactic.fail "not a logical entailment"
  end

meta def reify_goal : tactic unit :=
  on_sequent_goal $ λ xs P, do
    ty ← infer_type P >>= whnf,
    xs' ← get_rlist xs,
    (xs', P', ctxt) ← sequent.reify xs' P,
    let ctxt' := make_list ctxt,
    let xs'' := make_rlist xs',
    xs''' ← i_to_expr xs'',
    P'' ← i_to_expr P',
    ctxtf ← i_to_expr ``(list.nth_def %%ctxt' ⊥),
    e ← i_to_expr ``(sequent.interp_impl %%xs''' %%P'' %%ctxtf),
    tactic.apply e

meta def entails_tactic (e : parse texpr) : tactic unit := do
  tgt ← target,
  tgt' ← instantiate_mvars tgt,
  match tgt' with
  | `(sequent.formula_entails %%Γ %%A) := do
    e' ← i_to_expr ``(%%e %%Γ %%A) >>= whnf,
    match e' with
    | `(some (plift.up %%x)) := tactic.apply x
    | _ := tactic.fail "Didn't get some"
    end
  | _ := tactic.fail "not a formula entailment"
  end

meta def intros := repeat (apply ``(sequent.intro _))
meta def revert := apply ``(sequent.revert _)
meta def left := apply ``(sequent.left _)
meta def right := apply ``(sequent.right _)
meta def split := apply ``(sequent.split _ _)
meta def prove_mem :=
  apply ``(rlist.mem.here) <|> (do apply ``(rlist.mem.there), prove_mem)
meta def assumption := do
  apply ``(sequent.assumption _),
  prove_mem
meta def apply (e : parse texpr) := do
  on_sequent_goal $ λ Γ P, do
    tactic.interactive.apply ``(sequent.apply_lemma %%Γ %%P %%e),
    repeat tactic.constructor

meta def assert (e : parse texpr) := do
  on_sequent_goal $ λ Γ P, do
    tactic.interactive.apply ``(sequent.cut %%Γ %%P %%e)

end sequent
end tactic.interactive