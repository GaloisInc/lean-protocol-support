/- A shallow embedding of temporal logic -/

import galois.tactic
import galois.nat.lemmas
import galois.subset.subset

universe variables u v

open subset

namespace temporal

/--An ordered series of events over states --/
def trace (T : Type u) : Type u := nat -> T

/--Type of Propositions over traces --/
@[reducible]
def tProp (T : Type u) := subset (trace T)

/- This defines a simp attribute named ltl
   later we can say "simp with ltl" in order
   to simplify any rule with this attribute -/
run_cmd mk_simp_attr `ltl
run_cmd mk_simp_attr `tImp

/--
Move a trace forward in time by n
-/
@[ltl]
def delayn {T : Type u} (n : ℕ) (tr : trace T) := (λ t : ℕ, tr (t + n))

/--
If we move forward twice, we can move forward once by the sum
-/
lemma delayn_combine {T : Type u} (n k : ℕ) (tr : trace T)
  : delayn k (delayn n tr) = delayn (k + n) tr
:= begin
apply funext, intros n, simp with ltl,
end


/--
Delay 0 does nothing
-/
lemma delayn_zero {T : Type u} (tr : trace T)
  : delayn 0 tr = tr := rfl

/--
Lift a prop into ltl at the given time
-/
@[ltl]
def nextn {T : Type u} (n : ℕ) (P : tProp T) : tProp T
  := λ tr, P (delayn n tr)

/--
We can combine multiple nextn
-/
lemma nextn_combine {T : Type u} (n k : ℕ) (P : tProp T)
  : nextn k (nextn n P) = nextn (n + k) P
:= begin
unfold nextn, apply funext, intros, rw delayn_combine
end

/-- Proposition P holds in the next state notation ◯ \ciO --/
@[ltl]
def next {T : Type u} : tProp T → tProp T := nextn 1

notation `◯` := next

/--
Nextn maintains decidability
-/
instance nextn_decidable {T : Type u} (P : tProp T) [decidable_pred P]
  (n : ℕ) : decidable_pred (nextn n P)
:= begin unfold nextn, apply_instance, end

/--
next maintains decidability
-/
instance next_decidable {T : Type u} (P : tProp T) [decidable_pred P]
  : decidable_pred (◯ P)
:= begin unfold next, apply_instance end

/-- Proposition P always holds notation □ \B --/
@[ltl]
def always {T: Type u} (P : tProp T) : tProp T :=
-- given a trace, P holds no matter how far forward we move the trace
 λ (tr : trace T), ∀ n : ℕ, P (delayn n tr)

notation `□` := always

/-- Proposition P eventually holds notation ◇ \dia -/
@[ltl]
def eventually {T: Type u} (P : tProp T) : tProp T :=
-- given a trace, we can find some n such that advancing
-- the trace by n allows p to hold on that trace
 λ (tr : trace T), ∃ n : ℕ, P (delayn n tr)

notation `◇` := eventually

/-- Until, notation \MCU --/
@[ltl]
def until {T : Type u} (P Q : tProp T) : tProp T :=
λ (tr : trace T), ∃ n, Q (delayn n tr) /\ (∀ n', n' < n -> P (delayn n' tr))

-- \MCU
infix `𝓤` : 50 := until

@[ltl]
def tInj1 {T: Type u} (R : Prop -> Prop) (P : tProp T) :=
λ (tr : trace T), R (P tr)

/-- Standard negation on tProps --/
@[ltl]
def tNot {T : Type u} (P : tProp T ) := tInj1 not P

/-- Proposition P holds for the first time -/
@[ltl]
def first {T : Type u} (P: tProp T) : tProp T := tNot P 𝓤 P


@[ltl, tImp]
def tInj2 {T: Type u} (R : Prop -> Prop -> Prop) (P Q : subset T) :=
λ (tr : T), R (P tr) (Q tr)

/-- Lifting of iff --/
@[ltl, tImp]
def tIff {T : Type u} (P Q : tProp T) : tProp T :=
tInj2 iff P Q

infixr `<=>` : 50 := tIff

/-- P holds at the nth step of some trace --/
@[ltl]
def later {T : Type u} (P : subset T) (n: nat) : tProp T :=
λ (tr : trace T), P (tr n)

/-- P holds at the first step of trace --/
@[ltl]
def now {T : Type u} (P: T -> Prop) := later P 0

/-- later maintains decidability-/
instance later_decidable {T : Type u} (P : T → Prop)
  (n : ℕ) [decidable_pred P]
  : decidable_pred (later P n)
:= begin
unfold later, apply_instance,
end

/-- now maintains decidability-/
instance now_decidable {T : Type u} (P : T → Prop) [decidable_pred P]
  : decidable_pred (now P)
:= begin
unfold now, apply_instance,
end

lemma later_mono (T : Type u) (n : ℕ) : monotone (λ P, @later T P n) :=
begin
intros P Q PQ tr, apply PQ,
end

lemma now_mono (T : Type u) : monotone (@now T) :=
begin
unfold monotone now, apply later_mono,
end

/-- Fairness constraints on a trace require that
    something happens infinitely often --/
@[ltl]
def fair {T : Type u} (P : tProp T) := □ (◇ P)

notation `⊩` P := forall tr, P tr

lemma eventually_always_mono {T : Type u} (A B : tProp T)
  : ⊩ □ (A => B) => ◇ A => ◇ B
:= begin
intros tr AB HA, induction HA with k HA,
unfold eventually, existsi k,
apply AB, assumption
end

lemma eventually_mono {T : Type u} (A B : tProp T)
  (AB : A ≤ B)
  : ◇ A ≤ ◇ B
:= begin
intros tr HA, apply eventually_always_mono,
intros n, apply AB, assumption
end

lemma until_always_mono {T : Type u} {A B P : tProp T}
  : ⊩ □ (A => B) => A 𝓤 P => B 𝓤 P
:= begin
intros tr AB AP, induction AP with k Hk,
induction Hk with H1 H2,
unfold until, existsi k, split, assumption,
intros, apply AB, apply H2, assumption
end

lemma until_mono {T : Type u} {A B P : tProp T}
  (AB : A ≤ B)
  : (A 𝓤 P) ≤ (B 𝓤 P)
:= begin
intros tr AP,  apply until_always_mono,
intros n, apply AB, assumption
end

lemma until_always_mono_r {T : Type u} {P A B : tProp T}
  : ⊩ □ (A => B) => P 𝓤 A => P 𝓤 B
:= begin
intros tr AB H, induction H with k Hk,
induction Hk with H1 H2,
constructor, split, apply AB, assumption, assumption
end

lemma and_imp_l {T : Type u} (P Q : tProp T)
  : ⊩ (P ∩ Q) => P
:= begin
intros tr H, induction H with HP HQ, assumption,
end

lemma and_imp_r {T : Type u} (P Q : tProp T)
  : ⊩ (P ∩ Q) => Q
:= begin
intros tr H, induction H with HP HQ, assumption,
end

lemma eventually_and_r {T : Type u} (P Q : tProp T)
 : ⊩ ◇ (P ∩ Q) => ◇ Q
:= begin
apply eventually_mono, apply and_imp_r,
end

/-- Pull out implication from always --/
lemma always_imp : forall {T : Type u} (P Q : tProp T),
(⊩ always (P => Q)) -> ((⊩ always P) -> (⊩ always Q)) :=
begin
simp with ltl,
intros,
    apply a,
    apply a_1,
end

lemma always_tImp : forall {T : Type u} (P Q : tProp T),
(⊩ □ (P => Q)) -> (⊩ □ P => □ Q) :=
begin
intros, intros H n, apply a, apply H,
end

lemma always_tautology {T : Type u} (P : tProp T) :
(⊩ P) → (⊩ □ P) :=
begin
intros, intros n, apply a,
end

/-- pull out top level implication --/
lemma imp_e : ∀ {T : Type u} (P Q : tProp T),
(⊩ (P => Q)) -> ((⊩ P) -> (⊩ Q)) :=
begin
intros, apply a, apply a_1
end

lemma always_mono {T : Type u} (P Q : tProp T)
  (H : P ≤ Q)
  : □ P ≤ □ Q
:= begin
intros tr HP n, apply H, apply HP,
end

lemma nextn_mono {T : Type u} {P Q : tProp T}
  (H : P ≤ Q) (n : ℕ)
  : nextn n P ≤ nextn n Q
:= begin
unfold nextn, intros x H', apply H, assumption
end

lemma next_mono {T : Type u} {P Q : tProp T}
 (H : P ≤ Q) : ◯ P ≤ ◯ Q
 := nextn_mono H 1

/-- always distributes over and --/
lemma always_and {T: Type u} (P Q : tProp T) :
 □ P ∩ □ Q = □ (P ∩ Q)
:= begin
apply funext, intros tr, apply propext,
split; intros H,
{ induction H with HP HQ,
  intros n, constructor, apply HP, apply HQ },
{ constructor,
  { apply always_mono, apply (and_imp_l _ Q), assumption },
  { apply always_mono, apply (and_imp_r P _), assumption }
}
end

def repeat_next {t : Type u} (P : t -> Prop) : nat -> tProp t
| 0 := later P 0
| (nat.succ n') := next (repeat_next n')

/-- lift_at is the same as repeated applictions of next --/
lemma lift_at_n : forall {T : Type u} (P : T -> Prop),
    repeat_next P = later P :=
begin
intros, apply funext, intros n,
apply funext, induction n; intros; simp [repeat_next],
unfold next nextn,
rw ih_1, simp [later, delayn],
end

/-- equivalence between eventually and until tt --/
lemma eventually_until {T : Type u} (P: tProp T) :
  ◇ P = (tt 𝓤 P)
 :=
begin
apply funext, intro tr, apply propext,
split; intros H,
{ induction H with k Hk,
  unfold until, existsi k, split, assumption,
  intros, trivial,
},
{
  induction H with k Hk,
  induction Hk with Hk1 Hk2,
  unfold eventually, existsi k, assumption
}
end


lemma congr_arg_app {T : Type u} ( P : T -> Prop) :
forall a1 a2,
P a1 -> a1 = a2 -> P a2 :=
begin
intros,
subst a1,
assumption
end

lemma ne0_succ_exists : forall n : nat,
¬ n = 0 ->
exists n', n = nat.succ n' :=
begin
intros,
cases n,
{ contradiction },
apply exists.intro,
reflexivity
end

lemma always_and_next {T : Type u} (P : tProp T) :
 (□ P) = (P ∩ ◯ (□ P)) :=
begin
apply funext, intros tr,
apply propext, split; intros H,
{
    constructor,
    { rw ← (delayn_zero tr),
      apply H },
    {
        intro n,
        specialize (H (n + 1)),
        rw delayn_combine, assumption
    }
},
{
    induction H with H0 HS,
    intros n, cases n, rw delayn_zero,
    assumption,
    apply HS
}
end

lemma next_delay {T : Type u} {P : tProp T}
  (n : ℕ) (tr : trace T)
  (H : ◯ P (delayn n tr))
  : P (delayn (nat.succ n) tr)
:= begin
dsimp [next, nextn] at H,
rw delayn_combine at H,
rw add_comm at H, assumption
end

lemma temporal_induction {T : Type u} (P : tProp T)
  : ⊩ (P => □ (P => (◯ P)) => □ P) :=
begin
intros tr H0 HS n,
induction n,
{ rw delayn_zero, assumption },
{ specialize (HS a ih_1), apply next_delay, assumption }
end

lemma temporal_induction' {T : Type u} : ∀ (P : tProp T),
  ∀ trace, P trace -> □ (P => (◯ P)) trace -> □ P trace
 := temporal_induction

lemma always_implies_eventually {T : Type u}
  (P Q : tProp T) :
⊩ □ (P => Q) => ◇ P => ◇ Q
:= begin
intros tr PQ evP,
induction evP with k Hk,
constructor, apply PQ, assumption
end

lemma next_eventually {T : Type u} (P : tProp T)
  : ⊩ ◯ P => ◇ P
:= begin
intros tr H, constructor, assumption
end

lemma eventually_return {T : Type u} (P : tProp T)
  : ⊩ P => ◇ P
:= begin
intros tr H, constructor, rw delayn_zero, assumption
end

lemma eventually_idempotent {T : Type u} (P : tProp T)
  : ◇ (◇ P) = ◇ P
:= begin
apply funext, intro tr, apply propext, split; intros H,
{
induction H with k Hk,
induction Hk with n Hn,
rw delayn_combine at Hn,
constructor, assumption
},
{ apply eventually_return, assumption }
end

lemma always_idempotent {T : Type u} (P : tProp T)
  : □ (□ P) = □ P
:= begin
apply funext, intro tr, apply propext, split; intros H,
{ specialize (H 0), rw delayn_zero at H, assumption },
{ intros n k, rw delayn_combine, apply H }
end


lemma eventually_cut {T : Type u} {P Q : tProp T}
  : ⊩ ◇ P => □ (P => ◇ Q) => ◇ Q
:= begin
intros tr HP PQ,
rw ← eventually_idempotent,
revert HP, apply eventually_always_mono, assumption,
end

lemma fair_cut {T : Type u} {P Q : tProp T}
  : ⊩ fair P => □ (P => ◇ Q) => fair Q
:= begin
intros tr fairP PQ n,
apply eventually_cut, apply fairP,
rw ← always_idempotent at PQ,
apply PQ,
end

/-- If I have a type A with a well-founded relation R on it, 
    then if for every state that measures to some `x : A`, 
      if I am at `x` now, I will eventually reach a smaller state or Q happens,
    then if I am in some state that yields an `A`, eventually Q happens.
   Note: your `meas` will likely take the form of `now _` -/
lemma always_eventually_well_founded_option {T : Type u} {A : Type v}
  {R : A → A → Prop} (wf : well_founded R)
  (meas : trace T → option A) (Q : tProp T)
  (tr : trace T)
  (H : ∀ x : A, □ ((λ s, meas s = some x) => ◇ (((λ s, 
  match meas s with 
  | none := false
  | (some m) := R m x end)) ∪ Q)) tr)
  (z : A) : □ ((λ s, meas s = some z) => ◇ Q) tr
:= begin
have wf_ind := λ x y z, @well_founded.induction _ _ wf x z y,
revert z,
apply (@wf_ind (λ (z : A), □ ((λ s, meas s = some z)=>◇ Q) tr)),
intros x IH n Hn,
specialize (H x n Hn),
induction H with k Hk,
induction Hk with Hk Hk,
{ generalize Hm : ((meas (delayn k (delayn n tr)))) = m,
  rw Hm at Hk,
  induction m;
    dsimp at Hk,
  contradiction,
  specialize (IH _ Hk (k + n)),
  rw ← eventually_idempotent,
  constructor, rw delayn_combine, apply IH,
  simp with ltl, simp with ltl at Hm,
  assumption
  },
{ constructor, assumption }
end

/-- Like the above but without partiality: every state is required 
    to have some measure.
-/
lemma always_eventually_well_founded {T : Type u} {A : Type v}
  {R : A → A → Prop} (wf : well_founded R)
  (meas : trace T → A) (Q : tProp T)
  (tr : trace T)
  (H : ∀ x : A, □ ((λ s, meas s = x) => ◇ (((λ s, R (meas s) x)) ∪ Q)) tr)
  : □ (◇ Q) tr
:= begin
have H1 := always_eventually_well_founded_option wf (λ x, some (meas x)) Q tr,
intros n, apply H1; clear H1,
{ intros x n H1,
  specialize (H x n), simp with ltl at H1,
  injection H1 with H1', clear H1, subst x,
  apply H, simp with ltl },
{ unfold now later }
end

lemma now_until_eventually {T : Type u}
  {P Q : tProp T}
  : ⊩ P => (◯ P) 𝓤 Q => ◇ (P ∩ Q)
:= begin
intros tr HP Huntil,
induction Huntil with k Hk,
induction Hk with H1 H2,
constructor, constructor; try { assumption },
cases k,
{ rw delayn_zero, assumption },
{ apply next_delay, apply H2, apply nat.le_refl, }
end

lemma until_next {T : Type u} {P Q : tProp T}
: ⊩ (P𝓤(P ∩ Q)) => (P ∩ ◯ P𝓤Q)
:= begin
intros tr QRP,
induction QRP with k Hk, induction Hk with H1 H2,
induction H1 with HP HQ,
unfold until, existsi k, split, assumption,
intros, constructor,
{ apply H2, assumption },
{ unfold next nextn, rw delayn_combine,
rw add_comm,
apply (if H : n' + 1 = k then _ else _),
rw H, assumption, apply H2,
apply nat.lt_succ_ne_lt,
apply nat.succ_lt_succ, assumption, assumption, }
end

lemma not_eventually_always_not {T : Type u} (P : tProp T)
  : tNot (◇ P) = □ (tNot P)
:= begin
apply included_eq,
{ intros tr contra n contra',
apply contra, constructor, assumption, },
{ intros tr H contra,
  induction contra with k Hk,
  apply (H k), assumption }
end

namespace trace
def map {A : Type u} {B : Type v} (f : A → B)
  : trace A → trace B
  := λ tr n, f (tr n)
end trace

section map_props
parameters {A : Type u} {B : Type v} (f : A → B)

lemma later_map (P : subset B)
  (n : ℕ) : later P n ∘ trace.map f = later (P ∘ f) n
:= begin
apply funext, intros x, reflexivity,
end

lemma now_map (P : subset B)
  : now P ∘ trace.map f = now (P ∘ f)
:= later_map P 0
end map_props

section precompose_props
parameters {A : Type u} {B : Type v}
lemma imp_precompose (P Q : tProp B) (f : A → trace B)
  : (P => Q) ∘ f = ((P ∘ f) => (Q ∘ f))
:= rfl

lemma and_precompose (P Q : tProp B) (f : A → trace B)
  : (bintersection P Q) ∘ f = (bintersection (P ∘ f) (Q ∘ f))
:= rfl

lemma or_precompose (P Q : tProp B) (f : A → trace B)
  : (bunion P Q) ∘ f = (bunion (P ∘ f) (Q ∘ f))
:= rfl

lemma next_map (P : tProp B) (f : A → B)
  : (◯ P) ∘ trace.map f = ◯ (P ∘ trace.map f)
:= rfl


end precompose_props

end temporal

namespace temporalExample
open temporal
def natTrace := temporal.trace nat

def one_at_one : natTrace :=
λ n, if (n = 1) then 1 else 0

lemma nextone : temporal.next (temporal.now (eq 1)) one_at_one:=
begin
simp [one_at_one] with ltl
end

end temporalExample
