/- A shallow embedding of temporal logic -/
universe variable u

namespace temporal

/--An ordered series of events over states --/
def trace (T : Type u) : Type u := nat -> T

/--Type of Propositions over traces --/
def tProp (T : Type u) := trace T → Prop

/- This defines a simp attribute named ltl
   later we can say "simp with ltl" in order
   to simplify any rule with this attribute -/
run_cmd mk_simp_attr `ltl
run_cmd mk_simp_attr `tImp

@[ltl]
def delayn {T : Type u} (n : ℕ) (tr : trace T) := (λ t : ℕ, tr (t + n))

lemma delayn_combine {T : Type u} (n k : ℕ) (tr : trace T)
  : delayn k (delayn n tr) = delayn (k + n) tr
:= begin
apply funext, intros n, simp with ltl,
end

lemma delayn_zero {T : Type u} (tr : trace T)
  : delayn 0 tr = tr := rfl

@[ltl]
def nextn {T : Type u} (n : ℕ) (P : tProp T) : tProp T
  := λ tr, P (delayn n tr)

lemma nextn_combine {T : Type u} (n k : ℕ) (P : tProp T)
  : nextn k (nextn n P) = nextn (n + k) P
:= begin
unfold nextn, apply funext, intros, rw delayn_combine
end

/-- Proposition P holds in the next state notation ◯ \ciO --/
@[ltl]
def next {T : Type u} : tProp T → tProp T := nextn 1

notation `◯` := next

instance nextn_decidable {T : Type u} (P : tProp T) [decidable_pred P]
  (n : ℕ) : decidable_pred (nextn n P)
:= begin unfold nextn, apply_instance, end

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
def tInj2 {T: Type u} (R : Prop -> Prop -> Prop) (P Q : tProp T) :=
λ (tr : trace T), R (P tr) (Q tr)

/-- Prop and on tProp, notation //\\ --/
@[ltl]
def tAnd {T: Type u} (P Q : tProp T) : tProp T  :=
tInj2 and P Q

infix `//\\` : 50 := tAnd

/-- Prop or on tProp, notation \\// --/
@[ltl]
def tOr {T: Type u} (P Q : tProp T) : tProp T :=
tInj2 or P Q

infix `\\//` : 50 := tOr

-- if running into axiom of choice problems, this one will need a more
-- positive definition TODO: what's the internal only command?
/-- This is here for posterity, use release --/
def release_neg {T : Type u} (P Q : tProp T) : tProp T  :=
tNot ((tNot P) 𝓤 (tNot Q))

/-- same as until, but we don't require Q to occur --/
@[ltl]
def release {T : Type u} (P Q : tProp T) : tProp T :=
(P 𝓤 Q) \\// □ P
-- \MCR
infix `𝓡` : 50 := release

/-- Lifting of prop implication --/
@[ltl, tImp]
def tImp {T : Type u} (P Q : tProp T) : tProp T :=
tInj2 implies P Q

infixr `=>` : 50 := tImp

@[ltl]
def weak_until {T : Type u} (P Q : tProp T) : tProp T :=
  ◇ Q => (P 𝓤 Q)

-- \MCW
infix `𝓦` : 50 := weak_until

/-- Lifting of iff --/
@[ltl, tImp]
def tIff {T : Type u} (P Q : tProp T) : tProp T :=
tInj2 iff P Q

infixr `<=>` : 50 := tIff

/-- True --/
@[ltl]
def tt {T : Type u} : tProp T :=
λ (tr : trace T), true

/-- False --/
@[ltl]
def ff {T : Type u} : tProp T :=
λ (tr : trace T), false

/-- P holds at the nth step of some trace --/
@[ltl]
def later {T : Type u} (P : T -> Prop) (n: nat) : tProp T :=
λ (tr : trace T), P (tr n)

/-- P holds at the first step of trace --/
@[ltl]
def now {T : Type u} (P: T -> Prop) := later P 0

instance now_decidable {T : Type u} (P : T → Prop) [decidable_pred P]
  : decidable_pred (now P)
:= begin
unfold now later, apply_instance,
end

/-- Fairness constraints on a trace require that
    something happens infinitely often --/
@[ltl]
def fair {T : Type u} (P : tProp T) := □ (◇ P)

notation `⊩` P := forall tr, P tr

lemma eventually_mono {T : Type u} (A B : tProp T)
  (AB : ⊩ A => B)
  : ⊩ ◇ A => ◇ B
:= begin
intros tr HA, induction HA with k HA,
unfold eventually, existsi k,
apply AB, assumption
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
  (AB : ⊩ A => B)
  : ⊩ A 𝓤 P => B 𝓤 P
:= begin
intros tr AP,  apply until_always_mono, 
intros n, apply AB, assumption
end

lemma weak_until_always_mono {T : Type u} (A B P : tProp T)
  : ⊩ □ (A => B) => A 𝓦 P => B 𝓦 P
:= begin
intros tr AB AP evQ,
apply until_always_mono, assumption, apply AP, assumption
end

lemma weak_until_mono {T : Type u} {A B P : tProp T}
  (AB : ⊩ A => B)
  : ⊩ A 𝓦 P => B 𝓦 P
:= begin
intros tr AP,  apply weak_until_always_mono, 
intros n, apply AB, assumption
end

lemma and_imp_l {T : Type u} (P Q : tProp T)
  : ⊩ (P //\\ Q) => P
:= begin
intros tr H, induction H with HP HQ, assumption,
end

lemma and_imp_r {T : Type u} (P Q : tProp T)
  : ⊩ (P //\\ Q) => Q
:= begin
intros tr H, induction H with HP HQ, assumption,
end

lemma eventually_and_r {T : Type u} (P Q : tProp T)
 : ⊩ ◇ (P //\\ Q) => ◇ Q
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
simp with ltl,
intros, unfold implies, intros, apply a, apply a_1
end

lemma always_tautology {T : Type u} (P : tProp T) :
(⊩ P) → (⊩ □ P) :=
begin
intros, intros n, apply a,
end

/-- pull out top level implication --/
lemma imp_e : forall {T : Type u} (P Q : tProp T),
(⊩ (P => Q)) -> ((⊩ P) -> (⊩ Q)) :=
begin
intros,
 {simp [tImp, tInj2, implies] at a,
    apply a,
    apply a_1},
end

lemma always_mono {T : Type u} (P Q : tProp T)
  (H : ⊩ P => Q)
  : ⊩ □ P => □ Q
:= begin
intros tr HP n, apply H, apply HP,
end

/-- always distributes over and --/
lemma always_and {T: Type u} (P Q : tProp T) :
 □ P //\\ □ Q = □ (P //\\ Q)
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
 (□ P) = (P //\\ ◯ (□ P)) :=
begin
apply funext, intros tr,
apply propext, split; intros H,
{
    constructor, 
    { rw ← (delayn_zero tr),
      apply H },
    {
        intro n,
        have a1 := H (n + 1),
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

/-- Induction over time --/
lemma temporal_induction {T} : forall (P : tProp T),
⊩ (P => always (P => (next P)) => always P) :=
begin
simp [always, next],
intros P tr,
simp [tImp, tInj2, implies],
intros p0 pIH n,
induction n; intros,

    simp,
    have treq : tr = λ t, tr t,
    {    apply funext,
        intro, reflexivity,
    },
    exact p0,

    --simp with ltl,
    have pIHa := pIH a,
    have pC := pIHa ih_1,
    have teq : delayn 1 (delayn a tr) =
                  delayn (nat.succ a) tr,
    {   apply funext,
        intro x,
        simp with ltl,
        apply congr_arg,
        rewrite (nat.add_comm a (x + 1)),
        rewrite (nat.add_assoc),
        rewrite (nat.add_comm 1 a),

    },
        rewrite <- teq, apply pC,
end

lemma temporal_induction' {T : Type u} : ∀ (P : tProp T),
  ∀ trace, P trace -> □ (P => (◯ P)) trace -> □ P trace 
 := temporal_induction

lemma eventually_strengthen_until {T : Type u}
  (P Q : tProp T)
  : ⊩ ◇ Q => (P 𝓦 Q) => (P 𝓤 Q)
:= begin
intros tr PWQ fairQ, apply fairQ, assumption,
end

lemma fair_strengthen_until {T : Type u}
  (P Q : tProp T) :
  ⊩ □ (P 𝓦 Q)
  => □ (◇ Q)
  => □ (P 𝓤 Q)
:= begin
intros tr PQ fairQ  n,
apply eventually_strengthen_until; apply PQ <|> apply fairQ,
end

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
