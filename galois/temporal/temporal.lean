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

/-- Proposition P holds in the next state notation ◯ \ciO --/
@[ltl]
def next {T : Type u} (P : tProp T) : tProp T :=
  λ tr : trace T, P (λ t : ℕ, tr (t + 1))

notation `◯` := next


/-- Proposition P always holds notation □ \B --/
@[ltl]
def always {T: Type u} (P : tProp T) : tProp T :=
-- given a trace, P holds no matter how far forward we move the trace
 λ (tr : trace T), ∀ n : ℕ, P (λ t, tr (t + n))

notation `□` := always

/-- Proposition P eventually holds notation ◇ \dia -/
@[ltl]
def eventually {T: Type u} (P : tProp T) : tProp T :=
-- given a trace, we can find some n such that advancing
-- the trace by n allows p to hold on that trace
 λ (tr : trace T), ∃ n : ℕ, P (λ t, tr(t + n))

notation `◇` := eventually

/-- Until, notation \MCU --/
@[ltl]
def until {T : Type u} (P Q : tProp T) : tProp T :=
λ (tr : trace T), ∃ n, (Q (λ t, tr(t + n)) /\ (∀ n', n' < n -> (P (λ t: ℕ, tr(t + n')))))

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

/-- Fairness constraints on a trace require that
    something happens infinitely often --/
@[ltl]
def fair {T : Type u} (P : T -> Prop) := always (eventually (now P))

notation `⊩` P := forall tr, P tr

lemma eventually_mono {T : Type u} (A B : tProp T)
  (AB : ⊩ A => B)
  : ⊩ ◇ A => ◇ B
:= begin
intros tr HA, induction HA with k HA,
unfold eventually, existsi k,
apply AB, assumption
end


lemma weak_until_mono {T : Type u} (A B P : tProp T)
  (AB : ⊩ A => B)
  : ⊩ A 𝓦 P => B 𝓦 P
:= begin
intros tr AP evQ,
have H := AP evQ,
induction H with k Hk, induction Hk with H1 H2,
unfold until, existsi k, split, assumption,
intros, apply AB, apply H2, assumption
end

lemma eventually_and_r {T : Type u} (P Q : tProp T)
 : ⊩ ◇ (P //\\ Q) => ◇ Q
 :=
 begin
intros tr PQ,
induction PQ with k Hk,
induction Hk with Hkl Hkr,
constructor, assumption,
end


lemma nat.lt_succ_le : forall a b,
a < nat.succ b ->
a ≤ b :=
begin
intros,
cases a_1,
{
    refl,
},
{
    apply nat.le_trans,
    apply nat.le_add_right,
    exact 1,
    apply a_2
}
end

lemma nat.lt_succ_ne_lt : forall a b,
a < nat.succ b ->
a ≠ b ->
a < b :=
begin
intros,
cases  (nat.lt_trichotomy a b),
{  assumption },
{ cases a_3,
    { contradiction},
    {   exfalso,
        apply nat.le_lt_antisymm,
        apply a_1,
        apply nat.succ_lt_succ,
        assumption,
    }
}
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
lemma imp_e : forall {T : Type} (P Q : tProp T),
(⊩ (P => Q)) -> ((⊩ P) -> (⊩ Q)) :=
begin
intros,
 {simp [tImp, tInj2, implies] at a,
    apply a,
    apply a_1},
end

/-- always distributes over and --/
lemma always_and  : forall {T: Type} (P Q : tProp T) tr, always P tr ∧ always Q tr ↔ always (tAnd P Q) tr :=
begin
intros,
split; intros,
    cases a,
    simp only [always],
    intro n,
    simp only [tAnd, tInj2],
    split,
       apply (a n),
       apply (a_1 n),
simp only [always],
simp only [always] at a,
split; {intro n,
    simp only [tAnd] at a,
    have h_n: tAnd P Q (λ (t : ℕ), tr (t + n)),
        apply a, clear a,
    simp only [tAnd] at h_n,
    cases h_n, assumption}
end

def repeat_next {t : Type} (P : t -> Prop) : nat -> tProp t
| 0 := later P 0
| (nat.succ n') := next (repeat_next n')

/-- lift_at is the same as repeated applictions of next --/
lemma lift_at_n : forall {T : Type} (P : T -> Prop) (tr: trace T) (n : nat),
    repeat_next P n tr <-> later P n tr :=
begin
intros,
split; intros;
    revert tr;
    induction n; intros,
        simp [later],
        apply a,

        simp [later],
        simp [repeat_next, next] at a_1,
        revert a_1,
        apply ih_1,


        apply a,

        simp [repeat_next, next],
        revert a_1,
        apply ih_1
end

/-- equivalence between eventually and until tt --/
lemma eventually_until {T : Type} (P: tProp T) :
    forall tr, eventually P tr <-> until tt P tr :=
begin
intro tr,
split; intro,
    simp [until],
    simp [eventually] at a,
cases a with a_1 a_2,
{ existsi a_1,
    simp [tt],
  exact a_2,
},
{ simp [until] at a,
    simp [eventually],
    cases a,
    existsi a,
    cases a_1,
  assumption,
},
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

lemma always_and_next {T : Type} (P : tProp T) :
forall tr, □ P tr <-> (P //\\ ◯ (□ P)) tr :=
begin
intros; split; intros,
{
    simp [always, tAnd, tInj2, next],
    simp [always] at a,
    split,
    {
        have a0 := a 0,
        simp at a0,
        have treq : tr = λ t, tr t,
        { apply funext, intro, trivial },
        rewrite treq, assumption
    },
    {
        intro,
        have a1 := a (n + 1),
        apply congr_arg_app,
        apply a1,
        apply funext,
        intro,
        simp,
},
},
{
    simp with ltl,
    simp with ltl at a,
    cases a,
    intro,
    have a2n := a_1 (nat.pred n),
    apply dite (n = 0); intro,
    {
        subst n, simp,
        apply congr_arg_app,
        apply a,
        reflexivity,
    },
    {
        apply congr_arg_app,
        apply a2n,
        apply funext,
        intro,
        --dsimp,
        have nex := ne0_succ_exists _ a_2,
        cases nex,
        subst n,
        simp
    }
}
end

/-- This is probably true, but I can't prove it yet... --/
lemma alway_or_until {T : Type} (P Q : tProp T) :
forall tr, □ (tOr P Q) tr -> □ (◇ Q) tr -> (□ (P 𝓤 Q)) tr  :=
begin
simp with ltl,
intros,
have an := a n,
have a_1n := a_1 n,
clear a,
clear a_1,
induction n,
{
    simp,
    cases an,
    {
        cases a_1n,
        simp at a_2,
        existsi a_1,
        split,
        { assumption },
        {
            intro,
            dsimp at a,
               admit
        }
    }, admit
},
{admit}
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

    simp,
    have pIHa := pIH a,
    have pC := pIHa ih_1,
    have teq : (λ (t : ℕ), (λ (t : ℕ), tr (a + t)) (t + 1)) =
                  (λ (t : ℕ), tr (t + nat.succ a)),
    {   apply funext,
        intro x,
        dsimp,
        apply congr_arg,
        rewrite (nat.add_comm a (x + 1)),
        rewrite (nat.add_assoc),
        rewrite (nat.add_comm 1 a),

    },
        rewrite teq at pC,
    assumption,
end

lemma temporal_induction' {T : Type u} : forall (P : tProp T),
forall trace,
 P trace -> □ (P => (◯ P)) trace -> □ P trace :=
begin
intros,
have ti := @temporal_induction,
simp [implies] with tImp at ti,
apply ti;
assumption
end

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
simp [next,later, now],
reflexivity
end

end temporalExample
