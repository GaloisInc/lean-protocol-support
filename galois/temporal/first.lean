/- Lemmas allowing for finding the first time that something eventual happens, when the thing is decidable -/
import .temporal
import galois.list
import galois.nat

namespace temporal
open list
/-- If P is decidable we can find all of the times it is true until N-/
def find_P_until_n {T : Type} (P: T -> Prop) [decidable_pred P] (tr: trace T) : nat -> (list (nat × T))
| 0  := []
| (nat.succ n') := if (P (tr n')) 
                        then (n', (tr n')) :: find_P_until_n n' 
                        else find_P_until_n n'





lemma find_P_trace {T : Type} (P : T -> Prop) [decidable_pred P] : forall  (tr : trace T) max n,
In (n, (tr n)) (find_P_until_n P tr max) ↔ (P (tr n) ∧ n < max) :=
begin
    intros, split; intros,
    {
        induction max,
        {
            simp [find_P_until_n] at a,
            cases a
        },
        {
            rename a b,
            simp [find_P_until_n] at b,
            cases (_inst_1 (tr a)),
            {
                simp [a_1] at b,
                note ih_b := ih_1 b,
                cases ih_b,
                split, assumption,
                apply nat.lt.step, assumption
            },
            {
                simp [a_1] at b,
                cases b,
                {
                    cases a_2,
                    split,
                    assumption,
                    apply nat.lt.base
                },
                {
                    note iha := ih_1 a_2,
                    cases iha,
                    split, assumption,
                    apply nat.lt.step, assumption
                }
            }

        }
    },
    {
        induction max,
        {
            cases a,
            rw nat.lt_zero_iff_false at a_2, contradiction
        },
        {
            cases a,
            simp [find_P_until_n],
            cases (_inst_1 (tr a)),
            {
                simp [a_3],
                by_cases (a = n); intros,
                {
                    subst a,
                    exfalso,
                    apply a_3,
                    assumption
                },
                {
                    apply ih_1,
                    split, assumption, apply nat.lt_succ_ne_lt,
                    assumption,
                    intro, apply a_4, symmetry, assumption
                }
            },
            {
                simp [a_3],
                by_cases a = n; intros,
                subst a, left, refl,
                right, apply ih_1,split,
                { assumption },
                {
                    apply nat.lt_succ_ne_lt,
                    assumption, intro, apply a_4, symmetry, assumption
                }

            }
        }
    }
end

instance dnil {T : Type} (l : list T) : decidable (l = []) :=
begin
cases l, right, refl,
left, intro, contradiction
end

lemma find_n_tr_n T P [decidable_pred P] : forall (tr : @trace T) a fst snd, 
In (fst, snd) (find_P_until_n P tr a) -> snd = (tr fst) :=
begin
intros,
induction a; simp [find_P_until_n] at a_1,    
{
    cases a_1,
},
{
    rename a_1 ax,
    cases (_inst_1 (tr a_1)); simp [a] at ax,
    {
        apply ih_1, assumption
    },
    {
        cases ax,
        { cases a_2,
            refl,
        },
        {
            apply ih_1, assumption
        }
    }
}
end

lemma find_n_tr_n' T P [decidable_pred P] : forall (tr : @trace T) a fst snd t,
reverse (find_P_until_n P tr a) = (fst, snd) :: t ->
snd = tr fst :=
begin
intros,
apply @find_n_tr_n _ _ _inst_1,
rw In_reverse_In, rw a_1,
simp
end

lemma last_found_lowest max {T : Type} (P : T -> Prop) [decidable_pred P] : forall  (tr : trace T)  n tl,
list.reverse (find_P_until_n P tr max) = ((n, tr n) :: tl) -> forall n', n' < n -> ¬ P (tr n') :=
begin
    induction max; intros,
    {
        simp [find_P_until_n] at a,
        contradiction,
    },
    {
        simp [find_P_until_n] at a_1,
        cases (_inst_1 (tr a)),
        {
            simp [a_1] at a_1_1,
            apply ih_1; assumption
        },
        {
            simp [a_1] at a_1_1,
            revert a_1_1,
            generalize2 (list.reverse (find_P_until_n P tr a)) l f, intros,
            cases l,
            {   
                simp at a_1_1,
                cases a_1_1,
                cases a_4,
                clear a_4,
                clear ih_1,
                intro, 
                assert conj : P (tr n') /\ n' < a,
                { split; assumption},
                rw - find_P_trace at conj,
                rw In_reverse_In at conj,
                rw f at conj,
                cases conj,
            },
            {
                intros,
                cases a_3,
                assert sf : snd = tr fst,
                    {
                        apply @find_n_tr_n' _ _ _inst_1,
                        assumption
                    },
                subst snd,
                apply ih_1,
                {
                    apply f
                },
                {
                    cases a_1_1, assumption,
                },
                
            }

        }
    }
end


lemma eventually_first_dec {T: Type} P [decidable_pred P] : forall (tr :  @trace T),
(◇ (now P)) tr ->
first (now P) tr :=
begin
intros,
simp with ltl at a,
cases a,
simp [first],
generalize2 (list.reverse (find_P_until_n P tr (nat.succ a_1))) h z,
cases h,
{ admit },
{ 
    cases a,
  existsi fst,
  assert sf : (snd = tr fst),
  {
    apply @find_n_tr_n' _ _ _inst_1, assumption
  },
  subst snd,
  note lfl := last_found_lowest _ _ _ _ _ z,
  split,
  assert iz : In (fst, tr fst) (find_P_until_n P tr (nat.succ a_1)),
  {
      rw In_reverse_In, rw z,
      simp
  },
  rw find_P_trace at iz, cases iz,
  simp with ltl,
  simp, assumption,
  intros,
  intro,
  apply lfl,
  apply a, simp with ltl at a_4, simp at a_4,
  assumption,
}
end

end temporal