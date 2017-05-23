import galois.temporal.temporal

section temporalrelation

open temporal

parameter {state_ty : Type}
parameter {label_ty : Type}


structure temporalrelation :=
{atrace : trace (state_ty × label_ty)}
--{t0 : (state_ty × label_ty)}
--(t0_trace : atrace 0 = t0)
{relation : state_ty -> label_ty -> state_ty -> Prop}
(trace_next : forall (t: nat), relation ((atrace t)^.fst) (prod.snd (atrace t)) (prod.fst (atrace (t+1))))



def relation_maintains_prop  (relation : state_ty -> label_ty -> state_ty -> Prop) (P : state_ty -> Prop) : Prop
:= 
forall st st' label, 
P st -> 
relation st label st' ->
P st'

def relation_maintains_prop_unless (relation : state_ty -> label_ty -> state_ty -> Prop) 
                                    (P : state_ty -> Prop)
                                    (Q : label_ty -> Prop) :=
forall st st' label,
P st -> 
relation st label st' ->
P st' \/ (Q label)

@[ltl]
def later_state (P : state_ty -> Prop) n := (later (λ (st : state_ty × label_ty), P st^.fst) n)
@[ltl]
def later_label (P : label_ty -> Prop) n := (later (λ (st : state_ty × label_ty), P st^.snd) n)

@[ltl]
def now_state (P : state_ty -> Prop) := (now (λ (st : state_ty × label_ty), P st^.fst))
@[ltl]
def now_label (P : label_ty -> Prop) := (now (λ (st : state_ty × label_ty), P st^.snd))

lemma always_relation_always (r : temporalrelation) (P : state_ty  -> Prop ) :
forall n, P (r^.atrace n)^.fst -> 
            relation_maintains_prop r^.relation P -> 
            (□ (later_state P n)) r^.atrace :=
begin
    intros,
    simp with ltl,
    intros,
    dsimp,
    induction n_1,
    {
        simp,
        assumption
    },
    {
        unfold relation_maintains_prop at a_1,
        note rel := r^.trace_next (a_2 + n),
        note wat := a_1 _ _ _ ih_1 rel,
        apply congr_arg_app _ _ _ wat,
        simp
    }
end


--probably true...
lemma until_relation_until (r : temporalrelation) (P : state_ty -> Prop) (Q : label_ty -> Prop) :
forall n, 
P (r^.atrace n) ^. fst ->
relation_maintains_prop_unless r^.relation P Q ->
(□ (◇ (later_label Q 0))) r^.atrace->
(later_state P n 𝓤 later_label Q 0) r^.atrace:=
begin
simp with ltl, -- don't want to do this, haven't found the right abstraction at the next level
dsimp,
intros,
induction n,
{
     note a_n := a_2 0,
     cases a_n,
     existsi a_3,
     split,
     {
         simp, simp at a_4,
         assumption
     },
     {
         intros,
         simp, 
         simp at a_2,
         unfold relation_maintains_prop_unless at a_1,
         admit
     }
},
{admit}
end

end temporalrelation