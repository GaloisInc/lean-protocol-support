import .temporal

universes u v

open temporal

section LTS
parameters {S : Type u} {L : Type v}

def LTS_trace  (r : S → L → S → Prop)
  (t : trace (S × L)) : Prop :=
  ∀ n : ℕ, r (t n).fst (t n).snd (t n.succ).fst

def inLabel {S} {L} {B} (f : L → B) (x : S × L) : B := f x.snd
def inState {S} {L} {B} (f : S → B) (x : S × L) : B := f x.fst

instance inLabel_decidable {S L} {P : L → Prop} [decP : decidable_pred P] :
  decidable_pred (@inLabel S L _ P) :=
begin
intros x, apply decP,
end

parameter (LTS : S → L → S → Prop)

structure valid_trace (t : trace (S × L)) : Prop :=
  (next_step : LTS_trace LTS t)

lemma prove_always {P : S × L → Prop} 
  {Q : S → Prop}
  (H : ∀ s l s', LTS s l s' → P (s, l) → Q s')
  : ⊩ valid_trace
    => □ (now P => ◯ (now (inState Q)))
:= begin
intros tr validtr n,
unfold next nextn now later inState,
intros HP,
rw delayn_combine,
rw add_comm, simp [delayn], apply H,
apply validtr.next_step,
dsimp [delayn] at HP, simp at HP,
cases (tr n), dsimp, assumption
end

lemma invariant_always (P : S → Prop)
  (H : ∀ s l s', P s → LTS s l s' → P s')
  : ⊩ valid_trace => now (inState P) => □ (now (inState P))
:= begin
intros tr validtr H0 n, induction n,
{ apply H0 },
{ apply H, apply ih_1, apply validtr.next_step }
end

end LTS