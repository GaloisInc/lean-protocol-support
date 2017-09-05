/-
A labeled transition system built on top of temporal logic
-/

import .fixpoint

universes u v u' v'

open temporal

section LTS
parameters {S : Type u} {L : S → Type v}

-- TODO: Why can't this be a doc?
-- Ben S.: I think they're not allowed inside sections.
/-
A labeled trace takes a relation from start state through a label to an end state
and a trace made up of states paired with labels. In each pair the label represents
the step that will be taken from its paired state
-/
def LTS_trace  (r : ∀ s : S, L s → S → Prop)
  (t : trace (sigma L)) : Prop :=
  ∀ n : ℕ, r (t n).fst (t n).snd (t n.succ).fst

/--
Apply a function (usually a predicate) to the state of a state-label pair
-/
def inState {B} (f : S → B) (x : sigma L) : B := f x.fst


lemma inState_mono : subset.monotone (@inState Prop)
:= begin
intros P Q PQ x Hx, apply PQ, apply Hx
end

instance inState_decidable {P : S → Prop} [decP : decidable_pred P] :
  decidable_pred (@inState Prop P) :=
begin
intros x, apply decP,
end

parameter (LTS : ∀ s : S, L s → S → Prop)

/--
A trace is valid if it is a labeled transition system
-/
structure valid_trace (t : trace (sigma L)) : Prop :=
  (next_step : LTS_trace LTS t)

lemma prove_next {P : sigma L → Prop}
  {Q : S → Prop}
  (H : ∀ s l s', LTS s l s' → P ⟨ s, l ⟩ → Q s')
  : ⊩ valid_trace
    => now P => ◯ (now (inState Q))
:= begin
intros tr validtr,
unfold next nextn now later,
intros HP,
apply H,
apply validtr.next_step,
cases (tr 0), dsimp, assumption
end

lemma valid_trace_delay : ⊩ valid_trace => ◯ valid_trace
:= begin
intros tr validtr, constructor,
simp [delayn], dsimp [LTS_trace],
intros n, apply validtr.next_step
end

lemma valid_trace_always : ⊩ valid_trace => □ valid_trace
:= begin
intros tr validtr, apply temporal_induction, assumption,
intros n, apply valid_trace_delay,
end

lemma global_always (P : tProp (sigma L))
  (H : ⊩ valid_trace => P)
  : ⊩ valid_trace => □ P
:= begin
intros tr validtr n,
apply H, apply valid_trace_always, assumption
end

lemma prove_always {P : sigma L → Prop}
  {Q : S → Prop}
  (H : ∀ s l s', LTS s l s' → P ⟨ s, l ⟩ → Q s')
  : ⊩ valid_trace
    => □ (now P => ◯ (now (inState Q)))
:= begin
apply (global_always _ _),
apply prove_next, assumption
end


lemma invariant_always (P : S → Prop)
  (H : ∀ s l s', P s → LTS s l s' → P s')
  : ⊩ valid_trace => now (inState P) => □ (now (inState P))
:= begin
intros tr validtr H0 n, induction n,
{ apply H0 },
{ apply H, apply ih_1, apply validtr.next_step }
end

lemma sigma_eta (x : sigma L) : sigma.mk x.fst x.snd  = x
:= begin induction x, reflexivity end

lemma invariant_holds_while {P : S → Prop} {Q : sigma L → Prop}
  [decidable_pred Q]
  (H : ∀ s l s', LTS s l s' → ¬ Q ⟨s, l⟩ → P s → P s')
  : ⊩ valid_trace => now (inState P)
    => ◯ (now (inState P)) 𝓦 now Q
:= begin
intros tr validtr HP,
apply weak_until_induction,
assumption,
intros n HQn HPn,
unfold next nextn, rw delayn_combine,
rw add_comm,
simp [inState] with ltl at HQn HPn,
simp [inState] with ltl,
apply (H _ _), apply validtr.next_step,
rw sigma_eta, assumption, assumption,
end

lemma LTS_now_next (P' : S → Prop) (P Q : sigma L → Prop)
  (H : ∀ s l s', LTS s l s' → P ⟨ _, l⟩ → P' s' ∨ Q ⟨ _, l ⟩)
  : ⊩ valid_trace
    => now P
    => ( ◯ (now (inState P')) ∪ now Q)
:= begin
intros tr valid HP,
specialize (H _ _ _ (valid.next_step 0)),
rw sigma_eta at H,
specialize (H HP),
induction H, left, assumption,
right, assumption
end

end LTS

section LTS_refinement

def WithSkip {S : Type u} (L : S → Type v) (s : S) : Type v := option (L s)

parameters {S : Type u} {L : S → Type v}
parameter (LTS : ∀ s : S, L s → S → Prop)

def SkipLTS (s : S) (l : WithSkip L s) (s' : S) : Prop :=
  match l with
  | none := s = s'
  | some l' := LTS s l' s'
  end

def inSkipLabel (P : sigma L → Prop) : sigma (WithSkip L) → Prop
| (sigma.mk s l) := match l with
  | none := false
  | some l' := P (sigma.mk s l')
  end

instance inSkipLabel_decidable P [decP : decidable_pred P]
  : decidable_pred (inSkipLabel P)
:= begin
intros x, induction x with s l,
induction l; dsimp [inSkipLabel],
apply decidable.is_false, trivial,
apply decP,
end

def fairness_SkipLTS : tProp (sigma (WithSkip L)) :=
  fair (now (inSkipLabel (λ _, true)))

lemma SkipLTS_next_state
  (P Q : S → Prop)
  (W : sigma L → Prop)
  (HLTS : ∀ s l s', LTS s l s' → P s → W ⟨ _, l ⟩ → Q s')
   : ⊩ valid_trace SkipLTS
   => now (inState P)
   => now (inSkipLabel W)
   => ◯ (now (inState Q))
:= begin
simp with ltl,
intros tr valid nowP goes,
have H := valid.next_step 0,
destruct ((tr 0)), intros s l Hsl,
rw Hsl at goes,
induction l; dsimp [inSkipLabel] at goes,
{ contradiction },
{ apply HLTS, rw Hsl at H, dsimp [SkipLTS] at H,
  apply H, rw Hsl at nowP, assumption, assumption
}
end

lemma SkipLTS_now_next (P' : S → Prop) (P Q : sigma (WithSkip L) → Prop)
  (H : ∀ s l s', LTS s l s' → P ⟨ _, some l⟩ → P' s' ∨ Q ⟨ _, some l ⟩)
  : ⊩ valid_trace SkipLTS
    => now P => now (inSkipLabel (λ _, true))
    => ( ◯ (now (inState P')) ∪ now Q)
:= begin
intros tr valid HP Hgoes,
have valid0 := valid.next_step 0,
unfold now later at Hgoes,
unfold now later at HP,
destruct ((tr 0)); intros,
rw a at Hgoes,
cases snd; dsimp [inSkipLabel] at Hgoes,
contradiction,
rw a at valid0, rw a at HP,
dsimp [SkipLTS] at valid0,
specialize (H _ _ _ valid0 HP),
induction H with H H,
left, assumption, right, unfold now later,
rw a, assumption,
end

lemma SkipLTS_state_stays_constant
  (P : S → Prop) :
  ⊩  valid_trace SkipLTS
  => □ (now (inState P)
  => ((◯ (now (inState P)))
       𝓦
       now (inSkipLabel (λ _, true)))
  )
:= begin
intros tr validtr n Pst,
apply (invariant_holds_while SkipLTS _ (delayn n tr)),
apply valid_trace_always, assumption, assumption,
apply_instance,
intros,
induction l,
{ dsimp [SkipLTS] at a, subst s', assumption },
{ exfalso, apply a_1, constructor, }
end

parameters {S' : Type u'}{L' : S' → Type v'}
parameter (LTS' : ∀ s : S', L' s → S' → Prop)

structure Refinement :=
  (S_refine : S → S')
  (L_refine : ∀ {s}, L s → L' (S_refine s))
  (refines : ∀ s l s', LTS s l s' → LTS' (S_refine s) (L_refine l) (S_refine s'))
end LTS_refinement

namespace Refinement
section
parameters {S : Type u} {S' : Type u'} {L : S → Type v} {L' : S' → Type v'}
  {LTS : ∀ s : S, L s → S → Prop}
  {LTS' : ∀ s : S', L' s → S' → Prop}

def SL_refine' (r : Refinement LTS LTS')
  : sigma L → sigma L'
| (sigma.mk s l) := sigma.mk (r.S_refine s) (r.L_refine l)
def SL_refine (r : Refinement LTS LTS')
  (x : sigma L) : sigma L'
   := sigma.mk (r.S_refine x.fst) (r.L_refine x.snd)

def SL_refine_valid_trace (r : Refinement LTS LTS')
  (tr : trace (sigma L))
  (valid : valid_trace LTS tr)
  : valid_trace LTS' (tr.map r.SL_refine)
:= begin
constructor, unfold LTS_trace,
dsimp [trace.map],
intros n, dsimp [SL_refine], apply refines, apply valid.next_step,
end

def SL_refine_transform
  (r : Refinement LTS LTS')
  (P : tProp (sigma L'))
  (H : ⊩ valid_trace LTS' => P)
  : ⊩ valid_trace LTS => (P ∘ trace.map r.SL_refine)
:= begin
intros tr validtr, dsimp [function.comp],
apply H, apply SL_refine_valid_trace, assumption
end

end
end Refinement