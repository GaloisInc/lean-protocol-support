-- author: Ben Sherman

import galois.network.network_implementation
       galois.network.network_local_abs
       galois.temporal.fixpoint
       galois.temporal.classical
       galois.temporal.LTS

universes u v

/-- reflexive-transitive closure of a relation -/
inductive RTclosure {A : Type u} (R : A → A → Prop) (x : A) : A → Prop
  | refl {} : RTclosure x
  | step {} : ∀ {y z : A}, R y z → RTclosure y → RTclosure z

inductive RTclosure' {A : Type u} (R : A → A → Prop) (x z : A) : Prop
  | refl {} : x = z → RTclosure'
  | step {} : ∀ {y : A}, R y z → RTclosure R x y → RTclosure'

namespace RTclosure

def stepL {A : Type u} {R : A → A → Prop} {x y : A} (r : R x y)
  : ∀ {z : A}, RTclosure R y z → RTclosure R x z
:= begin
intros z s, induction s, apply step, assumption, apply refl,
apply step; assumption,
end

def invert {A : Type u} {R : A → A → Prop} {x z : A}
  (r : RTclosure R x z) :
  RTclosure' R x z
:= begin
induction r, left, reflexivity,
right, assumption, assumption
end

end RTclosure

namespace network

open temporal

section
parameter {agents : map ip agent}

def indLabel {A} (P : agent_label → Prop)
  := λ a_next, P ∘ @dlabel_to_label A a_next


instance inLabeld_decidable {ag : agent} (P : agent_label → Prop)
  [decP : decidable_pred P]
  : decidable_pred (@loc.inLabeld ag (indLabel P))
:= begin
intros x, dsimp [loc.inLabeld, indLabel, function.comp],
induction x, dsimp, apply decP
end

inductive sys_agent_does (ag : agents.member)
  (P : agent_label → Prop)
  : sigma sys_dlabel → Prop
| mk : ∀ sys dlabel, P (dlabel_to_label dlabel) → sys_agent_does (sigma.mk sys (sys_dlabel.mk ag dlabel))


@[trace_map]
lemma label_refine_eqd {ag : agents.member} (P : agent_label → Prop)
 : inSkipLabel (@loc.inLabeld ag.value (indLabel P)) ∘
       (Refinement.SL_refine (refinesd ag))
 = sys_agent_does ag P
:= begin
apply funext, intros x, dsimp [function.comp],
apply propext, split; intros H,
{
  induction x, induction snd,
  dsimp [inSkipLabel] at H,
  dsimp [Refinement.SL_refine, refinesd, inSkipLabel] at H,
  dsimp [sys_dlabel_to_local] at H,
  apply (if Hag : ag_1 = ag then _ else _),
  { subst ag_1, constructor,
    rw (option.precondition_true_bind (eq.refl ag)) at H,
    dsimp [sys_dlabel_to_local] at H,
    dsimp [inSkipLabel] at H,
    dsimp [loc.inLabeld] at H,
    dsimp [indLabel] at H,
    apply H },
  { rw (option.precondition_false Hag) at H,
    dsimp [has_bind.bind, option.bind] at H,
    dsimp [inSkipLabel] at H, contradiction,
  },
},
{ induction H,
  dsimp [Refinement.SL_refine, refinesd, inSkipLabel],
  dsimp [sys_dlabel_to_local],
  rw (option.precondition_true_bind (eq.refl ag)),
  dsimp [sys_dlabel_to_local], dsimp [inSkipLabel],
  unfold loc.inLabeld, unfold indLabel, assumption
}
end


instance decidable_sys_agent_does a P
  [decidable_pred P] : decidable_pred (sys_agent_does a P)
:= begin
intros l, induction l with s l,
induction l with a' l,
apply (if Hip : a = a' then _ else _),
{ apply (if H : P (dlabel_to_label l) then _ else _),
  subst a',
  { apply decidable.is_true,
    constructor, assumption } ,
  { apply decidable.is_false,
    intros contra, cases contra, contradiction }
 },
{ apply decidable.is_false, intros contra,
  cases contra, contradiction }
end

inductive next_state_from_label_ind' (ag : agents.member) (s : system_state) (la : dlabel ((ag.value).loop (s.local_state ag))) (s' : @system_state agents) : Prop
| mk : ∀ (new_state : (ag.value).state_type)
         (updatef : global_state_t → global_state_t)
         (Hagl : next_agent_state_from_dlabel (ag.key) (ag.value) (s.global_state (ag.key)) la = some (new_state, updatef))
         (Hupd : s' = {local_state := lookup_update ag new_state (s.local_state), global_state := updatef (s.global_state)})
         , next_state_from_label_ind'


lemma agent_update_invert_st'
  {ag : agents.member}
  {s la s'}
  : LTSd s (sys_dlabel.mk ag la) s'
  → next_state_from_label_ind' ag s la s'
:= begin
intros H,
simp [LTSd] at H,
simp [next_state_from_dlabel] at H,
apply_in H option.bind_some,
induction H with res p, induction p with Hag1 Hag2,
induction res with new_state updatef,
dsimp [next_agent_state_from_dlabel] at Hag1,
dsimp [next_state_from_dlabel] at Hag2,
injection Hag2 with Hag2', clear Hag2,
constructor; try { assumption }, symmetry, assumption
end

/-- Every agent always eventually gets to step -/
def fairness_specd : @TP agents
  := λ tr, ∀ (a : agents.member),
   fair (now (sys_agent_does a (λ _, true))) tr

/-- Indicates that an agent is at the beginning of running
    an iteration of its loop (or doing something equivalent
    to that)
-/
def starts_loop {a : agents.member} (next : act a.value.state_type) : Prop :=
  ∃ (s : a.value.state_type), next = a.value.loop s

def inLocalState (a : agents.member) (P : a.value.state_type → Prop)
  {L : system_state → Type u}
  : sigma L → Prop
  := inState (λ s, P (s.local_state a))

/-- If a transition occurs that doesn't involve a particular agent,
    that agent's state doesn't change.
-/
lemma local_state_stays_constant {s l s'}
  (a : agents.member)
  (HLTS : LTSd s l s')
  (Hagent : ¬sys_agent_does a (λ (_x : agent_label), true) ⟨ _, l ⟩)
  : s.local_state a = s'.local_state a
:= begin
induction l with a' la,
apply_in HLTS agent_update_invert_st',
induction HLTS with new_state updatef H1 Hs',
subst s', dsimp,
unfold lookup_update lookup_updatef,
apply (if Heq : a' = a then _ else _),
{ exfalso, subst a',
 apply Hagent,
 constructor, trivial },
{ rw (dif_neg Heq) }
end

def agent_has_state {L : @system_state agents → Type u}
  (ag : agents.member)
  (P : ag.value.state_type → Prop)
  : tProp (sigma L) := now (@inLocalState ag P L)

lemma agent_has_state_refine_eq (ag : agents.member)
  (P : ag.value.state_type → Prop) :
  agent_has_state ag P =
     now (inState P ∘ Refinement.SL_refine (refinesd ag))
:= begin
apply funext, intros x, reflexivity
end

/-- A statement of the fact that a particular agent's state
    doesn't change (weak-) until it takes a step within
    temporal logic.
    (Using the sort of Leibniz equality: Any predicate `P`
    that held on the old state will hold on the new state)
-/
lemma local_state_stays_constant_ltl (a : agents.member)
  (P : a.value.state_type → Prop)
  : ⊩ valid_trace LTSd
    => □ (now (inLocalState a P)
    => (◯ (now (inLocalState a P))
        𝓦
       now (sys_agent_does a (λ _, true)))
    )
:= begin
intros tr validtr n Pst,
unfold inLocalState,
apply (invariant_holds_while LTSd _ (delayn n tr)),
apply valid_trace_always, assumption, assumption,
apply_instance,
intros,
have H := local_state_stays_constant _ a_1 a_2,
rw ← H, assumption,
end

/-- If an agent always eventually polls, and if it is sent a message,
    then it eventually receives that message.
-/
def message_fairness_specd : @TP agents := λ tr,
  ∀ (a : agents.member) (sock : socket) (mess : message_t),
    (fair (   now (inLocalState a (polls_on_socket sock ∘ a.value.loop))
            ∩ now (sys_agent_does a (λ _, true)))
     => □ (now (inState (λ s : system_state, (sock, mess) ∈ (s.global_state a.key).messages))
           => ◇ (now (sys_agent_does a (receives_message sock mess))))) tr

end

section
parameters {agents : map ip agent}
  (a : agents.member)
  (P : socket → message_t → Prop)

lemma blocks_until_not_never_receives_always_polls
  (s : socket)
  : ⊩ valid_trace (@LTSd agents)
    => (◇ (now (inLocalState a (polls_on_socket s ∘ a.value.loop))
           ∩ now (sys_agent_does a (λ _, true)))
        𝓦 (now (sys_agent_does a (receives P))))
    => □ (tNot (now (sys_agent_does a (receives P))))
    => fair (now (inLocalState a (polls_on_socket s ∘ a.value.loop))
             ∩ now (sys_agent_does a (λ _, true)))
:= begin
intros tr valid nows never,
apply weak_until_not_always; assumption,
end

/--
   As Joey and I discussed, the way this proof should go is as follows:
   Use classical logic to do a proof by contradiction. Assume that we
   never receive the message. Then,
   use message fairness in conjunction with with the fact that we
   have a message in the queue to derive that
   H : if the agent always eventually polls, it eventually receives the message.
   Next, use the fact that we do *not* eventually receive the message,
   together with the fact that we block until we receive the message,
   to derive that we always eventually poll.
   Combining this with the `H` specified above, we find that we
   eventually do receive the message, a contradiction.
-/
theorem blocking_agent_eventually_receives_message
  {s : socket}
  : ⊩ valid_trace (@LTSd agents)
    => message_fairness_specd
    => (◇ (now (inLocalState a (polls_on_socket s ∘ a.value.loop))
          ∩ now (sys_agent_does a (λ _, true))))
        𝓦 (now (sys_agent_does a (receives P)))
    => now (inState (λ ss : system_state, ∃ mess : message_t,
         P s mess ∧
         (s, mess) ∈ (ss.global_state a.key).messages))
    => ◇ (now (sys_agent_does a (receives P)))
:= begin
intros tr valid mfair nowstate H,
apply classical.not_always_not_implies_eventually,
intros contra,
have H' := blocks_until_not_never_receives_always_polls
  _ _ _ _ valid nowstate contra,
induction H with mess Hmess,
induction Hmess with Hmess1 Hmess2,
specialize (mfair a s mess H'),
rw ← (delayn_zero tr) at Hmess2,
specialize (mfair 0 Hmess2),
rw ← not_eventually_always_not at contra,
apply contra,
revert mfair, rw delayn_zero,
apply eventually_mono,
intros x H,
unfold now later inLabel at H,
unfold now later inLabel,
induction H with s l Psl,
constructor, unfold receives_message at Psl,
induction Psl with t rn mess' ms H,
induction H with H1 H2, subst mess', subst s,
constructor, assumption,
end

/-- Agent fairness in the global transition system implies
    "skip fairness" in the local system, where there is only
    a single agent
-/
lemma fairness_Skip_impl (agents : map ip agent) (ag : agents.member) :
 ⊩ fairness_specd => (fairness_SkipLTS ∘ trace.map (Refinement.SL_refine (refinesd ag)))
:= begin
intros tr agent_fair,
unfold fairness_SkipLTS,
dsimp, rw fair_map, rw now_map,
unfold fairness_specd at agent_fair,
specialize (agent_fair ag),
rw ← label_refine_eqd at agent_fair,
assumption,
end

end

end network