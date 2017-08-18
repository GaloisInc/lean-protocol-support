-- author: Ben Sherman

import galois.network.network_implementation
       galois.temporal.fixpoint
       galois.temporal.classical
       galois.temporal.LTS

universes u

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

instance decidable_agent_does (a_ip : ip) P
  [decidable_pred P] : decidable_pred (agent_does a_ip P)
:= begin 
intros l, induction l with a_ip' l,
apply (if Hip : a_ip = a_ip' then _ else _),
{ apply (if H : P l then _ else _),
  subst a_ip',
  { apply decidable.is_true,
    constructor, assumption } ,
  { apply decidable.is_false,
    intros contra, cases contra, contradiction }
 },
{ apply decidable.is_false, intros contra,
  cases contra, contradiction }
end

inductive next_state_from_label_ind' (ag : agents.member) (s : system_state) (la : agent_label) (s' : @system_state agents) : Prop
| mk : ∀ (la' : dlabel ((ag.value).loop (s.local_state ag)))
         (Hla' : agent_label.to_dlabel (s.global_state (ag.key)) ((ag.value).loop (s.local_state ag)) la = some la')
         (new_state : (ag.value).state_type)
         (updatef : global_state_t → global_state_t)
         (Hagl : next_agent_state_from_dlabel (ag.key) (ag.value) (s.global_state (ag.key)) la' = some (new_state, updatef))
         (Hupd : s' = {local_state := lookup_update ag new_state (s.local_state), global_state := updatef (s.global_state)})
         , next_state_from_label_ind'

inductive next_state_from_label_ind (a_ip : ip) (s : system_state) (la : agent_label) (s' : system_state) : Prop
| mk : ∀ (ag : agents.member) (Hip : ag.key = a_ip)
         (H : next_state_from_label_ind' ag s la s'), next_state_from_label_ind


/-- WARNING: This lemma is now incorrect
    The definition of next_state_from_label_ind' needs
    to be modified
-/
lemma agent_update_invert_st' {s la s'}
  {ag : agents.member}
  : LTS s (next_state_label.agent_update ag.key la) s'
  → next_state_from_label_ind' ag s la s'
:= begin
intros H,
simp [LTS] at H,
simp [next_state_from_label] at H,
apply_in H option_bind_some,
induction H with la' p, induction p with Hag1 Hag2,
dsimp [label.to_sys_dlabel] at Hag1,
apply_in Hag1 option_bind_some,
induction Hag1 with ag' Hag1,
induction Hag1 with Hag Hag',
apply_in Hag mapd.check_member_same, 
subst ag',
dsimp at Hag',
apply_in Hag' option_bind_some,
induction Hag' with la'' Hla'',
induction Hla'' with H1 H2,
injection H2 with H2', clear H2, subst la',
dsimp [next_state_from_dlabel] at Hag2,
apply_in Hag2 option_bind_some,
induction Hag2 with res Hres,
induction Hres with HA HB,
induction res with new_state updatef,
dsimp [next_state_from_dlabel] at HB,
injection HB with HB', clear HB,
constructor; try { assumption }, symmetry, assumption
end

lemma agent_update_invert_st {s la s'}
  {a_ip : ip}
  : LTS s (next_state_label.agent_update a_ip la) s'
  → next_state_from_label_ind a_ip s la s'
:= begin
intros H, have H1 := H,
have H' := option_bind_some H,
clear H, induction H' with la' p, induction p with Hag1 Hag2,
dsimp [label.to_sys_dlabel] at Hag1,
apply_in Hag1 option_bind_some,
induction Hag1 with ag Hag,
induction Hag with H1 H2,
apply_in H1 mapd.check_member_same_key,
subst a_ip,
dsimp at H2,
constructor, reflexivity,
apply agent_update_invert_st', assumption,
end

lemma agent_does_invert {a_ip : ip} {P : agent_label → Prop}
  {l : next_state_label}
  (H : agent_does a_ip P l)
  : ∃ (la : agent_label), P la
   ∧ l = next_state_label.agent_update a_ip la
:= begin
induction H, constructor, split, assumption,
reflexivity
end

/-- Every agent always eventually gets to step -/
def fairness_spec : @TP agents
  := λ tr : TR, ∀ (a : agents.member),
   fair (now (inLabel (agent_does a.key (λ _, true)))) tr


lemma agent_update_invert {tr : TR} (a_ip : ip)
  (validtr : valid_trace LTS tr)
  {n : nat}
  {la : agent_label}
  (H : (tr n).snd = next_state_label.agent_update a_ip la)
  : next_state_from_label_ind a_ip (tr n).fst la (tr n.succ).fst
:= begin
have Hn := validtr.next_step n,
apply agent_update_invert_st,
rw <- H,
apply (validtr.next_step n),
end

lemma agent_update_invert' {tr : TR} (ag : agents.member)
  (validtr : valid_trace LTS tr)
  {n : nat}
  {la : agent_label}
  (H : (tr n).snd = next_state_label.agent_update ag.key la)
  : next_state_from_label_ind' ag (tr n).fst la (tr n.succ).fst
:= begin
have Hn := validtr.next_step n,
apply agent_update_invert_st',
rw <- H,
apply (validtr.next_step n),
end

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
  (HLTS : LTS s l s')
  (Hagent : ¬agent_does (a.key) (λ (_x : agent_label), true) l)
  : s.local_state a = s'.local_state a
:= begin
induction l with a_ip la,
apply_in HLTS agent_update_invert_st,
induction HLTS with ag Hip H, subst a_ip,
induction H,
subst s', dsimp, unfold lookup_update lookup_updatef,
apply (if Heq : ag = a then _ else _),
{ exfalso, subst ag,
 apply Hagent,
 constructor, trivial },
{ rw (dif_neg Heq) }
end

/-- A statement of the fact that a particular agent's state 
    doesn't change (weak-) until it takes a step within
    temporal logic.
    (Using the sort of Leibniz equality: Any predicate `P`
    that held on the old state will hold on the new state)
-/
lemma local_state_stays_constant_ltl (a : agents.member)
  (P : a.value.state_type → Prop)
  : ⊩ valid_trace LTS
    => □ (now (inLocalState a P)
    => (◯ (now (inLocalState a P))
        𝓦
       now (inLabel (agent_does a.key (λ _, true))))
    )
:= begin
intros tr validtr n Pst,
unfold inLocalState,
apply (invariant_holds_while LTS _ (delayn n tr)),
apply valid_trace_always, assumption, assumption,
apply_instance,
intros,
have H := local_state_stays_constant _ a_1 a_2,
rw ← H, assumption,
end

/-- If an agent always eventually polls, and if it is sent a message,
    then it eventually receives that message.
-/
def message_fairness_spec : @TP agents := λ tr,
  ∀ (a : agents.member) (mess : (socket × message_t)),
    (fair (now (inLabel (agent_does a.key polls))) 
     => □ (now (inState (λ s : system_state, mess ∈ (s.global_state a.key).messages))
           => ◇ (now (inLabel (agent_does a.key (receives_message mess.snd)))))) tr



end

inductive can_possibly_step (a_ip : ip) (a : agent) 
  (s : a.state_type) (l : next_state_label) (s' : a.state_type) : Prop
| mk : ∀ 
  (agents : map ip agent)
  (Hmap : mapd.find a_ip agents = some a)
  (ss ss' : @system_state agents)
  (loc : ss.local_state ⟨ _, _, Hmap ⟩ = s)
  (loc' : ss'.local_state ⟨ _, _, Hmap ⟩ = s')
  (HLTS : LTS ss l ss'),
  can_possibly_step

section
parameters {agents : map ip agent}
  (a : agents.member)
  (P : message_t → Prop)

lemma blocks_until_not_never_receives_always_polls
  : ⊩ valid_trace (@LTS agents)
    => (◇ (now (inLabel (agent_does a.key polls))) 
        𝓦 (now (inLabel (agent_does a.key (receives P)))))
    => □ (tNot (now (inLabel (agent_does a.key (receives P)))))
    => fair (now (inLabel (agent_does a.key polls)))
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
  : ⊩ valid_trace (@LTS agents)
    => fairness_spec
    => message_fairness_spec
    => (◇ (now (inLabel (agent_does a.key polls))) 
        𝓦 (now (inLabel (agent_does a.key (receives P)))))
    => now (inState (λ ss : system_state, ∃ mess : socket × message_t,
         P mess.snd ∧
         mess ∈ (ss.global_state a.key).messages))
    => ◇ (now (inLabel (agent_does a.key (receives P))))
:= begin
intros tr valid fair mfair nowstate H,
apply classical.not_always_not_implies_eventually,
intros contra,
have H' := blocks_until_not_never_receives_always_polls 
  _ _ _ valid nowstate contra,
induction H with mess Hmess,
induction Hmess with Hmess1 Hmess2,
specialize (mfair a mess H'),
rw ← (delayn_zero tr) at Hmess2,
specialize (mfair 0 Hmess2),
rw ← not_eventually_always_not at contra,
apply contra,
revert mfair, rw delayn_zero,
apply eventually_mono,
intros x H,
unfold now later inLabel at H,
unfold now later inLabel,
apply_in H agent_does_invert,
induction H with la Hla,
induction Hla with Hlal Hlar,
rw Hlar,
constructor,
induction Hlal,
constructor, rw ← a_1, assumption
end

end

end network