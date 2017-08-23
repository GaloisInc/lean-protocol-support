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
    rw (precondition_true_bind (eq.refl ag)) at H,
    dsimp [sys_dlabel_to_local] at H,
    dsimp [inSkipLabel] at H,
    dsimp [loc.inLabeld] at H,
    dsimp [indLabel] at H,
    apply H },
  { rw (precondition_false Hag) at H,
    dsimp [has_bind.bind, option_bind] at H,
    dsimp [inSkipLabel] at H, contradiction,
  },
},
{ induction H,
  dsimp [Refinement.SL_refine, refinesd, inSkipLabel],
  dsimp [sys_dlabel_to_local],
  rw (precondition_true_bind (eq.refl ag)),
  dsimp [sys_dlabel_to_local], dsimp [inSkipLabel],
  unfold loc.inLabeld, unfold indLabel, assumption
}
end



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

def fairness_specd
  := λ tr, ∀ (a : agents.member),
   fair (now (sys_agent_does a (λ _, true))) tr


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


lemma SkipLTS_state_stays_constant (ag : agent)
  (P : ag.state_type → Prop) : 
  ⊩  valid_trace (SkipLTS (loc.LTSd ag))
  => □ (now (inState P)
  => ((◯ (now (inState P)))
       𝓦 
       now (inSkipLabel (λ _, true)))
  )
:= begin
intros tr validtr n Pst,
apply (invariant_holds_while (SkipLTS (loc.LTSd ag)) _ (delayn n tr)),
apply valid_trace_always, assumption, assumption,
apply_instance,
intros,
induction l,
{ dsimp [SkipLTS] at a, subst s', assumption },
{ exfalso, apply a_1, constructor, }
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
  ∀ (a : agents.member) (sock : socket) (mess : message_t),
    (fair (   now (inLocalState a (polls_on_socket sock ∘ a.value.loop))
            ∩ now (inLabel (agent_does a.key (λ _, true))))
     => □ (now (inState (λ s : system_state, (sock, mess) ∈ (s.global_state a.key).messages))
           => ◇ (now (inLabel (agent_does a.key (receives_message mess)))))) tr

def message_fairness_specd := λ tr,
  ∀ (a : agents.member) (sock : socket) (mess : message_t),
    (fair (   now (inLocalState a (polls_on_socket sock ∘ a.value.loop))
            ∩ now (sys_agent_does a (λ _, true)))
     => □ (now (inState (λ s : system_state, (sock, mess) ∈ (s.global_state a.key).messages))
           => ◇ (now (sys_agent_does a (receives_message mess))))) tr


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
  (s : socket)
  : ⊩ valid_trace (@LTS agents)
    => (◇ (now (inLocalState a (polls_on_socket s ∘ a.value.loop))
           ∩ now (inLabel (agent_does a.key (λ _, true)))) 
        𝓦 (now (inLabel (agent_does a.key (receives P)))))
    => □ (tNot (now (inLabel (agent_does a.key (receives P)))))
    => fair (now (inLocalState a (polls_on_socket s ∘ a.value.loop))
             ∩ now (inLabel (agent_does a.key (λ _, true))))
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
  : ⊩ valid_trace (@LTS agents)
    => message_fairness_spec
    => (◇ (now (inLocalState a (polls_on_socket s ∘ a.value.loop))
          ∩ now (inLabel (agent_does a.key (λ _, true))))
        𝓦 (now (inLabel (agent_does a.key (receives P)))))
    => now (inState (λ ss : system_state, ∃ mess : message_t,
         P mess ∧
         (s, mess) ∈ (ss.global_state a.key).messages))
    => ◇ (now (inLabel (agent_does a.key (receives P))))
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