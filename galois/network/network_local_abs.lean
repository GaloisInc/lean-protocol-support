/-
For a given agent, we define a labeled transition system
where everything else occuring on the network may be completely arbitrary
-/
import .action
       galois.option
       galois.network.network_implementation
       galois.temporal.LTS

namespace network
namespace loc

def next_agent_state_from_dlabel {A} {a_next : act A} (la : dlabel a_next)
  : A
  := la.cont_result.snd

def sends_message_st (P : socket → message_t → Prop) (l : agent_label) : Prop
  := l.messages.Exists (λ x, P x.fst x.snd)

def sends_message_std (P : socket → message_t → Prop) {ag : agent}
  (a_next : act ag.state_type) (la : dlabel a_next) : Prop
  := la.messages.Exists (λ x, P x.fst x.snd)

section
parameters {ag : agent}

def inLabeld (P : ∀ (a_next : act ag.state_type), dlabel a_next → Prop)
  (x : sigma (λ s : ag.state_type, dlabel (ag.loop s))) : Prop
:= begin
induction x, apply P; assumption
end

instance sends_message_st_decidable (P : socket → message_t → Prop) 
  [decP : ∀ x y, decidable (P x y)] : decidable_pred (sends_message_st P)
:= begin
intros x, unfold sends_message_st,
apply list.Exists_decidable,
end

end

def LTSd (ag : agent) s l s' := @next_agent_state_from_dlabel ag.state_type (ag.loop s) l = s'

end loc

open temporal

def sys_dlabel_to_local {agents : map ip agent}
 (ag : agents.member) (s : @system_state agents) : 
  sys_dlabel s → option (dlabel (ag.value.loop (s.local_state ag)))
| (sys_dlabel.mk ag' aupdate) := do
  plift.up H ← option.precondition (ag' = ag),
  some (eq.rec_on H aupdate)

universes u

lemma next_state_local 
  (agents : map ip agent)
  (ag : mapd.member agents)
  (incoming : incoming_items)
  (a_next : act ag.value.state_type)
  (label : dlabel a_next)
  (new_state : (ag.value).state_type)
  (updatef : global_state_t → global_state_t)
  (Hx1 : next_agent_state_from_dlabel (ag.key) (ag.value) incoming label = some (new_state, updatef))
: loc.next_agent_state_from_dlabel label = new_state
:= begin
induction label, dsimp [loc.next_agent_state_from_dlabel, dlabel.cont_result],
dsimp [next_agent_state_from_dlabel] at Hx1,
apply_in Hx1 option.bind_some,
induction Hx1 with updatef H,
induction H with H1 H2,
dsimp [next_agent_state_from_dlabel] at H2,
generalize Hx : cont r = x, rw Hx at H2,
clear Hx, induction x, dsimp,
dsimp [next_agent_state_from_dlabel] at H2,
injection H2 with H, clear H2, injection H with H1 H2
end

def refinesd
  {agents : map ip agent}
  (ag : agents.member)
 : Refinement (@LTSd agents) (SkipLTS (loc.LTSd ag.value))
:= { S_refine := λ s, s.local_state ag
   , L_refine := sys_dlabel_to_local ag
   , refines := begin
   intros s l s' H,
   unfold LTSd at H, induction l,
   simp only [next_state_from_dlabel] at H,
   simp only [sys_dlabel_to_local],
   rename ag_1 ag',
   apply_in H option.bind_some,
   induction H with Hx Hx', induction Hx' with Hx1 Hx2,
   induction Hx with new_state updatef,
   dsimp [next_state_from_dlabel] at Hx2,
   injection Hx2 with Hx2', clear Hx2,
   subst s', dsimp,
   apply (if Hag : ag' = ag then _ else _),
   { -- I go! 
     rw (option.precondition_true_bind Hag),
     dsimp [sys_dlabel_to_local], induction Hag,
     dsimp, unfold SkipLTS,
     unfold loc.LTSd,
     rw lookup_update_refl,
     generalize Hls : (ag'.value).loop (s.local_state ag') = ls,
     rw Hls at label, rename label label',
     apply next_state_local, assumption,
   },
   { --Someone else goes
   rw (option.precondition_false Hag),
   dsimp [has_bind.bind, option_bind],
   dsimp [SkipLTS],
   rw (lookup_update_different Hag),
   },
   end
   }
end network