/-
For a given agent, we define a labeled transition system
where everything else occuring on the network may be completely arbitrary
-/
import .action

namespace network
namespace loc

def next_agent_state_from_dlabel {A} {a_next : act A} (la : dlabel a_next)
  : A
  := la.cont_result.snd 

inductive sends_message_st (P : socket → message_t → Prop) : agent_label → Prop
| mk : ∀ sock mess plabel ms, P sock mess
     → (sock, mess) ∈ ms
     → sends_message_st (agent_label.poll plabel ms)

inductive sends_message_std (P : socket → message_t → Prop) {ag : agent}
  (a_next : act ag.state_type) (la : dlabel a_next) : Prop
| mk : ∀ sock mess, (sock, mess) ∈ la.messages → sends_message_std

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
intros x, induction x,
have H := list.Exists_decidable (λ x : socket × message_t, P x.fst x.snd) a_1,
induction H,
{ apply decidable.is_false, intros contra, cases contra,
  apply a_2, 
  admit },
{ admit }
end

end

def LTSd (ag : agent) s l s' := @next_agent_state_from_dlabel ag.state_type (ag.loop s) l = s'

end loc
end network