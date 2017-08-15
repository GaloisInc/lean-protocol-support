/-
For a given agent, we define a labeled transition system
where everything else occuring on the network may be completely arbitrary
-/
import .action

namespace network
namespace loc

inductive poll_receive_dlabel_abs (ports : list port) (sockets : list socket)
    : Type
| new_connection {} : ports.member → socket → poll_receive_dlabel_abs
| receive_message {} : sockets.member → message_t → poll_receive_dlabel_abs

@[reducible]
def dlabel' {a} := @dlabel a poll_receive_dlabel_abs

section
parameters (a_ip : ip) (ag : agent)

def next_receive_dlabel {ports : list port} {sockets : list socket}
  {bound : time}
  (cont : poll_result ports sockets bound → act ag.state_type)
  (elapsed_fin : fin bound) (rn : remote_name)
  : poll_receive_dlabel_abs ports sockets
  → act ag.state_type
| (poll_receive_dlabel_abs.new_connection p sock) :=
     cont (poll_result.new_connection elapsed_fin p sock)
| (poll_receive_dlabel_abs.receive_message sock mess) := 
     cont (poll_result.message elapsed_fin sock mess)

def next_poll_dlabel {ports : list port} {sockets : list socket}
  {bound : time} (cont : poll_result ports sockets bound → act ag.state_type)
  : @poll_dlabel poll_receive_dlabel_abs ports sockets bound 
  → act ag.state_type
| poll_dlabel.timeout := cont poll_result.timeout
| (poll_dlabel.receive elapsed_fin rn rlabel) := next_receive_dlabel
     cont elapsed_fin rn rlabel

def next_agent_state_from_dlabel
  : ∀ (a_next : act ag.state_type) (la : dlabel' a_next)
  , act ag.state_type
| (act.return new_state) (dlabel.update_own_state ._) := ag.loop new_state
| (act.connect rn cont) (dlabel.connect ._ ._) := cont rn
| (act.send_message sock mess cont) (dlabel.send_message ._ ._ ._) := cont
| (act.poll ports sockets bound cont) (dlabel.poll ._ ._ ._ ._ plabel)
    := next_poll_dlabel cont plabel

inductive sends_message_st (P : socket → message_t → Prop) : act ag.state_type → Prop
| mk : ∀ sock mess cont, P sock mess 
     → sends_message_st (act.send_message sock mess cont)

instance sends_message_st_decidable (P : socket → message_t → Prop) 
  [decP : ∀ x y, decidable (P x y)] : decidable_pred (sends_message_st P)
:= begin
intros x, induction x;
  try { solve1 {apply decidable.is_false, intros x, cases x} },
have H := decP a a_1, induction H,
{ apply decidable.is_false, intros contra, cases contra,
  apply a_3, assumption },
{ apply decidable.is_true, 
  constructor, assumption
}
end

def LTS s l s' := next_agent_state_from_dlabel s l = s'

end

end loc
end network