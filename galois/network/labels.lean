-- author: Ben Sherman

import galois.network.network_monad

universes u v

namespace network

def message_t := list byte

@[reducible]
def socket := remote_name

inductive poll_receive_label : Type
| new_connection : poll_receive_label
| drop_connection : poll_receive_label
| receive_message : message_t → poll_receive_label

instance poll_receive_label_decidable_eq 
  : decidable_eq poll_receive_label
  := by tactic.mk_dec_eq_instance

inductive poll_label : Type
| timeout : poll_label
| receive : time → remote_name → poll_receive_label → poll_label

instance poll_label_decidable_eq 
  : decidable_eq poll_label
  := by tactic.mk_dec_eq_instance

inductive agent_label : Type
  | poll : poll_label → list (remote_name × message_t) → agent_label

/-- Decidable equality is straightforward, but currently it's
    difficult for me to automate.
-/
instance agent_label_decidable_eq : decidable_eq agent_label
  := by tactic.mk_dec_eq_instance

inductive next_state_label : Type 1
  | agent_update : ip → agent_label → next_state_label

/-- Indicates that an agent takes a step satisfying a given property -/
inductive agent_does (a : ip) (P : agent_label → Prop) : next_state_label → Prop
| mk : ∀ (l : agent_label), P l → agent_does (next_state_label.agent_update a l)

/-- Indicates that an agent is polling -/
inductive polls : agent_label → Prop
| mk : ∀ (l : poll_label) ms, polls (agent_label.poll l ms)

instance polls_decidable : decidable_pred polls
:= begin
intros x, induction x;
try { solve1 { apply decidable.is_false; intros contra; cases contra } },
apply decidable.is_true, constructor,
end

inductive receives (P : poll_receive_label → Prop) : agent_label → Prop
| mk : ∀ (t : time) (rn : remote_name) (prl : poll_receive_label) ms,
       P prl → receives (agent_label.poll (poll_label.receive t rn prl) ms)

inductive receives_or_timeout (P : poll_receive_label → Prop) (l : agent_label) : Prop
| receives : receives P l → receives_or_timeout
| timeouts : ∀ ms, l = agent_label.poll poll_label.timeout ms -> receives_or_timeout

def receives_message (m : message_t) : agent_label → Prop :=
  receives (eq (poll_receive_label.receive_message m))

def poll_result_to_label {ports : list port} {sockets : list socket}
  {timeout : time} : poll_result ports sockets timeout → poll_label
| poll_result.timeout := poll_label.timeout
| (poll_result.new_connection elapsed prt sock) := 
    poll_label.receive elapsed.val sock poll_receive_label.new_connection
| (poll_result.drop_connection elapsed sock) := 
    poll_label.receive elapsed.val sock.value poll_receive_label.drop_connection
| (poll_result.message elapsed sock mess) :=  
   poll_label.receive elapsed.val sock.value
     (poll_receive_label.receive_message mess)

end network