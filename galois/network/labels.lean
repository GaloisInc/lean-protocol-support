-- author: Ben Sherman

import galois.network.network_monad
import galois.tactic

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
  | update_own_state : agent_label
  | connect : remote_name → agent_label
  | send_message : remote_name → message_t → agent_label
  | poll : poll_label → agent_label

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
| mk : ∀ (l : poll_label), polls (agent_label.poll l)

instance polls_decidable : decidable_pred polls
:= begin
intros x, induction x;
try { solve1 { apply decidable.is_false; intros contra; cases contra } },
apply decidable.is_true, constructor,
end

inductive receives (P : poll_receive_label → Prop) : agent_label → Prop
| mk : ∀ (t : time) (rn : remote_name) (prl : poll_receive_label),
       P prl → receives (agent_label.poll (poll_label.receive t rn prl))

inductive receives_or_timeout (P : poll_receive_label → Prop) (l : agent_label) : Prop
| receives : receives P l → receives_or_timeout
| timeouts : l = agent_label.poll poll_label.timeout -> receives_or_timeout

def receives_message (m : message_t) : agent_label → Prop :=
  receives (eq (poll_receive_label.receive_message m))

end network