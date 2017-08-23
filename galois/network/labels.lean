-- author: Ben Sherman

import galois.network.network_monad

universes u v

namespace network

def message_t := list byte

@[reducible]
def socket := remote_name

inductive poll_label : Type
| timeout : poll_label
| receive : time → remote_name → message_t → poll_label

instance poll_label_decidable_eq 
  : decidable_eq poll_label
  := by tactic.mk_dec_eq_instance

structure agent_label : Type :=
  (plabel : poll_label)
  (messages : list (remote_name × message_t))

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

inductive receives (P : message_t → Prop) : agent_label → Prop
| mk : ∀ (t : time) (rn : remote_name) (mess : message_t) ms,
       P mess → receives (agent_label.mk (poll_label.receive t rn mess) ms)

inductive timeouts : agent_label → Prop
| mk : ∀ ms, timeouts (agent_label.mk poll_label.timeout ms)

instance timeouts_decidable : decidable_pred timeouts
:= begin
intros x, induction x, induction plabel,
{ apply decidable.is_true, constructor, },
{ apply decidable.is_false, intros contra, cases contra, }
end

inductive receives_or_timeout (P : message_t → Prop) (l : agent_label) : Prop
| receives : receives P l → receives_or_timeout
| timeouts : timeouts l -> receives_or_timeout

def receives_message (m : message_t) : agent_label → Prop :=
  receives (eq m)

def poll_result_to_label {ports : list port} {sockets : list socket}
  {timeout : time} : poll_result ports sockets timeout → poll_label
| poll_result.timeout := poll_label.timeout
| (poll_result.message elapsed sock mess _) :=
   poll_label.receive elapsed.val sock.value mess

end network