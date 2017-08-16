import galois.map.fmap_func
       galois.network.labels

universes u v


namespace network

inductive act (A : Type u) : Type u
--| connect : remote_name → (socket → A) → act
-- return a poll result and the amount of time elapsed
| poll : Π (ports : list port) (sockets : list socket) (bound : time), 
     (poll_result ports sockets bound → (list (socket × message_t) × A)) → act

namespace act
def just_send_messages {A : Type u} (ms : list (socket × message_t)) 
  (x : A) := act.poll [] [] 0 (λ _, (ms, x))

def return {A : Type u} (x : A) : act A := just_send_messages [] x
end act

-- An agent is defined as a type for the internal state, an process that produces
-- the state, and a looping process that will execute when the process is complete.
--
-- Semantically, think of the behavior as `next >>= forever loop` where
-- `forever loop = loop >=> forever loop`.
structure agent : Type 1 :=
  (state_type : Type)
  (loop : state_type → act state_type)


section
parameters (ag : agent)

parameter {poll_receive_label_impl : list port → list socket → Type}

inductive poll_dlabel (ports : list port) (sockets : list socket) (bound : ℕ) : Type
| timeout {} : poll_dlabel
| receive {} : ∀ (elapsed_fin : fin bound) (rn : remote_name),
    poll_receive_label_impl ports sockets
    → poll_dlabel

inductive dlabel : act ag.state_type → Type
| poll : ∀ (ports : list port) (sockets : list socket) (bound : time) 
    cont (ms : list (socket × message_t)),
    poll_dlabel ports sockets bound
    → dlabel (act.poll ports sockets bound cont)

end

end network