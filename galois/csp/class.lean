universe variable u

namespace csp

-- | This defines the monad process class for messages.
--
-- Defined as a class so that components can depend on this.
class has_send_receive (msg_t : Type) (m : Type → Type u) :=
(send : msg_t → m unit)
(receive : Π (guard : msg_t → bool), m (psigma (λ(m : msg_t), guard m = tt)))

@[reducible]
def send {msg_t : Type} {m :Type → Type u} [has_send_receive msg_t m]
: msg_t → m unit :=
  has_send_receive.send m

@[reducible]
def receive {msg_t : Type} {m :Type → Type u} [has_send_receive msg_t m] (guard : msg_t → bool)
: m (psigma (λ(m : msg_t), guard m = tt)) :=
  has_send_receive.receive m guard

-- Define state_t transformation for has_send_receive
instance state_t_has_send_receive
         (s : Type)
         (msg_t : Type)
         (m : Type → Type)
         [monad m]
         [has_send_receive msg_t m]
: has_send_receive msg_t (state_t s m) :=
{ send := λ(msg : msg_t), state_t.lift $ send msg
, receive := λ(guard : msg_t → bool), state_t.lift $ receive guard
}

end csp
