-- This defines a framework for defining communicating sequential
-- agents with asynchronous messages.
--
-- The key concepts are agents and messages.  The type for agents is
-- defined by the framework, but message type is left as an abstract
-- parameter.
--
-- Each agent consists of existentially quantified state type, a next
-- action that produces a value of the state type, and a loop action
-- which takes the state and generates a new state.  The loop action
-- called again whenever the next action terminates.
--
-- On top of these core definitions, we define a translation relation
-- over a system state, which is defined as a collection of agents,
-- and messages between agents.
--
-- To define the transition relation, we allow that one
-- of the following may happen at each step:
--
-- * A message may be received by an an agent when the agent is in a
--   receive state and the message satisfies the guard on the receive.
--
-- * A message may be sent by an agent whose next action is to
--   receive a message.
--
-- * A next action may complete, and loop restarted for each agent
--   whose next action is to complete.
--
-- Design notes:
--
-- To avoid potentially unneeded complexity, there is deliberately a
-- single type for messages, and no notion of names.  Agents can potentially
-- receive any message in the system.  This allows one to define an adversary
-- agent that intercepts messages or creates fake messages.
--
-- The framework includes no facilities for creating new agents, or
-- terminating an existing agent, or synchronous messages.  We may need
-- these later.
import galois.csp.class

universe variables u v

namespace csp

-- This represents an action for an agent an ability to send and receive messages.
--
-- Note: We may want to add additional actions such as spawning new agents,
inductive process (message_t : Type u) (α : Type v) : Type (max u v)

  -- Given a message, receive calls the guard to check if the message
  -- should be received, and if so, calls the next process with the message
  -- and a proof that the guard is satisfied.  --
  -- This function needed to be implemented this way rather than a
  -- single next process with the type `(message_t → option process)` to
  -- generate the correct recursor.
| receive    : Π(guard : message_t → bool) (next : Π(m : message_t) (ok : guard m = tt), process), process
| send       : message_t → process → process
| pure       : α → process

namespace process

section
parameter {message_t : Type u}

-- Define bind on processes.
def bind {α β : Type v} (m : process message_t α) (h : α → process message_t β) : process message_t β :=
  let C := λ(a : process message_t α), process message_t β in
  let on_receive (guard : message_t → bool)
                 (next : Π (msg : message_t), guard msg = tt → process message_t α)
                 (ind  : Π (msg : message_t), guard msg = tt → process message_t β)
       : process message_t β :=
     process.receive guard ind in
  let on_send := λ(m : message_t) (next : process message_t α) (ind : process message_t β), process.send m ind in
  @process.rec _ _ C @on_receive @on_send h m

-- receive and bind commute
protected
theorem receive_bind {α β : Type v}
                     (guard : message_t → bool)
                     (f : Π(msg : message_t), guard msg = tt → process message_t α)
                     (h : α → process message_t β)
: bind (receive guard f) h = receive guard (λmsg pr, bind (f msg pr) h) := rfl

-- send and bind commute
protected
theorem send_bind {α β : Type v} (msg : message_t) (f : process message_t α) (h : α → process message_t β)
: bind (send msg f) h = send msg (bind f h) := rfl

-- pure is a "left identity" to bind.
protected
theorem pure_bind {α β : Type v} (v : α) (h : α → process message_t β)
: bind (pure message_t v) h = h v := rfl

end -- section

instance is_monad (message_t : Type u) : monad (process message_t) :=
{ pure := @process.pure message_t
, bind := @process.bind message_t
, id_map :=
  begin
    intros α,
    apply process.rec,
    -- Receive
    { intros guard next ind,
      dsimp [monad.map._default] at ind,
      simp [monad.map._default, process.receive_bind, function.right_id],
      apply congr_arg,
      apply funext,
      intro msg,
      apply funext,
      apply ind,
    },
    -- Send
    { intros m next ind,
      simp [monad.map._default, process.send_bind],
      apply congr_arg,
      exact ind,
    },
    -- Pure
    { intros val,
      simp [monad.map._default, process.pure_bind],
      trivial
    }
  end
, pure_bind := @process.pure_bind message_t
, bind_assoc :=
  begin
    intros α β γ m f g,
    induction m with guard rcv ind msg next ind,
    -- Receive case
    { simp [process.receive_bind],
      apply congr_arg,
      apply funext,
      intro msg,
      apply funext,
      apply ind,
    },
    -- Send case
    { simp [process.send_bind],
      apply congr_arg,
      exact ind,
    },
    -- Pure case
    { simp [process.pure_bind],
    },
  end
}

end process

instance is_has_send_receive (message_t : Type) : has_send_receive message_t (process message_t) :=
{ send := λ(m : message_t), process.send m (pure ())
, receive := λ(guard : message_t → bool), process.receive guard (λm pr, pure ⟨m, pr⟩)
}

section

parameter (message_t: Type u)

-- An agent is defined as a type for the internal state, an process that produces
-- the state, and a looping process that will execute when the process is complete.
--
-- Semantically, think of the behavior as `next >>= forever loop` where
-- `forever loop = loop >=> forever loop`.
structure agent : Type (max u 1) :=
(state_type : Type)
(loop : state_type → process message_t state_type)
(next : process message_t state_type)

-- The system consists of agents and messages.
structure system_state : Type (max u 1) :=
(agents : list agent)
(messages : list message_t)

def partitions_core {α : Type u} : list α → list α → list (α × list α × list α)
| prev [] := []
| prev (a::r) := (a, prev, r) :: partitions_core (a::prev) r

-- Given a input list, this returns a list that contains a triple for each
-- input.  The first component of the triple at index i is the element
-- at index i in the input.  The other components are the elements before,
-- and after the given value.
def partitions {α : Type u} : list α → list (α × list α × list α) := partitions_core []

-- Enumerate the list of possible next states.
def next_states (system : system_state) : list system_state := do
  (⟨state_t, loop, action⟩, before, after) ← partitions system.agents,
  match action with
    -- If process is about to receive a message,
    -- consider all possible messages process could receive..
  | (process.receive guard next) :=
    -- Pattern match on messages
    -- Note: This uses list.bind to avoid a universe incompatibility
    list.bind (partitions system.messages) $ λm,
    let ⟨msg, before_messages, after_messages⟩ := m in
    -- If message satisfies guard
    if pr : guard msg = tt then
      -- Update agent to indicate it received message
      let agent' := agent.mk state_t loop (next msg pr) in
      pure { agents   := list.reverse_core before (agent' :: after)
             -- Delete message
           , messages := list.reverse_core before_messages after_messages
           }
    else
      -- Otherwise have message fail.
      []
    -- Send a new message
  | (process.send msg next) :=
    -- Update agent state and add message to list
    let agent' := agent.mk state_t loop next in
    pure { agents := list.reverse_core before (agent' :: after)
         , messages := msg :: system.messages
         }
    -- Start a new loop iteration.
  | (process.pure .(message_t) next_state)   :=
    let agent' := agent.mk state_t loop (loop next_state) in
    pure { system with agents := list.reverse_core before (agent' :: after) }
  end

end

end csp
