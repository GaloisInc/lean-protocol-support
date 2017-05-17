/- This file defines a class monad_state for monads that have a state variable.
 -/
universe variables u v w

namespace monad

-- A typeclas for monad states.
-- The definition allows one to get a state value, and apply a function that returns
-- a value and new state.
class monad_state (s : Type w) (m : Type u → Type v) extends monad m :=
(state : Π (α : Type u), (s → α × s) → m α)

-- Get the current state value
def get (s : Type u) (m : Type u → Type v) [monad_state s m] : m s :=
  monad_state.state m s (λs, (s, s))

-- Set the current state value
def put (s : Type u) (m : Type → Type v) [monad_state s m] (v : s) : m unit :=
  monad_state.state m unit (λt, ((), v))

end monad
