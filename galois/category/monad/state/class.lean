/- This file defines a class monad_state for monads that have a state variable.
 -/
universe variables u v w

namespace monad

-- A unit type with a polymorphic universe parameter.
inductive punit : Type u
| punit : punit

-- A typeclass for monad states.
--
-- The definition allows one to get a state value, and apply a function that returns
-- a value and new state.
class monad_state (m : Type u → Type v) extends monad m :=
(state : Type u)
(with_state : Π{α : Type u}, (state → α × state) → m α)

-- Get the current state value
def get {m : Type u → Type v} [inst : monad_state m] : m inst.state :=
  @monad_state.with_state _ _ _ (λs, (s, s))

-- Set the current state value
def put {m : Type u → Type v} [inst : monad_state m] (v : inst.state) : m punit :=
  @monad_state.with_state _ inst _ (λt, (punit.punit, v))

end monad
