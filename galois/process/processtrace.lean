import galois.process.process
import galois.temporal.temprelation

namespace process_set_trace
section
open process_set
open temporalrelation
open temporal

parameter {message_ty : Type}
parameter {state_ty : Type}

parameter set_type : Type
parameter proc_actions : Type

parameter [@process_set message_ty state_ty set_type]


/-- We can make a state for a process trace by combining a process
    set with an action allowed on any give process state -/
def process_trace_state : Type := 
    (set_type × @process_set_actions message_ty state_ty proc_actions)

-- given the right parameters, we can construct a relationtrace

parameter {trace : temporal.trace (process_trace_state)}
parameter {s0 : process_trace_state}
parameter t0_trace : (trace 0 = s0)
parameter trace_next : forall (t: nat), update_process_set _ _ _ _ ((trace t)^.fst) (prod.snd (trace t)) (prod.fst (trace (t+1)))

/-- a relational trace over processes
    and actions that can be taken
    over them
-/
def proc_trace : temporalrelation :=
⟨
    t0_trace,
    trace_next
⟩

-- some operations over process set traces

/-- Applies a prop to a process in a set -/
def at_proc_state (id : nat) (P : state_ty -> Prop) (st : set_type) := 
match process_set.get_process  message_ty state_ty st id with
                                | some proc := P (proc^.state)
                                | none := false
                                end



/-- Applies a proposition to the state of the process with the given id -/
def now_at_proc_state (id : nat) (P : state_ty -> Prop)  : @tProp process_trace_state :=
(now_state (λ st : set_type, at_proc_state id P st)) 



end  
end process_set_trace 

