import galois.process.processtrace

section simple_processes
open process
open process_set
open process_set_trace

/-- Our processes keep a list (queue) of nats and send lists of nats -/
@[reducible]
def proc_ty := process (list nat) (list nat)

/-- A process with a queue -/
def proc : proc_ty :=
⟨ 
    (λ message state, some (state ++ message)),
    list.nil,
    (λ state, match state with
                | h :: t := some ( t, [h])
                | [] := none
                end )
⟩

/-- All a process can do to its state without sending messages is add a new message -/
inductive proc_actions : Type
| add_message : nat -> proc_actions

/-- A relation defining what add_message from proc_actions does -/
def proc_action_relation : (list nat) -> proc_actions -> list nat -> Prop
| l (proc_actions.add_message n) l' := l' =l ++ [n] 

/-- We'll reason about a set of processes -/
@[reducible]
def proc_set : Type := list proc_ty

/-- our proc_set is a valid set of processes --/
instance proc_set_set : process_set proc_set := list_process_set.list_process_set (list nat) (list nat)

/-- The state of our trace -/
def proc_state : Type := @process_trace_state (list nat) (list nat) proc_set proc_actions _


-- we define an abstract trace
-- that starts with a set of two of our processs
parameter trace : temporal.trace (proc_state)
parameter a0 : @process_set_actions (list nat) (list nat) proc_actions 
parameter t0_trace : (trace 0 = ([proc, proc], a0))
parameter trace_next : forall (t: nat), update_process_set _ _ _ _ ((trace t)^.fst) (prod.snd (trace t)) (prod.fst (trace (t+1)))

include t0_trace
include trace_next

/-- Define a trace around our initial state and transitions -/
def proc_trace := process_set_trace.proc_trace _ _ trace_next

open temporal

-- we take proofs of  fairness for:
-- adding new messages to the first process

def state0_adds_message : nat -> proc_state  -> Prop 
| n' (_, process_set_actions.update_process 0 (proc_actions.add_message n) par ) :=
    par = proc_action_relation /\ n = n'
| _ _ := false

def state0_adds_message_ex (st : proc_state) : Prop :=
exists n, state0_adds_message n st 


parameter add_message_fair : fair state0_adds_message_ex trace

include add_message_fair
/-- The proc state is sending a specific mesage from the first argument to the second --/
def send_message_from_to : nat -> nat -> list nat -> proc_state ->  Prop
| fromid toid msg (_, (process_set_actions.send_message_from fromid' toid' m )) :=
    fromid = fromid' ∧ toid = toid' /\ msg = m
| _ _ _ _ := false

/-- The proc state is sending any mesage from the first argument to the second --/
def send_message_from_to_ex (fromid toid : nat) st :=
exists msg, send_message_from_to fromid toid msg st 

parameter send0_to1_fair : fair (send_message_from_to_ex 0 1) trace
include send0_to1_fair
-- sending messages from the second process to the first
parameter send1_to0_fair : fair (send_message_from_to_ex 1 0) trace
include send1_to0_fair

lemma adds_message_l : forall (m : nat) s, state0_adds_message m s ->
s^.snd = process_set_actions.update_process 0 (proc_actions.add_message m) proc_action_relation :=
begin
intros,
cases s,
cases snd,
{ unfold state0_adds_message at a, contradiction },
{ rename a add_message, cases a_1, 
    { cases a,
        { rewrite state0_adds_message.equations._eqn_2 at add_message, --why can't I simp this?
        cases add_message,
        subst a_2,
        subst a_3,
        },
        { 
        rewrite state0_adds_message.equations._eqn_3 at add_message, --??
            { contradiction },
            { trivial }
        }
    },
 }
end

/-- relation between a process (by id in a set) and the prefix of its state -/
def prefix_state (n : nat) (ln : list nat) (ps : proc_state) : Prop :=  
exists post, (@at_proc_state (list nat) _ _ _ n (eq (ln ++ post)) ps^.fst)

/-- if we know that a queue will send "something" eventually, we can find the first send -/
lemma send_ex_send_head :
forall fr to hd tl, 
((fair (send_message_from_to_ex fr to)) =>
(now_at_proc_state _ _ fr (eq (hd::tl))) =>  
(◇ (now (send_message_from_to fr to [hd]) //\\ (now (prefix_state fr tl ))))) trace :=
begin
admit
end



/-- the prefix of the state stays the same until that process sends a message -/
lemma prefix_state_until_send : 
forall pref to, 
((temporal.now (prefix_state 0 pref)) => (until (temporal.now (prefix_state 0 pref)) 
                (temporal.now (send_message_from_to_ex 0 to)))) trace :=
begin
intros,
simp [tInj2, implies] with tImp, intros --todo, I should be able to do this with lemmas
intro,
simp [until], 
simp [fair] at send0_to1_fair,
simp [always, eventually, temporal.now] at send0_to1_fair,
note s01 := send0_to1_fair 0,
cases s01,
simp at a_1,
existsi a,
admit
end



lemma add_message_send_message :
forall m,
tImp (temporal.now (state0_adds_message m)) (eventually (now (send_message_from_to 0 1 [m]))) trace :=
begin
intros, simp [now, tInj2, implies, later] with tImp,
intros message_add, rewrite t0_trace at message_add,
note a0snd := (adds_message_l _ _ message_add),
simp at a0snd,
rewrite a0snd at t0_trace,
simp [fair] at send0_to1_fair,
rewrite send_message_from_to_ex.equations._eqn_1 at send0_to1_fair,


end


end simple_processes