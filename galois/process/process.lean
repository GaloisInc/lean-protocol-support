namespace process

structure process (message_ty : Type) (state_ty : Type) : Type :=
-- what the process will do when it recieves a message
(recieve_message : message_ty -> state_ty -> option state_ty)

-- the state of the process
(state : state_ty)

-- a function to create a message from a state
(make_message : state_ty -> option (state_ty × message_ty))

end process

namespace process_set
open process


-- should we be able to add or remove processes?
class process_set {message_ty state_ty : Type} (set_ty : Type) :=
(update_process_id : set_ty -> nat -> process message_ty state_ty -> set_ty)
(get_process : set_ty -> nat -> option (process message_ty state_ty))

(update_process_get_process : forall (set: set_ty) (id : nat) np,
                                (exists n, get_process set id = some n) ->
                                get_process (update_process_id set id np) id = some np)

(update_changes_only : forall set set' id1 id2 proc,
                        set' = update_process_id set id1 proc ->
                        id1 ≠ id2 ->
                        get_process set' id2 = get_process set id2) 

def at_process {message_ty state_ty : Type} (set_ty : Type) [c : @process_set message_ty state_ty set_ty] 
    (st : set_ty) (id : nat) (P : (process _ _) -> Prop) : Prop :=
    match process_set.get_process message_ty state_ty st id with
    | some proc := P proc
    | none := false
    end

/-- In a process set, we can either send a message or update a state --/
inductive process_set_actions {message_ty state_ty state_actions: Type} : Type
| send_message_from : nat -> nat -> message_ty -> process_set_actions
| update_process : nat -> state_actions -> (state_ty -> state_actions -> state_ty -> Prop) -> process_set_actions

/-- A process is an updated version of another if... -/
inductive update_process_set (set_ty message_ty state_ty state_actions : Type) [c : @process_set message_ty state_ty set_ty] 
    (startps : set_ty) (action : @process_set_actions message_ty state_ty state_actions) : set_ty -> Prop
--we can send a mesage from one process to another when...
| send_message : forall fromid toid message fromprocess toprocess fromst' tost' toprocess' fromprocess' endps,
                    -- the processes are distinct (we'll need a new rule otherwise)
                    fromid ≠ toid ->
                    -- we have the send action
                    action = process_set_actions.send_message_from fromid toid message ->
                    -- we get the appropriate processes out of the set (fromid and toid are well defined process identifiers)
                    some fromprocess = process_set.get_process message_ty state_ty startps fromid ->
                    some toprocess = process_set.get_process message_ty state_ty startps toid ->
                    -- we create a new message from the from process
                    some (fromst', message) = fromprocess^.make_message fromprocess^.state ->
                    -- we update the state of the from process
                    fromprocess' = {fromprocess with state := fromst'} ->
                    -- we pass the message to the to process, updating its state
                    some tost' = toprocess^.recieve_message message toprocess^.state ->
                    toprocess'  = {toprocess with state := tost'} ->
                    -- we create the new set by updating the two processes
                    endps = process_set.update_process_id (process_set.update_process_id startps  toid toprocess') fromid fromprocess' ->
                    update_process_set endps

| update_process : forall pid update_relation state_action process state' process' endps,
                    -- we have the appropriate action label
                    action = process_set_actions.update_process pid state_action update_relation ->
                    -- we get the process that matches the id
                    some process = process_set.get_process message_ty state_ty startps pid ->
                    -- the new state is the update of the old one
                    update_relation process^.state state_action state' ->
                    -- we update the process by the function/action
                    process' = { process with state := state'} ->
                    -- we put the new process in the set, removing the old
                    endps = (process_set.update_process_id startps pid process') ->
                    update_process_set endps

end process_set

namespace list_process_set

open process
open process_set

lemma list_update_only : forall (a : Type) (set : list a) set' id1 id2 proc,
                        set' = list.update_nth set id1 proc ->
                        id1 ≠ id2 ->
                        list.nth set' id2 = list.nth set id2 :=
begin
intros α set,
induction set; intros,
    { subst set', reflexivity },
    { subst set', cases id1,
        {
            simp [list.update_nth],
            cases id2,
            { contradiction },
            { reflexivity }
        },
        { cases id2,
            { reflexivity },
            { simp [list.update_nth],
                apply ih_1,
                { reflexivity },
                { rename a_3 hne,
                    assert na : (a_2 ≠ a_3),
                    {
                        intro,
                        apply hne,
                        apply congr_arg,
                        assumption
                    },
                  assumption  
                }
            }
        }
    }
end

lemma update_nth : forall (a : Type) (l : list a) id n,
(exists i, list.nth l id = some i) ->
list.nth (list.update_nth l id n) id = some n :=
begin
intros a l,
induction l; intros,
    { cases (a_1),
      simp [list.nth] at a_3,
      contradiction },
    { 
        cases id,
            { cases a_3, simp [list.nth] at a_5,
              injection a_5,
              subst a_1,
              reflexivity
            },
            {
                cases a_3,
                simp [list.nth] at a_5,
                simp [list.update_nth],
                apply ih_1,
                existsi a_4,
                assumption
            }        
    }
end

/-- We can use a list as a process set -/
instance list_process_set (message_ty state_ty : Type) : process_set (list (process message_ty state_ty)) :=
⟨ list.update_nth,
  list.nth,
  update_nth _,
  list_update_only _⟩

end list_process_set