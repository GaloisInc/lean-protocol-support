import galois.map.fmap_func
import galois.temporal.first
import galois.temporal.LTS
import galois.network.labels

universes u v

namespace network
section
parameter (message_type : Type)
parameter [decidable_eq message_type]

inductive act (A : Type u) : Type u
| return {} : A → act
| connect : remote_name → (socket → act) → act
| send_message : socket -> message_type → act → act
-- return a poll result and the amount of time elapsed
| poll : Π (ports : list port) (sockets : list socket) (bound : time), 
     (@poll_result _ message_type ports sockets bound → act) → act

def act_bind {A B : Type u} (x : act A) (f : A → act B) : act B
:= begin
induction x,
{ apply f, assumption },
{ apply act.connect; assumption },
{ apply act.send_message; assumption },
{ apply act.poll; try {assumption} }
end

lemma act_bind_pure {α : Type u} (x : act α)
: act_bind x act.return = x :=
begin
  simp [act_bind], induction x; dsimp,
  { reflexivity },
  { dsimp at ih_1,  
    apply congr_arg, apply funext,
    intros s, apply ih_1 },
  { apply congr_arg, apply ih_1 },
  { dsimp at ih_1,
    apply congr_arg, apply funext,
    intros t, apply ih_1 }
end

instance act_is_monad : monad act :=
{ pure := @act.return
, bind := @act_bind
, id_map := begin intros, dsimp, apply act_bind_pure end
, pure_bind :=
begin
  intros, simp [act_bind],
end
, bind_assoc :=
begin
  intros, induction x,
  { reflexivity },
  { simp [act_bind], dsimp,
    apply congr_arg, apply funext,
    intros s, apply ih_1 },
  { simp [act_bind],
    apply congr_arg, apply ih_1 },
  { simp [act_bind], dsimp,
    apply congr_arg, apply funext,
    intros s, apply ih_1 }
end
}

instance act_is_network_monad : network_monad act :=
  { to_monad := act_is_monad
  , socket := remote_name
  , message_type := message_type
  , connect := λ x, act.connect x act.return
  , send := λ x y, act.send_message x y (act.return punit.star)
  , poll := λ x y z, act.poll x y z act.return
  }


lemma act_bind_poll {A : Type} {ports sockets bound}
  (f : poll_result ports sockets bound → act A)
  : poll ports sockets bound >>= f
  = act.poll ports sockets bound f
:= rfl

structure socket_info :=
  (client : ip)
  (server : ip)
  (port : port)
  -- whether the receiver has not yet been notified yet that the socket exists
  -- (it is TRUE if it hasn't notified the receiver yet)
  (new : bool)

def socket_info.socket (s : socket_info) : socket
  := (s.client, s.port)

structure incoming_items :=
  (messages : list (socket × message_type))
  (sockets : list socket_info)

-- An agent is defined as a type for the internal state, an process that produces
-- the state, and a looping process that will execute when the process is complete.
--
-- Semantically, think of the behavior as `next >>= forever loop` where
-- `forever loop = loop >=> forever loop`.
structure agent : Type 1 :=
  (state_type : Type)
  (loop : state_type → act state_type)

def lookup_updatef {A : Type u} [decidable_eq A] {B : A → Type v}
  (a : A) (f : B a → B a) (m : ∀ a, B a) (x : A) : B x
:= if H : a = x
  then eq.rec_on H (f (m a))
  else m x

def lookup_update {A : Type u} [decidable_eq A] {B : A → Type v}
  (a : A) (b : B a) : (∀ a, B a) → (∀ a, B a)
:= lookup_updatef a (λ _, b)

lemma lookup_update_refl {A : Type u} [decidable_eq A] {B : A → Type v}
  {a : A} {b : B a} {f : ∀ a, B a} :
  lookup_update a b f a = b
:= begin
unfold lookup_update lookup_updatef,
rw (dif_pos (eq.refl a)),
end

section
parameter {agents : map ip agent}

@[reducible]
def global_state_t := ip → incoming_items

structure system_state : Type 1 :=
  (local_state : ∀ a : agents.member, act a.value.state_type)
  (global_state : global_state_t)

def initial_incoming_items : incoming_items
  := { sockets := []
     , messages := [] }

def next_agent_poll_state_from_label (a_ip : ip) (a : agent)
  (ports : list port) (sockets : list socket) (bound : time)
  (incoming : incoming_items)
  (cont : @poll_result _ message_type ports sockets bound → act a.state_type)
  : poll_label → option (act a.state_type × (global_state_t → global_state_t))
| poll_label.timeout := some (cont (poll_result.timeout), id)
| (poll_label.receive elapsed rn receive_label) := 
  if H : elapsed < bound 
    then let elapsed_fin : fin bound := ⟨ elapsed, H ⟩ in
     match receive_label with
     | poll_receive_label.drop_connection := none
     | poll_receive_label.new_connection :=
       match list.member_st_decide 
         (λ s : socket_info, s.server = a_ip ∧ s.new) incoming.sockets with
      | (sum.inl m) := 
         let m' := list.member_st_to_member m in
         let s := list.get_member m' in
         match list.check_member s.port ports with
         | (some portidx) := some (cont (poll_result.new_connection elapsed_fin portidx s.socket)
            , lookup_updatef a_ip (λ inc, {inc with sockets := list.update_member ({s with new := false}) _ m'})
            )
         | none := none
         end
        
      | (sum.inr contra) := none
      end
     | (poll_receive_label.receive_message mess) :=
      -- OOPS, need to fix: to receive message, I should already have been
      -- informed of the new connection that the message has transferred over
        match list.member_st_decide (λ p : socket × message_type, p.snd = mess) incoming.messages with
        | (sum.inl idx) := let idx' := list.member_st_to_member idx in
          let p := list.get_member idx' in
              match list.check_member p.fst sockets with --any other checks necessary?
              | (some sockidx) := some
              (cont (poll_result.message elapsed_fin sockidx mess)
              , lookup_updatef a_ip (λ inc, {inc with messages := list.remove_member _ idx'}))
              | none := none
              end
        | (sum.inr contra) := none
        end
     end
   else none

def add_socket (s : socket_info) (a_ip : ip) : global_state_t → global_state_t :=
  lookup_updatef a_ip (λ i : incoming_items, {i with sockets := s :: i.sockets })
def add_message (rn : remote_name) (m : message_type) (a_ip : ip)
  : global_state_t → global_state_t :=
  lookup_updatef a_ip (λ i : incoming_items, {i with messages := (rn, m) :: i.messages })


def next_agent_state_from_label (a_ip : ip) (a : agent)
  (a_next : act a.state_type)
  (incoming : incoming_items)
  : agent_label → option (act a.state_type × (global_state_t → global_state_t))
| agent_label.update_own_state := match a_next with
  | (act.return new_state) := 
     some (a.loop new_state, id)
  | _ := none
  end
| (agent_label.connect rn) := match a_next with
   | (act.connect rn' cont) :=
    if rn = rn' 
    then let s_info := socket_info.mk a_ip rn.fst rn.snd true in
      some (cont rn, add_socket s_info rn.fst)
    else none
   | _ := none
   end
| (agent_label.send_message rn mess) := match a_next with
   | (act.send_message sock mess' cont) :=
     if rn = sock /\ mess = mess'
     then some (cont, add_message (a_ip, rn.snd) mess rn.fst)
     else none
    -- Perhaps we should add a check here to make sure
    -- that the agent sending the message is actually
    -- on the sending end of the socket id it is using
    | _ := none
    end
| (agent_label.poll plabel) := match a_next with
  | (act.poll ports sockets bound cont) := 
     next_agent_poll_state_from_label a_ip a
           ports sockets bound incoming cont plabel
  | _ := none
  end

def next_state_from_label (system : system_state) 
  : next_state_label → option system_state
| (next_state_label.agent_update a_ip aupdate) := do
  a ← agents.check_member a_ip,
  option_bind (next_agent_state_from_label a_ip a.value (system.local_state a)
      (system.global_state a_ip) aupdate)
   $ λ p, let (next', update) := p in 
    some 
        { local_state  := lookup_update a next' system.local_state
        , global_state := update system.global_state }

def poll_result_to_label {ports : list port} {sockets : list socket}
  {timeout : time} : poll_result ports sockets timeout → @poll_label message_type
| poll_result.timeout := poll_label.timeout
| (poll_result.new_connection elapsed prt sock) := 
    poll_label.receive elapsed.val sock poll_receive_label.new_connection
| (poll_result.drop_connection elapsed sock) := 
    poll_label.receive elapsed.val (list.get_member sock) poll_receive_label.drop_connection
| (poll_result.message elapsed sock mess) :=  
   poll_label.receive elapsed.val (list.get_member sock)
     (poll_receive_label.receive_message mess)

open temporal

end
end

section 
parameters {m : Type} [decidable_eq m] {agents : map ip (agent m)}
-- Our labeled transition system
def LTS  (s : @system_state m _ agents) (l : @next_state_label m) (s' : @system_state m _ agents) : Prop :=
  next_state_from_label m s l = some s'

def TR := temporal.trace (@system_state m _ agents × @next_state_label m)
def TP := temporal.tProp (@system_state m _ agents × @next_state_label m)

end
end network