-- author: Ben Sherman

import galois.map.fmap_func
import galois.temporal.first
import galois.temporal.LTS
import galois.network.labels

universes u v

namespace network

inductive act (A : Type u) : Type u
| return : A → act
| connect : remote_name → (socket → act) → act
| send_message : socket -> message_t → act → act
-- return a poll result and the amount of time elapsed
| poll : Π (ports : list port) (sockets : list socket) (bound : time), 
     (poll_result ports sockets bound → act) → act

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
  { to_monad := network.act_is_monad
  , socket := remote_name
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
  (messages : list (socket × message_t))
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

def next_agent_receive_from_label (a_ip : ip) (a : agent)
  (ports : list port) (sockets : list socket) (bound : time)
  (incoming : incoming_items)
  (cont : poll_result ports sockets bound → act a.state_type)
  (elapsed_fin : fin bound) (rn : remote_name)
  : poll_receive_label → option (act a.state_type × (global_state_t → global_state_t))
| poll_receive_label.drop_connection := none
| poll_receive_label.new_connection :=
  match list.member_st_decide 
    (λ s : socket_info, s.server = a_ip ∧ s.new) incoming.sockets with
  | (sum.inl m) := 
    let m' := m.to_member in
    let s := m'.value in
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
  match list.member_st_decide (λ p : socket × message_t, p.snd = mess) incoming.messages with
  | (sum.inl idx) := let idx' := idx.to_member in
    let p := idx'.value in
        match list.check_member p.fst sockets with --any other checks necessary?
        | (some sockidx) := some
        (cont (poll_result.message elapsed_fin sockidx mess)
        , lookup_updatef a_ip (λ inc, {inc with messages := list.remove_member _ idx'}))
        | none := none
        end
  | (sum.inr contra) := none
  end

def next_agent_poll_state_from_label (a_ip : ip) (a : agent)
  (ports : list port) (sockets : list socket) (bound : time)
  (incoming : incoming_items)
  (cont : poll_result ports sockets bound → act a.state_type)
  : poll_label → option (act a.state_type × (global_state_t → global_state_t))
| poll_label.timeout := some (cont (poll_result.timeout), id)
| (poll_label.receive elapsed rn receive_label) := 
  if H : elapsed < bound 
    then let elapsed_fin : fin bound := ⟨ elapsed, H ⟩ in
      next_agent_receive_from_label a_ip a ports
        sockets bound incoming cont elapsed_fin rn receive_label
   else none

def add_socket (s : socket_info) (a_ip : ip) : global_state_t → global_state_t :=
  lookup_updatef a_ip (λ i : incoming_items, {i with sockets := s :: i.sockets })
def add_message (rn : remote_name) (m : message_t) (a_ip : ip)
  : global_state_t → global_state_t :=
  lookup_updatef a_ip (λ i : incoming_items, {i with messages := (rn, m) :: i.messages })

section
parameters (a_ip : ip) (a : agent) (incoming : incoming_items)

def next_agent_state_from_label (a_next : act a.state_type)
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

inductive poll_receive_dlabel (ports : list port) (sockets : list socket) (bound : ℕ) 
   (cont : poll_result ports sockets bound → act a.state_type) : Type
| new_connection : ∀ (sock : list.member_st (λ s : socket_info, s.server = a_ip ∧ s.new) incoming.sockets)
    (p : ports.member),
    sock.to_member.value.port = p.value →
    poll_receive_dlabel
| receive_message : ∀ (mess : incoming.messages.member)
    (sock : sockets.member),
    mess.value.fst = sock.value → 
    poll_receive_dlabel

inductive poll_dlabel (ports : list port) (sockets : list socket) (bound : ℕ) 
   (cont : poll_result ports sockets bound → act a.state_type) : Type
| timeout : poll_dlabel
| receive : ∀ (elapsed_fin : fin bound) (rn : remote_name),
    poll_receive_dlabel ports sockets bound cont
    → poll_dlabel

inductive dlabel : act a.state_type → Type
| update_own_state : ∀ new_state : a.state_type, dlabel (act.return new_state)
| connect : ∀ (rn : remote_name) cont, dlabel (act.connect rn cont)
| send_message : ∀ sock mess cont (rn : remote_name), rn = sock
    → dlabel (act.send_message sock mess cont)
| poll : ∀ (ports : list port) (sockets : list socket) (bound : time) cont,
    poll_dlabel ports sockets bound cont
    → dlabel (act.poll ports sockets bound cont)
    

def next_agent_state_from_dlabel 
 (a_next : act a.state_type) (la : dlabel a_next)
  : act a.state_type × (global_state_t → global_state_t)
:= begin
cases la,
{ -- update_own_state
exact (a.loop new_state, id)
},
{ -- connect
exact (
  let s_info := socket_info.mk a_ip rn.fst rn.snd true in
      (cont rn, add_socket s_info rn.fst))
},
{ -- send message
exact (cont, add_message (a_ip, rn.snd) mess rn.fst)
},
{ -- poll
induction a_1,
  { -- timeout 
    exact (cont (poll_result.timeout), id)
  },
  { -- receive
    induction a_1,
    { -- new connection
      let s := sock.to_member,
      exact (cont (poll_result.new_connection elapsed_fin p s.value.socket)
      , lookup_updatef a_ip (λ inc, {inc with sockets := list.update_member ({s.value with new := false}) _ s}))
    },
    { -- receive message
      exact (cont (poll_result.message elapsed_fin sock mess.value.snd)
        , lookup_updatef a_ip (λ inc, {inc with messages := list.remove_member _ mess}))
    }
  }
}
end

/-- Any step that we can take with a regular label, we can take 
    with a dependent label. Therefore, it is sound to reason based
    on the dependent-label traces.
-/
lemma label_dlabel_equiv (a_next : act a.state_type)
  : ∀ ans l, next_agent_state_from_label a_next l = some ans
  → ∃ l' : dlabel a_next, next_agent_state_from_dlabel a_next l' = ans
:= begin
intros ans l H,
induction l; simp [next_agent_state_from_label] at H,
{ cases a_next;
    dsimp [next_agent_state_from_label] at H;
    try { contradiction },
  injection H with H', clear H, rw ← H',
  fapply exists.intro, constructor, reflexivity,
},
{ cases a_next;
    dsimp [next_agent_state_from_label] at H;
    try { contradiction },
  apply (if Hs : a_1 = a_2 then _ else _),
  { rw (if_pos Hs) at H, subst Hs,
    injection H with H',
    clear H, rw ← H',
    fapply exists.intro, constructor,
    reflexivity,
  },
  { rw (if_neg Hs) at H, contradiction
  },
},
{ cases a_next; 
    dsimp [next_agent_state_from_label] at H;
    try { contradiction },
  apply (if Heq : (a_1 = a_3 ∧ a_2 = a_4) then _ else _),
  { rw (if_pos Heq) at H,
    injection H with H',
    clear H, rw ← H',
    fapply exists.intro, constructor,
    reflexivity, induction Heq with H1 H2,
    subst H1, subst H2,
    reflexivity,
  },
  { rw (if_neg Heq) at H, contradiction
  }, },
{ cases a_next; 
    dsimp [next_agent_state_from_label] at H;
    try { contradiction },
  cases a_1;
    dsimp [next_agent_poll_state_from_label] at H,
  { fapply exists.intro, constructor,
    apply poll_dlabel.timeout,
    dsimp, injection H with H',
  },
  { apply (if He : a_1 < bound then _ else _),
    { rw (dif_pos He) at H,
      induction a_4; dsimp [next_agent_receive_from_label] at H;
         try {contradiction},
      { -- new connection 
        cases (list.member_st_decide (λ (s : socket_info), s.server = a_ip ∧ ↑(s.new)) 
            (incoming.sockets));
           dsimp [next_agent_receive_from_label] at H;
           try { contradiction },
        destruct (list.check_member ((a_4.to_member).value.port) ports), intros X,
           rw X at H,
           dsimp [next_agent_receive_from_label] at H,
           contradiction,
        intros p Hp, rw Hp at H,
           dsimp [next_agent_receive_from_label] at H,
        injection H with H'', clear H,
        subst ans,
        apply_in Hp list.check_member_ok,
        fapply exists.intro, constructor,
        apply poll_dlabel.receive, exact ⟨ _, He ⟩,
        assumption, fapply poll_receive_dlabel.new_connection,
        assumption, assumption, dsimp,
        symmetry, assumption,
        dsimp [next_agent_state_from_dlabel],
        reflexivity,
      },
      { -- receive message
        cases (list.member_st_decide (λ (p : socket × message_t), p.snd = a_4) 
            (incoming.messages));
          dsimp [next_agent_receive_from_label] at H;
          try { contradiction },
        destruct (list.check_member ((list.member.value (list.member_st.to_member a_5)).fst) sockets),
          intros X, rw X at H,
          dsimp [next_agent_receive_from_label] at H,
          contradiction,
        intros p Hp, rw Hp at H,
           dsimp [next_agent_receive_from_label] at H,
        injection H with H', clear H, subst ans,
        apply_in Hp list.check_member_ok,
        fapply exists.intro, constructor,
        apply poll_dlabel.receive, exact ⟨ _, He ⟩,
        assumption, fapply poll_receive_dlabel.receive_message,
        exact a_5.to_member, assumption,
        symmetry, assumption,
        dsimp [next_agent_state_from_dlabel],
        f_equal, f_equal, f_equal,
        apply list.member_st_P_value a_5,
      }
    },
    { rw (dif_neg He) at H, contradiction
    }, 
  }
}
end

end

def next_state_from_label (system : system_state) 
  : next_state_label → option system_state
| (next_state_label.agent_update a_ip aupdate) := do
  a ← agents.check_member a_ip,
  option_bind (next_agent_state_from_label a_ip a.value
      (system.global_state a_ip) (system.local_state a) aupdate)
   $ λ p, let (next', update) := p in 
    some 
        { local_state  := lookup_update a next' system.local_state
        , global_state := update system.global_state }

def poll_result_to_label {ports : list port} {sockets : list socket}
  {timeout : time} : poll_result ports sockets timeout → poll_label
| poll_result.timeout := poll_label.timeout
| (poll_result.new_connection elapsed prt sock) := 
    poll_label.receive elapsed.val sock poll_receive_label.new_connection
| (poll_result.drop_connection elapsed sock) := 
    poll_label.receive elapsed.val sock.value poll_receive_label.drop_connection
| (poll_result.message elapsed sock mess) :=  
   poll_label.receive elapsed.val sock.value
     (poll_receive_label.receive_message mess)

open temporal

-- Our labeled transition system
def LTS (s : system_state) (l : next_state_label) (s' : system_state) : Prop :=
  next_state_from_label s l = some s'

def TR := trace (system_state × next_state_label)
def TP := tProp (system_state × next_state_label)


end

end network