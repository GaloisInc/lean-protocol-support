-- author: Ben Sherman
import .action
       galois.tactic
       galois.temporal.temporal

universes u v

namespace network

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

inductive poll_receive_dlabel (ports : list port) (sockets : list socket)
    : Type
| new_connection {} : ∀ (sock : list.member_st (λ s : socket_info, s.server = a_ip ∧ s.new) incoming.sockets)
    (p : ports.member),
    sock.to_member.value.port = p.value →
    poll_receive_dlabel
| receive_message {} : ∀ (mess : incoming.messages.member)
    (sock : sockets.member),
    mess.value.fst = sock.value → 
    poll_receive_dlabel

def dlabel' {a} := @dlabel a poll_receive_dlabel

def next_agent_state_receive_dlabel {ports : list port} {sockets : list socket}
  {bound : time}
  (cont : poll_result ports sockets bound → act a.state_type)
  (elapsed_fin : fin bound) (rn : remote_name)
  : poll_receive_dlabel ports sockets
  → act a.state_type × (global_state_t → global_state_t)
| (poll_receive_dlabel.new_connection sock p _) := 
let s := sock.to_member in
      (cont (poll_result.new_connection elapsed_fin p s.value.socket)
      , lookup_updatef a_ip (λ inc, {inc with sockets := list.update_member ({s.value with new := false}) _ s}))
| (poll_receive_dlabel.receive_message mess sock _) := 
  (cont (poll_result.message elapsed_fin sock mess.value.snd)
        , lookup_updatef a_ip (λ inc, {inc with messages := list.remove_member _ mess}))

def next_agent_state_poll_dlabel {ports : list port} {sockets : list socket}
  {bound : time} (cont : poll_result ports sockets bound → act a.state_type)
  : @poll_dlabel poll_receive_dlabel ports sockets bound 
  → act a.state_type × (global_state_t → global_state_t)
| poll_dlabel.timeout := (cont (poll_result.timeout), id)
| (poll_dlabel.receive elapsed_fin rn rlabel) := next_agent_state_receive_dlabel
     cont elapsed_fin rn rlabel

def next_agent_state_from_dlabel
  : ∀ (a_next : act a.state_type) (la : dlabel' a_next)
  , act a.state_type × (global_state_t → global_state_t)
| (act.return new_state) (dlabel.update_own_state ._) := (a.loop new_state, id)
| (act.connect rn cont) (dlabel.connect ._ ._) := 
   let s_info := socket_info.mk a_ip rn.fst rn.snd true in
      (cont rn, add_socket s_info rn.fst)
| (act.send_message sock mess cont) (dlabel.send_message ._ ._ ._) := 
     (cont, add_message (a_ip, sock.snd) mess sock.fst)
| (act.poll ports sockets bound cont) (dlabel.poll ._ ._ ._ ._ plabel)
    := next_agent_state_poll_dlabel cont plabel

def dlabel_to_label {a_next : act a.state_type} (la : dlabel' a_next)
  : agent_label
:= begin
cases la,
{ -- update_own_state
exact agent_label.update_own_state,
},
{ -- connect
exact agent_label.connect rn,
},
{ -- send message
exact agent_label.send_message sock mess,
},
{ -- poll
apply agent_label.poll,
induction a_1,
  { -- timeout
    exact poll_label.timeout,
  },
  { -- receive
    apply (poll_label.receive elapsed_fin.val rn),
    induction a_1,
    { -- new connection
      exact poll_receive_label.new_connection
    },
    { -- receive message
      exact poll_receive_label.receive_message mess.value.snd,
    }
  }
}
end

lemma dlabel_to_label_some {a_next : act a.state_type} (la : dlabel' a_next)
  : next_agent_state_from_label a_next (dlabel_to_label la) 
    = some (next_agent_state_from_dlabel _ la)
:= begin
induction la; dsimp [dlabel_to_label, next_agent_state_from_dlabel];
  simp [next_agent_state_from_label],
induction a_1; dsimp [dlabel_to_label, next_agent_state_poll_dlabel];
  simp [next_agent_poll_state_from_label],
rw (dif_pos elapsed_fin.is_lt),
induction a_1; dsimp [dlabel_to_label, next_agent_state_from_dlabel];
  simp [next_agent_receive_from_label],
{ have H := list.member_st_decide_present sock,
  induction H with sock' Psock',
  rw Psock',
  dsimp [next_agent_receive_from_label],
  /- there seems to generally be a missing fact/invariant here -/
  admit },
{ have H : mess.value.snd = mess.value.snd := rfl,
  have H' := mess.to_member_st (λ x, x.snd = mess.value.snd) H,
  clear H,
  have H := list.member_st_decide_present H',
  induction H with mess' Pmess', rw Pmess',
  clear H',
  dsimp [next_agent_receive_from_label],
  /- there also seems to be some missing facts/invariants here -/
  admit }
end

/-- Any step that we can take with a regular label, we can take 
    with a dependent label. Therefore, it is sound to reason based
    on the dependent-label traces.
-/
lemma label_dlabel_equiv {a_next : act a.state_type}
  : ∀ {ans l}, next_agent_state_from_label a_next l = some ans
  → psigma (λ l' : dlabel' a_next, next_agent_state_from_dlabel a_next l' = ans)
:= begin
intros ans l H,
induction l; simp [next_agent_state_from_label] at H,
{ cases a_next;
    dsimp [next_agent_state_from_label] at H;
    try { contradiction },
  injection H with H', clear H, rw ← H',
  fapply psigma.mk, constructor, reflexivity,
},
{ cases a_next;
    dsimp [next_agent_state_from_label] at H;
    try { contradiction },
  apply (if Hs : a_1 = a_2 then _ else _),
  { rw (if_pos Hs) at H, subst Hs,
    injection H with H',
    clear H, rw ← H',
    fapply psigma.mk, constructor,
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
    fapply psigma.mk, constructor,
    induction Heq with H1 H2,
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
  { fapply psigma.mk, constructor,
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
        fapply psigma.mk, constructor,
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
        fapply psigma.mk, constructor,
        apply poll_dlabel.receive, exact ⟨ _, He ⟩,
        assumption, fapply poll_receive_dlabel.receive_message,
        exact a_5.to_member, assumption,
        symmetry, assumption,
        dsimp [next_agent_state_poll_dlabel, 
          next_agent_state_from_dlabel, next_agent_state_from_dlabel,
          next_agent_state_receive_dlabel],
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

open temporal

-- Our labeled transition system
def LTS (s : system_state) (l : next_state_label) (s' : system_state) : Prop :=
  next_state_from_label s l = some s'

def TR := trace (sigma (λ _ : system_state, next_state_label))
def TP := tProp (sigma (λ _ : system_state, next_state_label))

/--
Apply a function (usually a predicate) to the label of a state-label pair
-/
def inLabel {S} {L} {B} (f : L → B) (x : sigma (λ _ : S, L)) : B := f x.snd
/--
If we apply a decidable prop to the label, that application is decidable
-/
instance inLabel_decidable {S L} {P : L → Prop} [decP : decidable_pred P] :
  decidable_pred (@inLabel S L _ P) :=
begin
intros x, apply decP,
end

lemma inLabel_mono {S} {L} : subset.monotone (@inLabel S L Prop)
:= begin
intros P Q PQ x Hx, apply PQ, apply Hx
end

end

end network