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
  (local_state : ∀ a : agents.member, a.value.state_type)
  (global_state : global_state_t)

def initial_incoming_items : incoming_items
  := { sockets := []
     , messages := [] }

def next_agent_poll_state_from_label (a_ip : ip) {A : Type u}
  (ports : list port) (sockets : list socket) (bound : time)
  (incoming : incoming_items)
  (cont : poll_result ports sockets bound → A)
  : poll_label → option (A × (global_state_t → global_state_t))
| (poll_label.receive elapsed rn mess) :=
-- OOPS, need to fix: to receive message, I should already have been
-- informed of the new connection that the message has transferred over
  if H : elapsed < bound 
    then let elapsed_fin : fin bound := ⟨ elapsed, H ⟩ in
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
     else none
| poll_label.timeout := some (cont poll_result.timeout, id)

def add_message (rn : remote_name) (m : message_t) (a_ip : ip)
  : global_state_t → global_state_t :=
  lookup_updatef a_ip (λ i : incoming_items, {i with messages := (rn, m) :: i.messages })

def option_filter {A : Type u}
   (P : A → Prop) [decidable_pred P] : option A → option A
| (some x) := if P x then some x else none
| none := none

section
parameters (a_ip : ip) (a : agent) (incoming : incoming_items)

def next_agent_state_from_label
  : act a.state_type → agent_label → 
    option ((list (socket × message_t) × a.state_type) × (global_state_t → global_state_t))
| (act.poll ports sockets bound after) (agent_label.poll plabel ms) :=
  option_filter (λ x, x.fst.fst = ms)
    (next_agent_poll_state_from_label a_ip
              ports sockets bound incoming after plabel)

inductive poll_receive_dlabel (ports : list port) (sockets : list socket)
    : Type
| receive_message {} : ∀ (mess : incoming.messages.member) (sock : sockets.member),
    mess.value.fst = sock.value → 
    poll_receive_dlabel

def dlabel' {a} := @dlabel a poll_receive_dlabel

def next_agent_state_poll_dlabel {A} {ports : list port} {sockets : list socket}
  {bound : time} (cont : poll_result ports sockets bound → A)
  : @poll_dlabel poll_receive_dlabel ports sockets bound 
  → A × (global_state_t → global_state_t)
| poll_dlabel.timeout := (cont poll_result.timeout, id)
| (poll_dlabel.receive elapsed_fin rn (poll_receive_dlabel.receive_message mess sock _)) 
  := (cont (poll_result.message elapsed_fin sock mess.value.snd)
        , lookup_updatef a_ip (λ inc, {inc with messages := list.remove_member _ mess}))

def next_agent_state_from_dlabel
  : ∀ (a_next : act a.state_type) (la : dlabel' a_next)
  , (list (socket × message_t) × a.state_type) × (global_state_t → global_state_t)
| (act.poll ports sockets bound cont) (dlabel.poll ._ ._ ._ ._ ms plabel)
    := next_agent_state_poll_dlabel cont plabel

def dlabel_to_label {a_next : act a.state_type} (la : dlabel' a_next)
  : agent_label
:= begin
cases la,
apply agent_label.poll,
induction a_1,
  { -- timeout
    exact poll_label.timeout,
  },
  { -- receive
    apply (poll_label.receive elapsed_fin.val rn),
    induction a_1,
    apply mess.value.snd
  },
assumption
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
cases a_next;
    dsimp [next_agent_state_from_label] at H,
  cases a_1;
    dsimp [next_agent_poll_state_from_label] at H,
  { injection H with H', clear H, subst ans,
    fapply psigma.mk, constructor, assumption,
    apply poll_dlabel.timeout,
    reflexivity,
  },
  { apply (if He : a_1 < bound then _ else _),
    { rw (dif_pos He) at H,
      induction a_5; dsimp [next_agent_receive_from_label] at H;
         try {contradiction},
      { -- new connection 
        cases (list.member_st_decide (λ (s : socket_info), s.server = a_ip ∧ ↑(s.new)) 
            (incoming.sockets));
           dsimp [next_agent_receive_from_label] at H;
           try { contradiction },
        destruct (list.check_member ((a_5.to_member).value.port) ports), intros X,
           rw X at H,
           dsimp [next_agent_receive_from_label] at H,
           contradiction,
        intros p Hp, rw Hp at H,
           dsimp [next_agent_receive_from_label] at H,
        injection H with H'', clear H,
        subst ans,
        apply_in Hp list.check_member_ok,
        fapply psigma.mk, constructor, assumption,
        apply poll_dlabel.receive, exact ⟨ _, He ⟩,
        assumption, fapply poll_receive_dlabel.new_connection,
        assumption, assumption, dsimp,
        symmetry, assumption,
        dsimp [next_agent_state_from_dlabel],
        reflexivity,
      },
      { -- receive message
        cases (list.member_st_decide (λ (p : socket × message_t), p.snd = a_5) 
            (incoming.messages));
          dsimp [next_agent_receive_from_label] at H;
          try { contradiction },
        destruct (list.check_member ((list.member.value (list.member_st.to_member a_6)).fst) sockets),
          intros X, rw X at H,
          dsimp [next_agent_receive_from_label] at H,
          contradiction,
        intros p Hp, rw Hp at H,
           dsimp [next_agent_receive_from_label] at H,
        injection H with H', clear H, subst ans,
        apply_in Hp list.check_member_ok,
        fapply psigma.mk, constructor, assumption,
        apply poll_dlabel.receive, exact ⟨ _, He ⟩,
        assumption, fapply poll_receive_dlabel.receive_message,
        exact a_6.to_member, assumption,
        symmetry, assumption,
        dsimp [next_agent_state_poll_dlabel, 
          next_agent_state_from_dlabel, next_agent_state_from_dlabel,
          next_agent_state_receive_dlabel],
        f_equal, f_equal, f_equal,
        apply list.member_st_P_value a_6,
      }
    },
    { rw (dif_neg He) at H, contradiction
    },
  }
end

end

def next_state_from_label (system : system_state) 
  : next_state_label → option system_state
| (next_state_label.agent_update a_ip aupdate) := do
  a ← agents.check_member a_ip,
  option_bind (next_agent_state_from_label a_ip a.value
      (system.global_state a_ip) (a.value.loop (system.local_state a)) aupdate)
   $ λ p, let ((ms, new_state), updatef) := p in
   let fs := (list.map (λ p : socket × message_t, let (sock, mess) := p in 
      add_message (a_ip, sock.snd) mess sock.fst) ms) in
   let updatef' : global_state_t → global_state_t := 
          list.foldr function.comp updatef fs in
    some 
        { local_state  := lookup_update a new_state system.local_state
        , global_state := updatef' system.global_state }

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