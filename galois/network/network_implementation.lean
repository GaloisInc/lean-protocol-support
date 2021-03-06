-- author: Ben Sherman
import .action
       galois.tactic
       galois.option
       galois.temporal.temporal

universes u v

namespace network

structure incoming_items :=
  (messages : list (socket × message_t))

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

lemma lookup_update_different {A : Type u} [decidable_eq A] {B : A → Type v}
  {a a' : A} {b : B a} {f : ∀ a, B a} (H : a ≠ a') :
  lookup_update a b f a' = f a'
:= begin
unfold lookup_update lookup_updatef,
rw (dif_neg H),
end

@[reducible]
def global_state_t := ip → incoming_items

def initial_incoming_items : incoming_items
  := { messages := [] }

def poll_label.to_poll_result
  (ports : list port) (sockets : list socket) (bound : time)
  (incoming : incoming_items)
  : poll_label → option (poll_result ports sockets bound)
| poll_label.timeout := some poll_result.timeout
| (poll_label.receive elapsed rn mess) := do
  plift.up (and.intro H H') ← option.precondition (elapsed < bound ∧ 0 < elapsed),
  idx ← list.check_member_st (λ p : socket × message_t, p.snd = mess) incoming.messages,
  sockidx ← list.check_member idx.to_member.value.fst sockets, --any other checks necessary?
  some (poll_result.message ⟨ elapsed, H ⟩ sockidx mess H')

def agent_label.to_dlabel
  (incoming : incoming_items) {ag : agent}
: ∀ (a_next : act ag.state_type), agent_label → option (dlabel a_next)
| (act.poll ports sockets bound cont) (agent_label.mk plabel ms) := do
   r ← plabel.to_poll_result ports sockets bound incoming,
   guard ((cont r).fst = ms),
   some (dlabel.poll ports sockets bound cont r)

def add_message (rn : remote_name) (m : message_t) (a_ip : ip)
  : global_state_t → global_state_t :=
  lookup_updatef a_ip (λ i : incoming_items, {i with messages := (rn, m) :: i.messages })

def dlabel_to_label {A} : ∀ {a_next : act A}, dlabel a_next → agent_label
| (act.poll ports sockets bound cont) (dlabel.poll ._ ._ ._ ._ r) :=
  agent_label.mk r.to_label ((cont r).fst)

section
parameter {agents : map ip agent}

structure system_state : Type 1 :=
  (local_state : ∀ a : agents.member, a.value.state_type)
  (global_state : global_state_t)

structure sys_dlabel (st : system_state) :=
  (ag : agents.member)
  (label : dlabel (ag.value.loop (st.local_state ag)))

section
parameters (a_ip : ip) (ag : agent) (incoming : incoming_items)

def apply_message_updates (ms : list (socket × message_t))
   (updatef : global_state_t → global_state_t)
  : global_state_t → global_state_t
  := let fs := (list.map (λ p : socket × message_t, let (sock, mess) := p in
      add_message (a_ip, sock.snd) mess sock.fst) ms) in
     list.foldr function.comp updatef fs

def next_agent_state_poll_dlabel {A : Type} {ports : list port} {sockets : list socket}
  {bound : time} (cont : poll_result ports sockets bound → A)
  : poll_result ports sockets bound
  → option (global_state_t → global_state_t)
| poll_result.timeout := some id
| (poll_result.message elapsed_fin sock mess H) := do
    midx ← incoming.messages.check_member (sock.value, mess),
    some (lookup_updatef a_ip (λ inc, {inc with messages := list.remove_member _ midx}))

def next_agent_state_from_dlabel
  : ∀ {a_next : act ag.state_type} (la : dlabel a_next)
  , option (ag.state_type × (global_state_t → global_state_t))
| (act.poll ports sockets bound cont) (dlabel.poll ._ ._ ._ ._ r) := do
    updatef ← next_agent_state_poll_dlabel cont r,
    let (ms, new_state) := cont r,
    some (new_state, apply_message_updates ms updatef)

end

def next_state_from_dlabel (system : system_state)
  : sys_dlabel system → option system_state
| (sys_dlabel.mk ag aupdate) :=
  option.bind (next_agent_state_from_dlabel ag.key ag.value
     (system.global_state ag.key) aupdate)
     $ λ p, let (new_state, updatef) := p in
   some  { local_state  := lookup_update ag new_state system.local_state
        , global_state := updatef system.global_state }

open temporal

-- Our labeled transition system
def LTSd (s : system_state) (l : sys_dlabel s) (s' : system_state) : Prop :=
  next_state_from_dlabel s l = some s'

def TR := trace (sigma sys_dlabel)
def TP := tProp (sigma sys_dlabel)

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