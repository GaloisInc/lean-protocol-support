-- author: Ben Sherman
import .action
       galois.tactic
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

@[reducible]
def global_state_t := ip → incoming_items

def initial_incoming_items : incoming_items
  := { messages := [] }

def precondition (P : Prop) [decP : decidable P] : option (plift P) :=
  match decP with
  | decidable.is_true H := some (plift.up H)
  | decidable.is_false contra := none
  end

def poll_label.to_poll_result
  (ports : list port) (sockets : list socket) (bound : time)
  (incoming : incoming_items)
  : poll_label → option (poll_result ports sockets bound)
| poll_label.timeout := some poll_result.timeout
| (poll_label.receive elapsed rn mess) := do
  plift.up H ← precondition (elapsed < bound),
  idx ← list.check_member_st (λ p : socket × message_t, p.snd = mess) incoming.messages,
  sockidx ← list.check_member idx.to_member.value.fst sockets, --any other checks necessary?
  some (poll_result.message ⟨ elapsed, H ⟩ sockidx mess)

def agent_label.to_dlabel
  (incoming : incoming_items) {ag : agent}
: ∀ (a_next : act ag.state_type), agent_label → option (dlabel a_next)
| (act.poll ports sockets bound cont) (agent_label.poll plabel ms) := do
   r ← plabel.to_poll_result ports sockets bound incoming,
   guard ((cont r).fst = ms),
   some (dlabel.poll ports sockets bound cont r)

def add_message (rn : remote_name) (m : message_t) (a_ip : ip)
  : global_state_t → global_state_t :=
  lookup_updatef a_ip (λ i : incoming_items, {i with messages := (rn, m) :: i.messages })

def option_filter {A : Type u}
   (P : A → Prop) [decidable_pred P] : option A → option A
| (some x) := if P x then some x else none
| none := none

lemma option_filter_some {A : Type u}
  {P : A → Prop} [decP : decidable_pred P] {mx : option A} {x : A}
  (H : option_filter P mx = some x)
  : mx = some x ∧ P x
:= begin
cases mx; simp [option_filter] at H,
contradiction,
have H' := decP a, induction H' with H' H',
{ rw (if_neg H') at H, contradiction, },
{ rw (if_pos H') at H, injection H with H'', clear H,
  subst x, constructor, reflexivity, assumption }
end

def guard_option_filter {A : Type}
  {P : Prop} [decP : decidable P] (mx : option A) :
  (do guard P, mx) = option_filter (λ _, P) mx
:= begin
induction mx; induction decP; try { reflexivity }
end

lemma option_filter_true {A : Type u}
  {P : A → Prop} [decP : decidable_pred P] {x : A}
  (H : P x)
  : option_filter P (some x) = some x
:= begin
unfold option_filter, rw (if_pos H),
end

def dlabel_to_label {A} : ∀ {a_next : act A}, dlabel a_next → agent_label
| (act.poll ports sockets bound cont) (dlabel.poll ._ ._ ._ ._ r) :=
  agent_label.poll (poll_result_to_label r) ((cont r).fst)

section
parameter {agents : map ip agent}

structure system_state : Type 1 :=
  (local_state : ∀ a : agents.member, a.value.state_type)
  (global_state : global_state_t)

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
| (poll_result.message elapsed_fin sock mess) := do
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

def next_agent_state_from_label
   (ag : agents.member) (ag_state : ag.value.state_type)
   (ag_incoming : incoming_items)
   (aupdate : agent_label)
   : option (ag.value.state_type × (global_state_t → global_state_t)) := do
  option_bind (aupdate.to_dlabel ag_incoming (ag.value.loop ag_state)) $ λ la,
  next_agent_state_from_dlabel ag.key _ ag_incoming la

def next_state_from_label (system : system_state) 
  : next_state_label → option system_state
| (next_state_label.agent_update a_ip aupdate) := do
  ag ← agents.check_member a_ip,
  let incoming := system.global_state ag.key,
  option_bind (next_agent_state_from_label ag (system.local_state ag) incoming aupdate)
     $ λ p, let (new_state, updatef) := p in
   some  { local_state  := lookup_update ag new_state system.local_state
        , global_state := updatef system.global_state }
  

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