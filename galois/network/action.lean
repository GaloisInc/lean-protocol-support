import galois.map.fmap_func
       galois.network.labels

universes u v


namespace network

inductive act (A : Type u) : Type u
-- return a poll result and the amount of time elapsed
| poll : Π (ports : list port) (sockets : list socket) (bound : time), 
     (poll_result ports sockets bound → (list (socket × message_t) × A)) → act

namespace act
def just_send_messages {A : Type u} (ms : list (socket × message_t)) 
  (x : A) := act.poll [] [] 0 (λ _, (ms, x))

def return {A : Type u} (x : A) : act A := just_send_messages [] x
end act

/-- Indicates that an agent is polling -/
inductive polls_on_socket {A : Type u} (s : socket) : act A → Prop
| mk : ∀ ports sockets bound cont, 0 < bound → s ∈ sockets 
  → polls_on_socket (act.poll ports sockets bound cont)

instance polls_decidable {A : Type} (s : socket) : decidable_pred (@polls_on_socket A s)
:= begin
intros x, induction x,
apply (if H : 0 < bound ∧ s ∈ sockets then _ else _),
{ apply decidable.is_true, induction H with H1 H2,
  constructor; assumption },
{ apply decidable.is_false, intros contra, cases contra,
  apply H, split; assumption }
end

-- An agent is defined as a type for the internal state, an process that produces
-- the state, and a looping process that will execute when the process is complete.
--
-- Semantically, think of the behavior as `next >>= forever loop` where
-- `forever loop = loop >=> forever loop`.
structure agent : Type 1 :=
  (state_type : Type)
  (loop : state_type → act state_type)


inductive dlabel {A : Type u} : act A → Type u
| poll : ∀ (ports : list port) (sockets : list socket) (bound : time) cont
    (r : poll_result ports sockets bound),
    dlabel (act.poll ports sockets bound cont)

namespace dlabel
def cont_result {A : Type u} : ∀ {next : act A} (la : dlabel next), 
   list (socket × message_t) × A
| (act.poll ports sockets bound cont) (dlabel.poll ._ ._ ._ ._ r) := cont r

def messages {A : Type u} {next : act A} (la : dlabel next) : list (socket × message_t)
  := la.cont_result.fst

lemma invert {A : Type u} 
  {ports sockets bound cont} (l : @dlabel A (act.poll ports sockets bound cont))
  : ∃ r : poll_result ports sockets bound,
    l = dlabel.poll ports sockets bound cont r
:= begin
cases l, constructor, reflexivity
end
end dlabel

end network