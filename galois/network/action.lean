import galois.map.fmap_func
       galois.network.labels

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

lemma act_bind_send {B : Type} {rn : remote_name}
  {mess : message_t}
  (f : act B)
  : @send _ network.act_is_network_monad rn mess >> f 
    = act.send_message rn mess f
  := rfl

lemma act_bind_connect {B : Type} {rn : remote_name}
  (f : socket → act B)
  : @network_monad.connect _ network.act_is_network_monad rn >>= f 
    = act.connect rn f
  := rfl

lemma act_bind_return {A B : Type} {x : A}
  (f : A → act B)
  : return x >>= f 
    = f x
  := rfl
    

-- An agent is defined as a type for the internal state, an process that produces
-- the state, and a looping process that will execute when the process is complete.
--
-- Semantically, think of the behavior as `next >>= forever loop` where
-- `forever loop = loop >=> forever loop`.
structure agent : Type 1 :=
  (state_type : Type)
  (loop : state_type → act state_type)


section
parameters (ag : agent)

parameter {poll_receive_label_impl : list port → list socket → Type}

inductive poll_dlabel (ports : list port) (sockets : list socket) (bound : ℕ) : Type
| timeout {} : poll_dlabel
| receive {} : ∀ (elapsed_fin : fin bound) (rn : remote_name),
    poll_receive_label_impl ports sockets
    → poll_dlabel

inductive dlabel : act ag.state_type → Type
| update_own_state : ∀ new_state : ag.state_type, dlabel (act.return new_state)
| connect : ∀ (rn : remote_name) cont, dlabel (act.connect rn cont)
| send_message : ∀ sock mess cont,
      dlabel (act.send_message sock mess cont)
| poll : ∀ (ports : list port) (sockets : list socket) (bound : time) cont,
    poll_dlabel ports sockets bound
    → dlabel (act.poll ports sockets bound cont)

end

end network