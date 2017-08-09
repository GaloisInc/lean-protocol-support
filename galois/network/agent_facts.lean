import galois.network.network_implementation
       galois.temporal.fixpoint
       galois.temporal.classical

universes u

namespace network

open temporal

section
parameter {agents : map ip agent}

instance decidable_agent_does (a_ip : ip) {P}
  [decidable_pred P] : decidable_pred (agent_does a_ip P)
:= begin 
intros l, induction l with a_ip' l,
apply (if Hip : a_ip = a_ip' then _ else _),
{ apply (if H : P l then _ else _),
  subst a_ip',
  { apply decidable.is_true,
    constructor, assumption } ,
  { apply decidable.is_false,
    intros contra, cases contra, contradiction }
 },
{ apply decidable.is_false, intros contra,
  cases contra, contradiction }
end

inductive next_state_from_label_ind' (ag : agents.member) (s : system_state) (la : agent_label) (s' : system_state) : Prop
| mk : ∀ (next' : act ag.value.state_type) (updatef : global_state_t → global_state_t)
       (Hagl : next_agent_state_from_label ag.key ag.value (s.local_state ag) ((s.global_state ag.key)) la = some (next', updatef))
       (Hupd : s' = {local_state := lookup_update ag next' (s.local_state)
                    , global_state := updatef (s.global_state)})
      , next_state_from_label_ind'

inductive next_state_from_label_ind (a_ip : ip) (s : system_state) (la : agent_label) (s' : system_state) : Prop
| mk : ∀ (ag : agents.member) (Hip : ag.key = a_ip)
         (H : next_state_from_label_ind' ag s la s'), next_state_from_label_ind


lemma option_bind_some {A B} {ma : option A} {f : A → option B}
  {b : B} (H : option_bind ma f = some b)
  : ∃ a : A, ma = some a ∧ f a = some b
:= begin
cases ma,
contradiction,
existsi a, split, reflexivity, assumption
end

lemma agent_update_invert_st' {s la s'}
  {ag : agents.member}
  : LTS s (next_state_label.agent_update ag.key la) s'
  → next_state_from_label_ind' ag s la s'
:= begin
intros H,
simp [LTS] at H,
simp [next_state_from_label] at H,
apply_in H option_bind_some,
induction H with ag' p, induction p with Hag1 Hag2,
dsimp at Hag2,
apply_in Hag1 mapd.check_member_same, subst ag',
apply_in Hag2 option_bind_some,
induction Hag2 with p1 p2,
induction p1 with next' updatef,
induction p2 with H1 H2,
dsimp [next_state_from_label] at H2,
injection H2 with H2', clear H2,
constructor; try {assumption},
symmetry, assumption
end

lemma agent_update_invert_st {s la s'}
  {a_ip : ip}
  : LTS s (next_state_label.agent_update a_ip la) s'
  → next_state_from_label_ind a_ip s la s'
:= begin
intros H, have H1 := H,
have H' := option_bind_some H,
clear H, induction H' with ag p, induction p with Hag1 Hag2,
have H1 := mapd.check_member_same_key Hag1,
subst a_ip,
constructor, reflexivity,
apply agent_update_invert_st', assumption,
end

lemma agent_does_invert {a_ip : ip} {P : agent_label → Prop}
  {l : next_state_label}
  (H : agent_does a_ip P l)
  : ∃ (la : agent_label), P la
   ∧ l = next_state_label.agent_update a_ip la
:= begin
induction H, constructor, split, assumption,
reflexivity
end

/-- Every agent always eventually gets to step -/
def fairness_spec : @TP agents
  := λ tr : TR, ∀ (a : agents.member),
   fair (now (inLabel (agent_does a.key (λ _, true)))) tr


lemma agent_update_invert {tr : TR} (a_ip : ip)
  (validtr : valid_trace LTS tr)
  {n : nat}
  {la : agent_label}
  (H : (tr n).snd = next_state_label.agent_update a_ip la)
  : next_state_from_label_ind a_ip (tr n).fst la (tr n.succ).fst
:= begin
have Hn := validtr.next_step n,
apply agent_update_invert_st,
rw <- H,
apply (validtr.next_step n),
end

lemma agent_update_invert' {tr : TR} (ag : agents.member)
  (validtr : valid_trace LTS tr)
  {n : nat}
  {la : agent_label}
  (H : (tr n).snd = next_state_label.agent_update ag.key la)
  : next_state_from_label_ind' ag (tr n).fst la (tr n.succ).fst
:= begin
have Hn := validtr.next_step n,
apply agent_update_invert_st',
rw <- H,
apply (validtr.next_step n),
end

/-- Indicates that an agent is at the beginning of running 
    an iteration of its loop (or doing something equivalent
    to that) 
-/
def starts_loop {a : agents.member} (next : act a.value.state_type) : Prop :=
  ∃ (s : a.value.state_type), next = a.value.loop s

lemma return_implies_starts_loop (a : agents.member) :
  ∀ {s s' : system_state} {l : next_state_label},
    LTS s l s'
  → agent_does a.key (eq agent_label.update_own_state) l
  → starts_loop (s'.local_state a)
:= begin
intros s s' l Hs' Hl,
cases Hl with l Hl', clear Hl,
subst l,
apply_in Hs' agent_update_invert_st',
induction Hs', subst s',
unfold starts_loop,
simp [next_agent_state_from_label] at Hagl,
rename a ag,
cases (s.local_state ag); 
  simp [next_agent_state_from_label] at Hagl;
  try {contradiction},
injection Hagl with Hagl', clear Hagl,
existsi a,
injection Hagl' with Hpl Hpr,
subst next', dsimp, rw lookup_update_refl,
end

def inLocalState (a : agents.member) (P : act a.value.state_type → Prop)
  : system_state × next_state_label → Prop
  := inState (λ s, P (s.local_state a))


lemma return_implies_starts_loop_ltl (a : agents.member) :
 ⊩ valid_trace LTS 
   => □ (now (inLabel (agent_does a.key (eq agent_label.update_own_state)))
         => ◯ (now (inLocalState a starts_loop)))
:= begin
apply prove_always,
intros, apply return_implies_starts_loop; assumption,
end

/- It feels like it should be possible to auto-generate something like
   this, which says when one term is directly a strict subterm of another
   (using if strictly_smaller^+ x y, then we can make a recursive call
   from x to y)
-/
inductive strictly_smaller {A : Type u} (a : act A) : act A → Prop
| connect : ∀ (rn : remote_name) (cont : socket → act A)
              (s : socket) (H : cont s = a), strictly_smaller (act.connect rn cont)
| send_message : ∀ (s : socket) (m : message_t) (cont : act A)
                (H : cont = a), strictly_smaller (act.send_message s m cont)
| poll : ∀ (ports : list port) (sockets : list socket) (bound : time)
      (cont : poll_result ports sockets bound → act A)
      (x : poll_result ports sockets bound) (H : cont x = a), 
      strictly_smaller (act.poll ports sockets bound cont)

/- Indeed, this relation is well-founded -/
lemma strictly_smaller_wf {A : Type u} : well_founded (@strictly_smaller A)
:= begin
constructor,
intros x, induction x; constructor; intros,
{ cases a_1, },
{ cases a_2, subst y, apply ih_1 },
{ cases a_3, subst y, apply ih_1 },
{ cases a_1, subst y, apply ih_1 }
end

/-- When an agent takes a step, if the code it had to run was an
    `act.return`, it returns to the top of its loop, and otherwise,
    it "proceeds" down its current code, that is, its new state for the
    code it will run is strictly smaller than it just was, since we're
    using the continuation-passing representation.
-/
lemma size_decreases {ag : agents.member} (a_ip : ip)
  {la : agent_label}
  {next' : act ag.value.state_type}
  {updatef : global_state_t → global_state_t}
  {s : system_state}
  (H : next_agent_state_from_label a_ip ag.value (s.local_state ag)
        (s.global_state a_ip) la = some (next', updatef))
  : (match (s.local_state ag) with 
  | act.return x := la = agent_label.update_own_state ∧ next' = ag.value.loop x
  | _ := strictly_smaller next' (s.local_state ag)
  end : Prop)
  := begin
generalize Hla : la = la',
induction la; simp [next_agent_state_from_label] at H,
{ cases (s.local_state ag); 
    dsimp [next_agent_state_from_label] at H;
    try { contradiction }; dsimp,
  injection H with H', clear H,
  injection H' with H1 H2, clear H', split;
   symmetry; assumption },
{ cases (s.local_state ag); 
    dsimp [next_agent_state_from_label] at H;
    try { contradiction }; dsimp,
  apply (if Hs : a = a_1 then _ else _),
  { rw (if_pos Hs) at H,
    injection H with H',
    clear H, injection H' with H1 H2, clear H',
    apply strictly_smaller.connect, assumption
  },
  { rw (if_neg Hs) at H, contradiction
  },
},
{ cases (s.local_state ag); 
    dsimp [next_agent_state_from_label] at H;
    try { contradiction }; dsimp,
  apply (if Heq : (a = a_2 ∧ a_1 = a_3) then _ else _),
  { rw (if_pos Heq) at H,
    injection H with H',
    clear H, injection H' with H1 H2, clear H',
    apply strictly_smaller.send_message, assumption
  },
  { rw (if_neg Heq) at H, contradiction
  },
},
{ cases (s.local_state ag); 
    dsimp [next_agent_state_from_label] at H;
    try { contradiction }; dsimp,
  induction a; simp [next_agent_poll_state_from_label] at H,
  { injection H with H', clear H, injection H' with H1 H2,
    clear H', apply strictly_smaller.poll, assumption
  },
  { apply (if He : a < bound then _ else _),
    { rw (dif_pos He) at H,
      induction a_3; 
        dsimp [next_agent_poll_state_from_label] at H;
        try { contradiction },
      { -- new connection 
        cases (list.member_st_decide 
         (λ s : socket_info, s.server = a_ip ∧ s.new) (s.global_state a_ip).sockets);
           dsimp [next_agent_poll_state_from_label] at H;
           try { contradiction },
        cases (list.check_member ((list.get_member (list.member_st_to_member a_3)).port) ports);
           dsimp [next_agent_poll_state_from_label] at H;
           try { contradiction },
        injection H with H', clear H, injection H' with H1 H2,
        clear H' H2, apply strictly_smaller.poll, assumption
      },
      { -- new message
        cases ((list.member_st_decide 
          (λ (p : socket × message_t), p.snd = a_3) ((s.global_state a_ip).messages)));
          dsimp [next_agent_poll_state_from_label] at H;
          try { contradiction },
        cases (list.check_member ((list.get_member (list.member_st_to_member a_4)).fst) sockets);
          dsimp [next_agent_poll_state_from_label] at H;
          try { contradiction },
        injection H with H', clear H, injection H' with H1 H2,
        clear H' H2, apply strictly_smaller.poll, assumption
      }
    },
    { rw (dif_neg He) at H, contradiction
    },    
  }
}
end

lemma size_decreases' {ag : agents.member} (a_ip : ip)
  {la : agent_label}
  {next' : act ag.value.state_type}
  {updatef : global_state_t → global_state_t}
  {s : system_state}
  (H : next_agent_state_from_label a_ip ag.value (s.local_state ag)
        (s.global_state a_ip) la = some (next', updatef))
  : strictly_smaller next' (s.local_state ag) 
  ∨ la = agent_label.update_own_state ∧ ∃ x, next' = ag.value.loop x
:= begin
apply_in H size_decreases,
cases (s.local_state ag); dsimp at H;
  try { left, assumption },
{ right, induction H with H1 H2, 
  split, assumption, constructor, assumption },
end

lemma return_implies_starts_loop_simple (a : agents.member)
  : ⊩ valid_trace LTS 
    => ◇ (now (inLabel (agent_does a.key (eq agent_label.update_own_state))))
    => ◇ (now (inLocalState a starts_loop))
:= begin
intros tr validtr H,
apply eventually_cut, assumption,
intros n H, apply next_eventually,
apply return_implies_starts_loop_ltl; assumption
end

/-- If a transition occurs that doesn't involve a particular agent,
    that agent's state doesn't change.
-/
lemma local_state_stays_constant {s l s'}
  (a : agents.member)
  (HLTS : LTS s l s')
  (Hagent : ¬agent_does (a.key) (λ (_x : agent_label), true) l)
  : s.local_state a = s'.local_state a
:= begin
induction l with a_ip la,
apply_in HLTS agent_update_invert_st,
induction HLTS with ag Hip H, subst a_ip,
induction H,
subst s', dsimp, unfold lookup_update lookup_updatef,
apply (if Heq : ag = a then _ else _),
{ exfalso, subst ag,
 apply Hagent,
 constructor, trivial },
{ rw (dif_neg Heq) }
end

/-- A statement of the fact that a particular agent's state 
    doesn't change (weak-) until it takes a step within
    temporal logic.
    (Using the sort of Leibniz equality: Any predicate `P`
    that held on the old state will hold on the new state)
-/
lemma local_state_stays_constant_ltl (a : agents.member)
  (P : act a.value.state_type → Prop)
  : ⊩ valid_trace LTS
    => □ (now (inLocalState a P)
    => (◯ (now (inLocalState a P))
        𝓦
       now (inLabel (agent_does a.key (λ _, true))))
    )
:= begin
intros tr validtr n Pst,
unfold inLocalState,
apply (invariant_holds_while LTS _ _ _ (delayn n tr)),
apply valid_trace_always, assumption, assumption,
apply_instance,
intros,
have H := local_state_stays_constant _ a_1 a_2,
rw ← H, assumption,
end

/-- If we take a step, then either our "next" code will be strictly
    smaller than it just was, or we will be at the top of a loop
-/
lemma agent_advances_helper2
  (a : agents.member)
  (ag_next : act a.value.state_type)
  : ⊩ valid_trace LTS
    => □ (now (inLocalState a (λ s, ag_next = s))
       => now ((inLabel (agent_does a.key (λ _, true))))
       => ◯ (now (inLocalState a (λ s, strictly_smaller s ag_next ∨ starts_loop s))))
:= begin
intros tr trvalid,
unfold inLocalState inState implies,
intros n agnext Hk,
-- Don't just use fairness! Need to use the "first"
-- version of fairness
apply_in Hk agent_does_invert,
induction Hk with la p, induction p with X upd,
clear X,
have H := agent_update_invert' a trvalid upd,
induction H,
simp at Hagl Hupd,
apply_in Hagl size_decreases',
simp [inState] with ltl,
rw Hupd, dsimp, rw lookup_update_refl,
induction Hagl,
{ -- strictly smaller (recursive case)
right,
unfold now inState later at agnext,
subst ag_next, simp with ltl,
assumption
},
{ -- loop (base case)
left, 
induction a_1 with state next'loop,
unfold starts_loop,
assumption,
}
end

/-- Assuming fairness, if we currently have some `next` code we are planning
    to run, eventually we will either have a smaller `next` code or we will
    be at the top of a loop.
-/
lemma agent_advances_helper1
  (a : agents.member)
  (ag_next : act a.value.state_type)
  : ⊩ valid_trace LTS => fairness_spec
    => □ (now (inLocalState a (λ s, ag_next = s))
           => ◇ (now (inLocalState a (λ s, strictly_smaller s ag_next ∨ starts_loop s)))
         )
:= begin
intros tr trvalid trfair n Hnow,
have H := local_state_stays_constant_ltl _ _ _ _ _ Hnow,
apply_in H (eventually_strengthen_until _ (trfair a n)),
have H' := now_until_eventually _ Hnow H,
clear Hnow H,
apply eventually_cut, assumption,
intros k H, induction H with H1 H2,
apply next_eventually, 
apply agent_advances_helper2; try {assumption},
apply valid_trace_always, assumption, assumption,
end

lemma inLocalState_meas_same (a : agents.member) (ag_next : act a.value.state_type)
  : inLocalState a (λ s, ag_next = s) 
  = λ s, (λ s' : system_state × next_state_label, s'.fst.local_state a) s = ag_next
:= begin
apply funext, intros x, dsimp [inLocalState, inState], apply propext,
split; intros; symmetry; assumption
end

/-- Assuming fairness, whenever we are in any particular state,
    we'll eventually return to the top of a loop.
-/
lemma agent_advances_helper
  (a : agents.member)
  (ag_next : act a.value.state_type)
  : ⊩ valid_trace LTS => fairness_spec =>
   □ (now (inLocalState a (λ s, ag_next = s))
      => ◇ (now (inLocalState a starts_loop)))
:= begin
intros tr trvalid trfair,
rw inLocalState_meas_same,
apply always_eventually_well_founded,
apply strictly_smaller_wf, intros,
rw ← inLocalState_meas_same,
apply agent_advances_helper1; assumption,
end

/-- The main theorem: supposing fairness, an agent always eventually
    returns to the top of its loop
-/
theorem agent_advances (a : agents.member) :
  ⊩ valid_trace LTS => fairness_spec => fair (now (inLocalState a starts_loop))
:= begin
intros tr trvalid trfair n,
apply agent_advances_helper a _ tr trvalid trfair n rfl,
end

/-- If an agent always eventually polls, and if it is sent a message,
    then it eventually receives that message.
-/
def message_fairness_spec : @TP agents := λ tr,
  ∀ (a : agents.member) (mess : (socket × message_t)),
    (fair (now (inLabel (agent_does a.key polls))) 
     => □ (now (inState (λ s : system_state, mess ∈ (s.global_state a.key).messages))
           => ◇ (now (inLabel (agent_does a.key (receives_message mess.snd)))))) tr



end

inductive can_possibly_step (a_ip : ip) (a : agent) 
  (s : act a.state_type) (l : next_state_label) (s' : act a.state_type) : Prop
| mk : ∀ 
  (agents : map ip agent)
  (Hmap : mapd.find a_ip agents = some a)
  (ss ss' : @system_state agents)
  (loc : ss.local_state ⟨ _, _, Hmap ⟩ = s)
  (loc' : ss'.local_state ⟨ _, _, Hmap ⟩ = s')
  (HLTS : LTS ss l ss'),
  can_possibly_step

inductive will_poll {a : agent} : act a.state_type → Prop
| mk : ∀ 
  (ports : list port)
  (sockets : list socket)
  (bound : time)
  (cont : poll_result ports sockets bound → act a.state_type),
  will_poll (act.poll ports sockets bound cont)

section
parameters (a_ip : ip) 
  (a : agent)
  (P : poll_receive_label → Prop)

lemma blocks_until_not_never_receives_always_polls
  : ⊩ valid_trace (can_possibly_step a_ip a)
    => (◇ (now (inLabel (agent_does a_ip polls))) 
        𝓦 (now (inLabel (agent_does a_ip (receives P)))))
    => □ (tNot (now (inLabel (agent_does a_ip (receives P)))))
    => fair (now (inState (@will_poll a)))
:= begin
intros tr valid nows,
admit
end

end

/--
   As Joey and I discussed, the way this proof should go is as follows:
   Use classical logic to do a proof by contradiction. Assume that we
   never receive the message. Then,
   use message fairness in conjunction with with the fact that we
   have a message in the queue to derive that
   H : if the agent always eventually polls, it eventually receives the message.
   Next, use the fact that we do *not* eventually receive the message,
   together with the fact that we block until we receive the message,
   to derive that we always eventually poll.
   Combining this with the `H` specified above, we find that we
   eventually do receive the message, a contradiction.
-/
theorem blocking_agent_eventually_receives_message {agents : map ip agent}
  (a : agents.member) (mess : (socket × message_t))
  : ⊩ valid_trace (@LTS agents)
    => fairness_spec
    => message_fairness_spec
    => (◇ (now (inLabel (agent_does a.key polls))) 
        𝓦 (now (inLabel (agent_does a.key (receives_message mess.snd)))))
    => □ (tNot (now (inLabel (agent_does a.key (receives_message mess.snd)))))
    => now (inState (λ ss : system_state, 
         mess ∈ (ss.global_state a.key).messages))
    => ◇ (now (inLabel (agent_does a.key (receives_message mess.snd))))
:= begin
intros tr valid fair mfair nowstate messstate H,
apply classical.not_always_not_implies_eventually,
intros contra,
admit
end

end network