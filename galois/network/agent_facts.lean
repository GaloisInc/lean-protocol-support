-- author: Ben Sherman

import galois.network.network_implementation
       galois.temporal.fixpoint
       galois.temporal.classical
       galois.temporal.LTS

universes u

/-- reflexive-transitive closure of a relation -/
inductive RTclosure {A : Type u} (R : A → A → Prop) (x : A) : A → Prop
  | refl {} : RTclosure x
  | step {} : ∀ {y z : A}, R y z → RTclosure y → RTclosure z

inductive RTclosure' {A : Type u} (R : A → A → Prop) (x z : A) : Prop
  | refl {} : x = z → RTclosure'
  | step {} : ∀ {y : A}, R y z → RTclosure R x y → RTclosure'

namespace RTclosure

def stepL {A : Type u} {R : A → A → Prop} {x y : A} (r : R x y)
  : ∀ {z : A}, RTclosure R y z → RTclosure R x z
:= begin
intros z s, induction s, apply step, assumption, apply refl,
apply step; assumption,
end

def invert {A : Type u} {R : A → A → Prop} {x z : A}
  (r : RTclosure R x z) :
  RTclosure' R x z
:= begin
induction r, left, reflexivity,
right, assumption, assumption
end

end RTclosure

namespace network

open temporal

section
parameter {agents : map ip agent}

instance decidable_agent_does (a_ip : ip) P
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
       (Hagl : next_agent_state_from_label ag.key ag.value ((s.global_state ag.key)) (s.local_state ag) la = some (next', updatef))
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
  : sigma (λ _ : system_state, next_state_label) → Prop
  := inState (λ s, P (s.local_state a))


lemma return_implies_starts_loop_ltl (a : agents.member) :
 ⊩ valid_trace LTS 
   => □ (now (inLabel (agent_does a.key (eq agent_label.update_own_state)))
         => ◯ (now (inLocalState a starts_loop)))
:= begin
apply prove_always,
intros, apply return_implies_starts_loop; assumption,
end

/-- It feels like it should be possible to auto-generate something like
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

/-- Indeed, this relation is well-founded -/
lemma strictly_smaller_wf {A : Type u} : well_founded (@strictly_smaller A)
:= begin
constructor,
intros x, induction x; constructor; intros,
{ cases a_1, },
{ cases a_2, subst y, apply ih_1 },
{ cases a_3, subst y, apply ih_1 },
{ cases a_1, subst y, apply ih_1 }
end

def may_step_to {A : Type u} (x y : act A) := RTclosure strictly_smaller y x

def may_step_to_bind_ty {A : Type u} (f : A → act A)
  (z : act A) : act A → Prop
| (act.return x) := may_step_to (f x) z
| (act.connect rn cont) := ∃ sock, may_step_to (cont sock) z
| (act.send_message rn mess cont) := may_step_to cont z
| (act.poll ports sockets bound cont) :=
   ∃ result, may_step_to (cont result) z

def may_step_to_bind {A : Type u} (x : act A) (f : A → act A)
  (z : act A)
  (H : may_step_to (x >>= f) z)
  : z = (x >>= f) ∨ may_step_to_bind_ty f z x
:= begin
apply_in H RTclosure.invert,
induction H with H y H H',
{ left, assumption },
{ right,
induction x; simp [may_step_to_bind_ty];
  simp [bind, act_bind] at H,
{
constructor; assumption,
},
{ admit },
{ admit },
{ admit },
}
end

inductive has_state {a : agent} (P : a.state_type → Prop) (z : act a.state_type) : Prop
| mk : ∀ (st : a.state_type), P st → may_step_to (a.loop st) z → has_state

lemma return_update_own_state
  {ag : agents.member}
  (a_next : act ag.value.state_type)
  (la : agent_label)
  {s : @system_state agents}
  ans
  (H : next_agent_state_from_label ag.key ag.value
        (s.global_state ag.key) a_next la = some ans)
  : (match a_next with 
  | act.return x := la = agent_label.update_own_state
  | _ := true
  end : Prop)
:= begin
induction la;
  simp [next_agent_state_from_label] at H;
  induction a_next;
  try { trivial <|> contradiction },
dsimp, reflexivity
end

/-- When an agent takes a step, if the code it had to run was an
    `act.return`, it returns to the top of its loop, and otherwise,
    it "proceeds" down its current code, that is, its new state for the
    code it will run is strictly smaller than it just was, since we're
    using the continuation-passing representation.
-/
lemma size_decreases {ag : agents.member}
  {la : agent_label}
  {next' : act ag.value.state_type}
  {updatef : global_state_t → global_state_t}
  {s : @system_state agents}
  {a_next : act ag.value.state_type}
  (H : next_agent_state_from_label ag.key ag.value
        (s.global_state ag.key) a_next la = some (next', updatef))
  : (match a_next with 
  | act.return x := la = agent_label.update_own_state ∧ next' = ag.value.loop x
  | _ := strictly_smaller next' a_next
  end : Prop)
  := begin
rename H H', have H := H',
apply_in H label_dlabel_equiv,
induction H with la H,
induction la; dsimp [next_agent_state_from_dlabel] at H;
  dsimp,
{ injection H with H', clear H,
  split, apply (return_update_own_state (act.return new_state)),
  assumption,
  symmetry, assumption },
{ injection H with H', clear H,
  apply strictly_smaller.connect, assumption
},
{ injection H with H',
  clear H, apply strictly_smaller.send_message, assumption
},
{ induction a; dsimp at H,
  { injection H with H H', subst next',
  apply strictly_smaller.poll, reflexivity, },
  { induction a; 
        dsimp at H,
      { -- new connection
        injection H with H1 H2, clear H, subst next',
        constructor, reflexivity,
      },
      { -- new message
        injection H with H1 H2, clear H, subst next',
        constructor, reflexivity,
      }
  }
}
end

lemma size_decreases' {ag : agents.member}
  {la : agent_label}
  {next' : act ag.value.state_type}
  {updatef : global_state_t → global_state_t}
  {s : system_state}
  (H : next_agent_state_from_label ag.key ag.value
        (s.global_state ag.key) (s.local_state ag) la = some (next', updatef))
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
apply (invariant_holds_while LTS _ (delayn n tr)),
apply valid_trace_always, assumption, assumption,
apply_instance,
intros,
have H := local_state_stays_constant _ a_1 a_2,
rw ← H, assumption,
end

lemma size_decreases_label : ∀ 
  {a : mapd.member agents}
  {ss ss' : system_state}
  {l : next_state_label}
  (HLTS : LTS ss l ss')
  (nogo : ¬ (agent_does (a.key) (eq agent_label.update_own_state)) l)
  (H : agent_does (a.key) (λ (_x : agent_label), true) l)
  , strictly_smaller (ss'.local_state a) (ss.local_state a)
:= begin
intros,
apply_in H agent_does_invert,
induction H with la Hla, induction Hla with tt Hla,
clear tt, subst l,
apply_in HLTS agent_update_invert_st',
induction HLTS,
have H' := size_decreases' Hagl,
induction H',
{ subst ss', dsimp, rw lookup_update_refl, assumption },
{ induction a_1 with H1 H2, subst la,
  exfalso, apply nogo, constructor, reflexivity }
end

lemma stuck_in_loop_iter {a : agents.member}
  (s : act a.value.state_type)
  : ⊩ valid_trace LTS
   => now (inLocalState a (may_step_to s))
   => (◯ (now (inLocalState a (may_step_to s)))
     𝓦
     now (inLabel (agent_does a.key (eq agent_label.update_own_state))))
:= begin
intros tr valid now,
apply invariant_holds_while; try { assumption },
intros ss l ss' HLTS nogo,
unfold may_step_to,
have H := decide (agent_does a.key (λ _, true) l), 
induction H with H H,
{ have H := local_state_stays_constant _ HLTS H,
  rw H, intros x, assumption
},
{ apply (RTclosure.stepL _),
  apply (size_decreases_label HLTS nogo H),
}
end

lemma starts_loop_union {a : agents.member}
  : now (inLocalState a starts_loop)
  = subset.union_ix (λ z : a.value.state_type, 
     now (inLocalState a (eq (a.value.loop z))))
:= begin
rw ← now_cocontinuous, f_equal,
apply funext, intros x,
unfold inLocalState inState,
unfold starts_loop,
apply propext, split; intros H; induction H,
constructor, trivial, unfold inState, symmetry, assumption,
constructor, symmetry, assumption,
end

/-- Once an agent hits the start of its loop,
    it will always be in some code "descended" from
    its loop.

   High-level description: use next_weak_until_always_loop
   with lemmas:
   stuck_in_loop_iter
   return_implies_starts_loop_ltl
-/
lemma stuck_in_loop {a : agents.member}
  : ⊩ valid_trace LTS
   => now (inLocalState a starts_loop)
   => □ (subset.union_ix (λ z, 
      (now (inLocalState a (may_step_to (a.value.loop z))))))
:= begin
rw starts_loop_union,
intros tr valid now,
apply (next_weak_until_always_loop _ _ _ _ _ _),
tactic.swap, revert now,
apply subset.union_ix_mono,
intros H, apply now_mono, apply inState_mono,
intros x Hx, rw Hx, apply RTclosure.refl,
tactic.swap,
intros n, 
rw next_cocontinuous,
rw subset.tImp_cocontinuous_l,
intros s Hnow,
-- it's not yet in the right shape to apply the below lemma
-- apply stuck_in_loop_iter,
apply weak_until_mono, tactic.swap,
apply stuck_in_loop_iter,
apply valid_trace_always, assumption,
assumption, intros x Hx,
constructor, trivial, assumption,
tactic.swap,
intros n HP,
apply (@next_mono _ (temporal.now (inLocalState a starts_loop)) _ _ _ _),
rw starts_loop_union,
apply subset.union_ix_mono, intros ix,
apply now_mono, apply inState_mono,
intros x Hx, rw Hx, apply RTclosure.refl,
apply return_implies_starts_loop_ltl,
assumption, apply HP
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
  = λ s, (λ s' : sigma (λ _ : system_state, next_state_label), s'.fst.local_state a) s = ag_next
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
parameters {agents : map ip agent}
  (a : agents.member)
  (P : poll_receive_label → Prop)

lemma blocks_until_not_never_receives_always_polls
  : ⊩ valid_trace (@LTS agents)
    => (◇ (now (inLabel (agent_does a.key polls))) 
        𝓦 (now (inLabel (agent_does a.key (receives P)))))
    => □ (tNot (now (inLabel (agent_does a.key (receives P)))))
    => fair (now (inLabel (agent_does a.key polls)))
:= begin
intros tr valid nows never,
apply weak_until_not_always; assumption,
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
theorem blocking_agent_eventually_receives_message
  : ⊩ valid_trace (@LTS agents)
    => fairness_spec
    => message_fairness_spec
    => (◇ (now (inLabel (agent_does a.key polls))) 
        𝓦 (now (inLabel (agent_does a.key (receives P)))))
    => now (inState (λ ss : system_state, ∃ mess : socket × message_t,
         P (poll_receive_label.receive_message mess.snd) ∧
         mess ∈ (ss.global_state a.key).messages))
    => ◇ (now (inLabel (agent_does a.key (receives P))))
:= begin
intros tr valid fair mfair nowstate H,
apply classical.not_always_not_implies_eventually,
intros contra,
have H' := blocks_until_not_never_receives_always_polls 
  _ _ _ valid nowstate contra,
induction H with mess Hmess,
induction Hmess with Hmess1 Hmess2,
specialize (mfair a mess H'),
rw ← (delayn_zero tr) at Hmess2,
specialize (mfair 0 Hmess2),
rw ← not_eventually_always_not at contra,
apply contra,
revert mfair, rw delayn_zero,
apply eventually_mono,
intros x H,
unfold now later inLabel at H,
unfold now later inLabel,
apply_in H agent_does_invert,
induction H with la Hla,
induction Hla with Hlal Hlar,
rw Hlar,
constructor,
induction Hlal,
constructor, rw ← a_1, assumption
end

end

end network