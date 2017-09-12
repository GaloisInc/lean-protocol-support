import galois.tactic
       galois.nat.simplify_le

def nat_to_fin_option (k n : ℕ) : option (fin k)
  := if H : n < k then some ⟨ _, H ⟩ else none

namespace fin

lemma fin_0_empty (x : fin 0) : false :=
begin
induction x,
apply nat.lt_irrefl,
apply lt_of_le_of_lt, tactic.swap,
assumption, apply nat.zero_le,
end

lemma val_inj {n : ℕ} (i j : fin n)
  (H : i.val = j.val) : i = j
:= begin
induction i, induction j, dsimp at H, induction H,
reflexivity,
end

lemma succ_pred_id {k : ℕ} (i : fin k.succ)
  (H : i ≠ 0)
  : fin.succ (fin.pred i H) = i
:= begin
induction i,
dsimp [fin.pred, fin.succ],
cases val, exfalso, apply H, unfold has_zero.zero,
dsimp [nat.pred], reflexivity,
end

lemma succ_pred_equiv {k : ℕ} (i : fin k.succ)
  (H : i ≠ 0)
  (n : ℕ)
 : (i.val = nat.succ n) ↔ ((fin.pred i H).val = n)
:= begin
induction i, dsimp [fin.pred],
cases val, exfalso, apply H,
unfold has_zero.zero,
dsimp [nat.pred], split; intros H',
injection H', subst H',
end

end fin

lemma nat_to_fin_option_pred_none {n i : ℕ}
  : nat_to_fin_option n.succ i.succ = none
  → nat_to_fin_option n i = none
:= begin
unfold nat_to_fin_option,
apply (if Hlt : i.succ < n.succ then _ else _),
{ rw (dif_pos Hlt), intros H,
  contradiction,
},
{ rw (dif_neg Hlt), intros H', clear H',
  have H : ¬ (i < n),
  intros contra, apply Hlt,
  apply nat.succ_lt_succ, assumption,
  rw (dif_neg H),
}
end

lemma nat_to_fin_option_succ_nz {n k : ℕ} {i : fin n.succ}
  : nat_to_fin_option n.succ k.succ = some i
  → i ≠ 0
:= begin
dsimp [nat_to_fin_option],
apply (if H : (nat.succ k < nat.succ n) then _ else _),
{ rw (dif_pos H), intros H', injection H' with H'', clear H',
  intros contra, subst i, injection contra,
  injection h,
},
{ rw (dif_neg H), intros contra, contradiction, }
end

lemma nat_to_fin_option_pred_some {n k : ℕ} (i : fin n.succ)
  : ∀ H : nat_to_fin_option n.succ k.succ = some i
  , nat_to_fin_option n k = some (i.pred (nat_to_fin_option_succ_nz H))
:= begin
dsimp [nat_to_fin_option],
intros H,
apply (if H' : (nat.succ k < nat.succ n) then _ else _),
{ rw (dif_pos H') at H, injection H with H2, clear H,
  rw nat.succ_lt_succ_iff at H',
  rename H' H'1,
  rw (dif_pos H'1), f_equal, subst i,
  dsimp [fin.pred], reflexivity,
},
{ rw (dif_neg H') at H, contradiction, }
end

lemma nat_to_fin_option_val {n k : ℕ} {i : fin n}
  (H : nat_to_fin_option n k = some i)
  : i.val = k
:= begin
dsimp [nat_to_fin_option] at H,
apply (if H' : k < n then _ else _),
{ rw (dif_pos H') at H, injection H with H2,
  clear H, subst i,
},
{ rw (dif_neg H') at H, contradiction }
end