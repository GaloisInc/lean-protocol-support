/- Lemmas about nth -/
universe u

namespace list

theorem nth_is_none_bound {α:Type} {l : list α} {i:ℕ} (pr : l.nth i = none)
: i ≥ l.length :=
begin
  revert i,
  induction l,
  case nil { intros i pr, apply nat.zero_le, },
  case cons h r ind {
    intros i pr,
    cases i; simp at pr,
    contradiction,
    exact nat.succ_le_succ (ind pr),
  }
end

theorem nth_is_some_bound {α:Type} {l : list α} {i:ℕ} {e : α}
(pr : l.nth i = some e)
: i < l.length :=
begin
  revert i,
  induction l,
  case nil { intros i pr, simp at pr, contradiction, },
  case cons h r ind {
    intros i pr,
    cases i,
    { apply nat.zero_lt_succ, },
    { apply nat.succ_le_succ (ind pr), }
  }
end

theorem nth_mem {α:Type} {l : list α} {i:ℕ} {e : α}
(pr : l.nth i = some e)
: e ∈ l :=
begin
  revert i,
  induction l,
  case nil { intros i pr, simp at pr, contradiction, },
  case cons h r ind {
    intros i pr,
    cases i; simp at pr,
    case nat.zero {
      simp [option.some.inj pr],
    },
    case nat.succ i {
      exact or.inr (ind pr),
    }
  }
end

lemma nth_mem_len {A} {x : A} {xs : list A}
  (H : x ∈ xs)
  : ∃ n, xs.nth n = some x :=
begin
  induction xs,
  case nil { simp at H, contradiction, },
  case cons h r ind {
    simp at H,
    cases H with here there,
    { apply exists.intro 0,
      simp [here],
    },
    { apply exists.elim (ind there),
      intros n pr,
      constructor,
      change (nth (h :: r) (nat.succ n) = some x),
      exact pr,
    }
  },
end


lemma nth_append_left {α:Type u} {x : α} (xs ys : list α) {i : ℕ}
  (pr : xs.nth i = some x)
  : (xs ++ ys).nth i = some x :=
begin
  revert i,
  induction xs,
  case nil { intros i pr, contradiction, },
  case cons h r ind {
    intros i pr,
    cases i with i,
    { exact pr, },
    { exact ind pr, },
  }
end

end list