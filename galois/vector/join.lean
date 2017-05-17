import galois.vector.basic
import galois.list.taken_dropn_lemmas

universe variables u

namespace vector

variables {α : Type u}
variable {m : ℕ}
variable {n : ℕ}

definition join_list : list (vector α m) → list α
| list.nil := list.nil
| (list.cons a v) := list.append (to_list a) (join_list v)

theorem length_join_list : ∀ (l : list (vector α m)), list.length (join_list l) = m * list.length l
| list.nil := rfl
| (list.cons a v) := calc
  list.length (list.append (to_list a) (join_list v))
        = list.length (to_list a) + list.length (join_list v) : list.length_append (to_list a) (join_list v)
    ... = m + list.length (join_list v) : congr_arg (λ i, i + list.length (join_list v)) (length_to_list a)
    ... = m + m * list.length v         : congr_arg (λ i, m + i) (length_join_list v)
    ... = m * list.length v + m         : nat.add_comm _ _

definition join : vector (vector α m) n → vector α (m * n)
| ⟨ l, h ⟩ :=
  let p := calc
     list.length (join_list l)
           = m * list.length l : length_join_list l
       ... = m * n : congr_arg (λ i, m * i) h
  in ⟨ join_list l, p ⟩

lemma to_list_join : ∀(x : vector (vector α m) n), to_list (join x) = join_list (to_list x)
| ⟨ l, h ⟩ := rfl

def take_le (n : ℕ) (l : list α) (p : n ≤ list.length l) : vector α n :=
  ⟨list.taken n l, eq.trans (list.length_taken n l) (min_eq_left p)⟩

lemma to_list_take_le (n : ℕ) (l : list α) (p : n ≤ list.length l) : to_list (take_le n l p) = list.taken n l := rfl

-- 'bounded_chunk_list n m l' splits 'l' into at most 'n' 'm'-element chunks.
definition bounded_chunk_list : Π(n m : ℕ), list α → list (vector α m)
| nat.zero m l := list.nil
| (nat.succ n) m l :=
  if p : list.length l ≥ m then
    list.cons (take_le m l p) (bounded_chunk_list n m (list.dropn m l))
  else
    list.nil

lemma bounded_chunk_list_zero (m : ℕ) (l : list α) : bounded_chunk_list 0 m l = [] := rfl

lemma bounded_chunk_list_succ_next (n m : ℕ) (l : list α) (p : list.length l ≥ m)
: bounded_chunk_list (nat.succ n) m l = list.cons (take_le m l p) (bounded_chunk_list n m (list.dropn m l)) :=
begin
  unfold bounded_chunk_list,
  rw [dif_pos p]
end

lemma length_bounded_chunk_list : ∀(n m : ℕ) (l : list α), (list.length l = m * n) → list.length (bounded_chunk_list n m l) = n
| nat.zero m t  :=
  begin
    intros,
    simp [bounded_chunk_list_zero],
  end
| (nat.succ n) m t :=
  if p : list.length t ≥ m then
    begin
      rw [nat.mul_succ],
      intro h,
      assert q : list.length (list.dropn m t) = m * n,
         { rw [list.length_dropn, h, nat.add_sub_cancel] },
      unfold bounded_chunk_list,
      rw [dif_pos p],
      simp [length_bounded_chunk_list n m _ q, nat.add_succ]
    end
  else
    begin
      simp [nat.mul_succ],
      intro h,
      assert t_ge : list.length t ≥ m,
        { rw [h], apply nat.le_add_right },
      contradiction
    end

definition split_vector {m:ℕ} : Π(n : ℕ), vector α (m * n) → list (vector α m)
| n ⟨ l, p ⟩ := bounded_chunk_list n m l

theorem length_split_vector {m : ℕ} : ∀ (n : ℕ) (t : vector α (m * n)), (split_vector n t)^.length = n
| n ⟨ l, p ⟩ :=
begin
  unfold split_vector,
  simp [length_bounded_chunk_list n m l p]
end

definition split : Π {n : ℕ}, vector α (m * n) → vector (vector α m) n
| n v := ⟨ split_vector n v, length_split_vector n v ⟩

--------------------------------------------------------------------------------
-- Relate join_list and split_list

theorem join_list_of_bounded_chunk_list {α : Type u}
: ∀ (n m) (l : list α) (p : list.length l = m * n), vector.join_list (vector.bounded_chunk_list n m l) = l
| 0 m l :=
begin
  unfold bounded_chunk_list,
  simp [nat.mul_zero],
  intros,
  cases l, refl, contradiction,
end
| (nat.succ n) m l :=
if q : list.length l ≥ m then
begin
  unfold bounded_chunk_list,
  rw [dif_pos q],
  unfold join_list,
  intros,
  assert h : list.length (list.dropn m l) = m * n,
    { rw [list.length_dropn, p, nat.mul_succ,nat.add_sub_cancel]
    },
  simp [join_list_of_bounded_chunk_list _ _ _ h, to_list_take_le],
  exact (list.taken_append_dropn_self m l)
end
else
begin
  rw [nat.mul_succ],
  intro p,
  -- Assert contradiction
  assert t_ge : list.length l ≥ m, { rw p, apply nat.le_add_left },
  contradiction
end

theorem join_list_of_split_list {α : Type u} {m n}
: ∀ (t : vector α (m * n)), join_list (split_vector n t) = t^.to_list
| ⟨l, p⟩ :=
  begin
    unfold split_vector,
    apply join_list_of_bounded_chunk_list,
    exact p
  end

end vector
