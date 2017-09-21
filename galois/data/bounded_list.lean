import galois.tactic

universe variables u v

def bounded_list (α : Type u) (n : ℕ) := { l : list α // l.length ≤ n }

namespace bounded_list

/-- Two bounded_lists are equal if the underlying lists are equal. -/
theorem eq (α : Type u) (n : ℕ)
: ∀ {t₀ t₁ : bounded_list α n}, t₀^.val = t₁^.val → t₀ = t₁
| ⟨l, p₀⟩ ⟨.(l), p₁⟩ rfl := rfl

/-- Return tt if a bounded list is not empty. -/
@[reducible]
def empty {α : Type u} {n : ℕ} (l : bounded_list α n) : bool := l.val.empty

/-- Return singleton bounded_list -/
def single {α : Type u} (x : α) : bounded_list α 1 := ⟨[x], dec_trivial⟩

-- Empty bounded_list
def nil {α : Type u} : bounded_list α 0 := ⟨ [], dec_trivial ⟩

-- Prepend an element to a bounded list.
def cons {α : Type u} {n : ℕ} (x : α) :  bounded_list α n → bounded_list α (n+1)
| ⟨l, p⟩ :=
  let q : (l.cons x).length ≤ n+1 :=
      begin
        simp [nat.add_succ],
        apply nat.succ_le_succ,
        exact p,
      end in
  ⟨ l.cons x, q ⟩

-- A bounded_list of length n can be extended to a list of length n + k
def extend {α : Type u} {n : ℕ} : bounded_list α n → Π (k : ℕ), bounded_list α (n + k)
| ⟨l, p⟩ k := ⟨ l, le_trans p (nat.le_add_right n k) ⟩

-- Map over elements in a list.
def map {α β : Type u} {n : ℕ} (f : α → β) : bounded_list α n → bounded_list β n
| ⟨l, p⟩ := ⟨ l.map f, begin simp [list.length_map], exact p, end⟩

def append {A : Type u} {n m : ℕ} :
  bounded_list A n → bounded_list A m → bounded_list A (n + m)
 | ⟨ xs, pxs ⟩ ⟨ ys, pys ⟩ := ⟨ xs ++ ys,
   begin
   rw list.length_append, apply add_le_add; assumption
   end ⟩

inductive length_succ_cons_ind {A : Type u} (xs : list A) (n : ℕ) : Prop
  | smaller : xs.length ≤ n → length_succ_cons_ind
  | same : ∀ (x : A) (xs' : list A), xs = x :: xs' → xs'.length = n → length_succ_cons_ind

lemma list.length_le_zero_nil {A : Type u} {xs : list A}
  (H : xs.length ≤ 0) : xs = list.nil
:= begin
apply list.eq_nil_of_length_eq_zero,
apply nat.eq_zero_of_le_zero, assumption,
end

lemma length_succ_cons {A : Type u} {xs : list A}
  {n : ℕ} (H : xs.length ≤ n.succ)
  : length_succ_cons_ind xs n
:= begin
rw le_iff_lt_or_eq at H, induction H with H H,
{ apply_in H  nat.le_of_lt_succ,
  apply length_succ_cons_ind.smaller, assumption
},
{ cases xs, try { contradiction },
  apply length_succ_cons_ind.same, reflexivity,
  dsimp at H, injection H,
}
end

/-- Given a list and a bound this returns a bounded list if the length is small enough. œ-/
def of_list {α : Type u} (l : list α) (m : ℕ )
: option (bounded_list α m) :=
  if p : l.length ≤ m then
    option.some (⟨l, p⟩)
  else
    option.none

/-- Concatenate a bounded list of bounded lists all together. -/
lemma concat {A : Type u} {n m : ℕ}
  : bounded_list (bounded_list A m) n → bounded_list A (m * n)
| ⟨ xss, pxss ⟩ := ⟨ (xss.map subtype.val).join , begin
  clear concat,
  revert xss, induction n; intros,
  {
  apply_in pxss list.length_le_zero_nil,
  subst xss, simp [list.join],
  },
  { apply_in pxss length_succ_cons, induction pxss,
    { specialize (ih_1 _ a_1),
      apply le_trans, assumption,
      apply nat.mul_le_mul_left,
      apply nat.le_succ,
    },
    { subst xss, dsimp [list.map, list.join],
      rw list.length_append,
      rw nat.mul_succ, rw nat.add_comm,
      apply add_le_add, apply ih_1, subst a,
      apply x.property,
    }
  }
  end ⟩

end bounded_list
