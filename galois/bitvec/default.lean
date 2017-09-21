import .simplify_eq
import galois.list
import galois.nat

namespace bitvec

-- Unsigned extension
def uext {m :ℕ } (x:bitvec m) (n:ℕ) (pr : m ≤ n) : bitvec n :=
  let q : n - m + m = n := nat.sub_add_cancel pr in
  bitvec.cong q (bitvec.append (bitvec.zero (n-m)) x)

-- Return all bitvectors with a given size.
def all : Π(k:ℕ), list (bitvec k)
| 0 := [bitvec.zero 0]
| (nat.succ k)
   := list.map (vector.cons ff) (all k)
   ++ list.map (vector.cons tt) (all k)

protected def to_string {n : nat} (x : bitvec n) : string := has_to_string.to_string x.to_nat

instance (n : nat) : has_to_string (bitvec n) := ⟨bitvec.to_string⟩

-- Return the maximum unsigned number.
def max_unsigned : ℕ → ℕ
| 0 := 0
| (nat.succ x) := 2 * max_unsigned x + 1

-- Lemma about upper bounds of bits_to_nat
lemma bits_to_nat_upper_bound (v : list bool) : bits_to_nat v ≤ max_unsigned (list.length v) :=
-- Show 'cond e 1 0' is at most 1.
let cond_le : Π (e : bool), cond e 1 0 ≤ 1 := λe,
      match e with
      | bool.tt := nat.le_refl _
      | bool.ff := nat.zero_le _
      end in
begin
  unfold bits_to_nat,
  -- Induct over the structure of foldl
  apply (list.foldl_rec (λl r, r ≤ max_unsigned (list.length l))),
  { intros l t e p,
    unfold add_lsb,
    -- Replace cond e 1 0 with 1
    transitivity,
    {  apply add_le_add_left,
       apply (cond_le e)
    },
    -- Simplify to recursive case
    simp [nat.add_succ, max_unsigned, add_lsb, nat.mul_succ],
    apply nat.succ_le_succ,
    apply nat.add_le_add_both,
    all_goals { exact p },
  },
  { exact dec_trivial,
  }
end

-- Upper bounds of bitvec.to_nat
theorem to_nat_upper_bound {n : ℕ} : ∀(x : bitvec n), bitvec.to_nat x ≤ max_unsigned n
| ⟨ x, p ⟩ :=
begin
  simp [eq.symm p],
  apply bitvec.bits_to_nat_upper_bound
end

-- Show that prepending zero to a number does not change it.
theorem to_nat_append_zero  (m : ℕ) {n : ℕ} (k : bitvec n)
: bitvec.to_nat (bitvec.append (0 : bitvec m) k) = bitvec.to_nat k :=
begin
  cases k,
  induction m with m ind,
  refl,
  {
    revert ind,
    simp [ bitvec.zero, bitvec.append],
    simp [vector.repeat, vector.append, bitvec.to_nat],
    simp [ bits_to_nat, list.foldl, add_lsb],
    exact id,
  }
end

end bitvec
