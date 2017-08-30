/-
This modules defines a type for representing integers modulo a natural number n,
along with the standard commutative ring operations.

The representation uses a canonical form of numbers between 0 and n-1.  Operations
preserve the canonical form.
-/
import galois.nat.div_lemmas

def intmod (n:ℕ) := { x : ℕ // x < n }

namespace intmod

open nat

variable {n : nat}

def of_nat (x:ℕ) : intmod (succ n) :=
 ⟨ x % succ n, nat.mod_lt x (nat.zero_lt_succ _) ⟩

private lemma mlt {b : nat} : ∀ {a}, n > a → b % n < n
| 0     h := nat.mod_lt _ h
| (a+1) h :=
  have n > 0, from lt.trans (nat.zero_lt_succ _) h,
  nat.mod_lt _ this

def zero : intmod (succ n) := ⟨ 0, nat.succ_pos n ⟩
def one  : intmod (succ n) := of_nat 1
def add  : intmod n → intmod n → intmod n
| ⟨x,x_lt⟩ ⟨y,y_lt⟩ :=
  if p:x+y < n then
    ⟨x+y, p⟩
  else
    let q : (x+y)-n < n :=
         begin
           simp [nat.sub_lt_iff],
           have xy_lt_nn : x + y < n + n := add_lt_add x_lt y_lt,
           have n_le_xy  : n ≤ x + y := le_of_not_gt p,
           cc,
         end in
    ⟨ (x+y)-n, q⟩

def neg  : intmod n → intmod n
| ⟨x,p⟩ :=
  let r := if x = 0 then 0 else n-x in
  let q : (if x = 0 then 0 else n-x) < n :=
    begin
      by_cases x = 0,
      { simp [h],
        simp [h] at p,
        exact p,
      },
      {
        -- Show x > 0
        have x_pos := nat.eq_zero_or_pos x,
        simp [h] at x_pos,
        -- show n - x < n
        simp [h, nat.sub_lt_iff],
        -- Decompose and
        constructor,
        -- n < n + x
        exact lt_add_of_le_of_pos (le_refl n) x_pos,
        -- show 0 < n
        exact or.inr (lt_trans x_pos p),
      }
    end in
  ⟨r, q ⟩

def sub  : intmod n → intmod n → intmod n
| ⟨x,h⟩ ⟨y,y_lt⟩ :=
  if p : y ≤ x then
    let q : x - y < n :=
      begin
        apply nat.lt_of_le_of_lt,
        apply nat.sub_le,
        exact h,
      end in
    ⟨ x-y, q ⟩
  else
    let q : x + n - y < n :=
          begin
            --have p : x < y := sorry,
            simp [nat.sub_lt_iff],
            constructor,
            { apply add_lt_add_left,
              -- Enforce h := x < y
              exact lt_of_not_ge p,
            },
            { -- Pick right branch to prove y ≤ n + x
              apply or.inr,
              transitivity,
              exact nat.le_of_lt y_lt,
              apply nat.le_add_right,
            }
          end  in
    ⟨ x+n-y, q ⟩

def mul : intmod n → intmod n → intmod n
| ⟨x,h⟩ ⟨y,_⟩ := ⟨(x*y)%n, mlt h ⟩

instance (n:ℕ) : has_zero (intmod (succ n)) := ⟨ zero ⟩
instance (n:ℕ) : has_one  (intmod (succ n)) := ⟨ one ⟩
instance (n:ℕ) : has_add  (intmod n) := ⟨ add ⟩
instance (n:ℕ) : has_neg  (intmod n) := ⟨ neg ⟩
instance (n:ℕ) : has_sub  (intmod n) := ⟨ sub ⟩
instance (n:ℕ) : has_mul  (intmod n) := ⟨ mul ⟩

theorem zero_val (n : ℕ) : (0 : intmod (succ n)).val = 0 := rfl

theorem one_val (n : ℕ) : (1 : intmod (succ n)).val = 1 % succ n := rfl

theorem add_val (x y : intmod n) : (x + y).val = (x.val + y.val) % n :=
begin
  cases x with xv x_lt,
  cases y with yv y_lt,
  transitivity,
  unfold has_add.add,
  by_cases (xv + yv < n) with p,
  {
    simp [add, p, nat.mod_eq_of_lt],
  },
  {
    -- Show xv + yv ≥ n
    have q : xv + yv ≥ n :=
      or.resolve_left (nat.lt_or_ge (xv + yv) n) p,
    have r : (xv + yv - n) < n,
    { simp [nat.sub_lt_iff],
      constructor,
      {
        transitivity,
        exact nat.add_lt_add_left  y_lt _,
        exact nat.add_lt_add_right x_lt _,
      },
      -- Show n ≤ x + y
      exact or.inr q,
    },
    simp [add, mod_eq_sub_mod,  mod_eq_of_lt, *],
  },
end

theorem mul_val (x y : intmod n) : (x * y).val = (x.val * y.val) % n :=
begin
  cases x with xv xp,
  cases y with yv yp,
  refl,
end

theorem zero_add (x : intmod (succ n)) : 0 + x = x :=
begin
  apply subtype.eq,
  simp [add_val, zero_val],
  exact nat.mod_eq_of_lt x.property,
end

theorem add_zero (x : intmod (succ n)) : x + 0 = x :=
begin
  apply subtype.eq,
  simp [add_val, zero_val],
  exact nat.mod_eq_of_lt x.property,
end

theorem add_assoc (x y z : intmod n) : (x + y) + z = x + (y + z) :=
begin
  apply subtype.eq,
  simp [add_val, nat.mod_add_right_mod],
end

theorem add_comm (x y : intmod n) : x + y = y + x :=
begin
  apply subtype.eq,
  simp [add_val],
end

 theorem add_left_neg (x : intmod (succ n)) : -x + x = 0 :=
 begin
   cases x with xv x_lt,

   apply subtype.eq,
   simp [add_val, has_neg.neg, neg],
   by_cases (xv = 0) with h,
   {
      simp [h, zero_val],
   },
   {
     have x_le : xv ≤ succ n := nat.le_of_lt x_lt,
     simp only [h, if_false, nat.add_comm xv, ge, *, nat.sub_add_cancel],
     simp [nat.mod_eq_sub_mod, zero_val],
   }
 end

theorem one_mul (x : intmod (succ n)) : 1 * x = x :=
begin
  apply subtype.eq,
  simp [mul_val, one_val, nat.mod_mul_left_mod, nat.mod_mul_right_mod],
  exact nat.mod_eq_of_lt x.property,
end

theorem mul_one (x : intmod (succ n)) : x * 1 = x :=
begin
  apply subtype.eq,
  simp [mul_val, one_val, nat.mod_mul_left_mod, nat.mod_mul_right_mod],
  exact nat.mod_eq_of_lt x.property,
end

theorem mul_assoc (x y z : intmod n) : (x * y) * z = x * (y * z) :=
begin
  apply subtype.eq,
  simp [mul_val, nat.mod_mul_right_mod],
end

theorem mul_comm (x y : intmod n) : x * y = y * x :=
begin
  apply subtype.eq,
  simp [mul_val],
end

theorem left_distrib (a b c : intmod n)
: a * (b + c) = a * b + a * c :=
begin
  apply subtype.eq,
  simp [add_val, mul_val],
  simp [nat.mod_add_right_mod,
        nat.mod_mul_right_mod,
        nat.left_distrib],
end

theorem right_distrib (a b c : intmod n)
: (a + b) * c = a * c + b * c :=
begin
  simp only [mul_comm _ c, left_distrib],
end

instance (n:ℕ) : comm_ring (intmod (succ n)) :=
{ zero := 0
, one  := 1
, add := add
, neg := neg
, mul := mul
, zero_add := zero_add
, add_zero := add_zero
, add_assoc := add_assoc
, add_comm  := add_comm
, add_left_neg := add_left_neg
, one_mul   := one_mul
, mul_one   := mul_one
, mul_assoc := mul_assoc
, mul_comm  := mul_comm
, left_distrib  := left_distrib
, right_distrib := right_distrib
}

end intmod
