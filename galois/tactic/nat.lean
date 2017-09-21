import galois.nat.simplify_le

namespace galois.tactic.nat

open nat
open tactic

local attribute [simp]  nat.succ_le_succ_iff
local attribute [simp]  nat.not_succ_le_zero

theorem one_add_bit1 (x : ℕ) : 1 + bit1 x = bit0 (1 + x) :=
begin
  cases x,
  { simp, },
  { simp [succ_add, bit1, bit0], },
end

theorem bit0_add_one (x : ℕ) : bit0 x + 1 = bit1 x :=
begin
  simp [bit1],
end

theorem bit0_add_bit0 (x y : ℕ) : bit0 x + bit0 y = bit0 (x + y) :=
begin
  cases x,
  { simp [bit0], },
  { simp [succ_add, add_succ, bit0], },
end

theorem bit1_add_one (x : ℕ) : bit1 x + 1 = bit0 (x + 1) :=
begin
  cases x,
  { simp [bit0, bit1], },
  { simp [succ_add, add_succ, bit1, bit0], },
end

theorem bit1_add_bit1 (x y : ℕ) : bit1 x + bit1 y = bit0 (x + y + 1) :=
begin
  cases x,
  { simp [bit0, bit1], },
  { simp [succ_add, add_succ, bit1, bit0], },
end

theorem one_le_bit0 (x : ℕ) : (1 ≤ bit0 x) ↔ (1 ≤ x) :=
begin
  cases x,
  { simp [bit0], },
  { simp [bit0, zero_le], },
end

theorem one_le_bit1 (x : ℕ) : (1 ≤ bit1 x) ↔ true :=
begin
  cases x,
  { simp [bit0], },
  { simp [bit0, bit1, add_succ, zero_le], },
end

theorem bit0_le_bit0 (x y : ℕ) : (bit0 x ≤ bit0 y) ↔ (x ≤ y) :=
begin
  revert y,
  induction x with x ind,
  { simp [zero_le], },
  { intro y,
    cases y with y,
    { simp [bit0, succ_add, not_succ_le_zero], },
    { simp [bit0, succ_add, add_succ],
      simp [bit0] at ind,
      apply ind,
    },
  },
end

theorem bit0_le_bit1 (x y : ℕ) : (bit0 x ≤ bit1 y) ↔ (x ≤ y) :=
begin
  revert y,
  induction x with x ind,
  { simp [zero_le], },
  { intro y,
    cases y with y,
    { simp [bit0, bit1, add_succ ], },
    { simp [bit0, bit1, add_succ, succ_add],
      simp [bit0, bit1, add_succ] at ind,
      apply ind,
    }
  },
end

theorem bit1_le_bit0 (x y : ℕ) : (bit1 x ≤ bit0 y) ↔ (x + 1 ≤ y) :=
begin
  revert y,
  induction x with x ind,
  { intro y,
    cases y with y,
    { simp [bit1, bit0], },
    { simp [bit1, bit0, zero_le], },
  },
  { intro y,
    cases y with y,
    { simp [bit0, bit1, add_succ], },
    { simp [bit0, bit1, add_succ, succ_add],
      simp [bit0, bit1, add_succ] at ind,
      apply ind,
    },
  },
end

theorem bit1_le_bit1 (x y : ℕ) : (bit1 x ≤ bit1 y) ↔ (x ≤ y) :=
begin
  revert y,
  induction x with x ind,
  { simp [zero_le, bit1, bit0, add_succ], },
  { intro y,
    cases y with y,
    { simp [bit0, bit1, add_succ], },
    { simp [bit0, bit1, add_succ, succ_add],
      simp [bit0, bit1, add_succ] at ind,
      apply ind,
    }
  },
end

meta def nat_lit_le : tactic unit := do
  let lemmas : list expr :=
    [ expr.const `norm_num.bin_zero_add [level.zero]

    , expr.const `norm_num.one_add_one  [level.zero]
    , expr.const `norm_num.one_add_bit0 [level.zero]
    , expr.const `galois.tactic.nat.one_add_bit1 []

    , expr.const `galois.tactic.nat.bit0_add_one []
    , expr.const `galois.tactic.nat.bit0_add_bit0 []
    , expr.const `norm_num.bit0_add_bit1 [level.zero]

    , expr.const `galois.tactic.nat.bit1_add_one []
    , expr.const `norm_num.bit1_add_bit0 [level.zero]
    , expr.const `galois.tactic.nat.bit1_add_bit1 []

    , expr.const `norm_num.mul_zero [level.zero]
    , expr.const `norm_num.mul_one  [level.zero]
    , expr.const `norm_num.mul_bit0 [level.zero]
    , expr.const `norm_num.mul_bit1 [level.zero]

    , expr.const `nat.zero_le []
    , expr.const `nat.le_refl []
    , expr.const `galois.tactic.nat.one_le_bit0 []
    , expr.const `galois.tactic.nat.one_le_bit1 []
    , expr.const `galois.tactic.nat.bit0_le_bit0 []
    , expr.const `galois.tactic.nat.bit0_le_bit1 []
    , expr.const `galois.tactic.nat.bit1_le_bit0 []
    , expr.const `galois.tactic.nat.bit1_le_bit1 []
    ] in do
  s ← simp_lemmas.mk_default,
  s ← s.append lemmas,
  tactic.simp_target s,
  try tactic.triv

open tactic
open monad

end galois.tactic.nat
