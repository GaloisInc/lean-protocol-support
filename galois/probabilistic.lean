/-
This module is the start for defining core concepts needed to talk about
security proofs of cryptographic processes.  At the moment, it is a fairly
empty skeleton.  I expect more will be needed.

Here are a list of the main concepts that we will need:

"Probability" : A function from some finite domain to rational numbers.  The sum should add up to one.

"Negligible function" : We'll need to define this concept, then prove various
operators involving negligible functions (e.g., the sum of two negligible functions
is negligible).

Univariate polynomial:

Polynomial-bounded Probablistic Process: Need an instruction set.

Notion of a "efficient computation":
- Maybe just a family of arithmetic circuits with a polynomial size.

The plan for this work is to create placeholder operations needed to formalize the
security model presented in Alex's paper and/or the Guardtime papers:

Security Proofs for the BLT Signature Scheme
http://eprint.iacr.org/2014/696

Efficient Record-Level Keyless Signatures for Audit Logs
https://eprint.iacr.org/2014/552.pdf
-/

import galois.bitvec
import galois.nat
import galois.rat

instance : has_to_string ℚ :=
⟨ λx, "rat" ⟩

namespace rat

lemma nz_mul {p q : ℚ} (p_nz : p ≠ 0) (q_nz :q ≠ 0) : p * q ≠ 0 := sorry

end rat

universe variables u v

def algebra.sum {α : Type u} [has_zero α] [has_add α] : list α → α
| [] := 0
| (x::l) := x + algebra.sum l

------------------------------------------------------------------------
-- univariate_poly

inductive univariate_poly.ne_poly (α : Type) [has_zero α]
| last : Π (r : α), r ≠ 0 → univariate_poly.ne_poly
| cons : α → univariate_poly.ne_poly → univariate_poly.ne_poly

-- A univariate polynomial
inductive univariate_poly (α : Type) [has_zero α]
| zero {} : univariate_poly
| nonzero : ne_poly α → univariate_poly


namespace univariate_poly


-- This returns the polynomial denoting a constant
def cns {α : Type} [has_zero α] [decidable_eq α] (x : α) : univariate_poly α :=
  if pr : x = 0 then
    zero
  else
    nonzero (ne_poly.last x pr)

def one {α : Type} [has_zero α] [has_one α] [decidable_eq α] : univariate_poly α := cns 1

def cons {α : Type} [has_zero α] [decidable_eq α] : α → univariate_poly α → univariate_poly α
| c zero := cns c
| c (nonzero p) :=
  nonzero (ne_poly.cons c p)

-- The free variable in the polynomial
def x {α : Type} [has_zero α] [has_one α] [decidable_eq α] : univariate_poly α := cons 0 one

section eval

variable {α : Type}
variables [has_zero α] [has_add α] [has_mul α]

def ne_eval  (x : α) : ne_poly α → α
| (ne_poly.last r pr) := r
| (ne_poly.cons c p) := c + ne_eval p * x

def eval (x : α) : univariate_poly α → α
| zero := 0
| (nonzero p) := ne_eval x p

end eval

section arith

variable {α : Type}
variable [semiring α]
variable [decidable_eq α]

def ne_add : ne_poly α → ne_poly α → univariate_poly α
| (ne_poly.last x _)   (ne_poly.last y _)   := cns (x + y)
| (ne_poly.last x _)   (ne_poly.cons yc yr) := nonzero (ne_poly.cons (x + yc) yr)
| (ne_poly.cons xc xr) (ne_poly.last y _)   := nonzero (ne_poly.cons (xc + y) xr)
| (ne_poly.cons xc xr) (ne_poly.cons yc yr) := cons (xc + yc) (ne_add xr yr)

def add : univariate_poly α → univariate_poly α → univariate_poly α
| zero y := y
| (nonzero x) zero := (nonzero x)
| (nonzero x) (nonzero y) := ne_add x y

instance : has_zero (univariate_poly α) := ⟨ zero ⟩
instance : has_one  (univariate_poly α) := ⟨ one ⟩
instance : has_add  (univariate_poly α) := ⟨ add ⟩

-- Multipy a non-empty polynomial by a constant
def ne_cmul (c : α) : ne_poly α → univariate_poly α
| (ne_poly.last d pr) := cns (c * d)
| (ne_poly.cons d p)  := cons (c * d) (ne_cmul p)

def cmul (c : α) : univariate_poly α → univariate_poly α
| zero  := zero
| (nonzero x)  := ne_cmul c x

def ne_mul : ne_poly α → univariate_poly α → univariate_poly α
| (ne_poly.last x xnz) y := cmul x y
| (ne_poly.cons c r) y := cmul c y + cons 0 (ne_mul r y)

def mul : univariate_poly α → univariate_poly α → univariate_poly α
| zero y := zero
| (nonzero x) y := ne_mul x y

end arith

section to_string

parameter {α : Type}
parameter [has_zero α]
parameter [has_to_string α]

-- `ne_to_string n p` prints out the polynomial "p × x^n" in normalized form.
def ne_to_string : ℕ → ne_poly α → string
| n (ne_poly.last r pr) := to_string r ++ " x^" ++ to_string n
| n (ne_poly.cons c p) := ne_to_string (n + 1) p ++ " + " ++ to_string c ++ "⬝x^" ++ to_string n

def to_string : univariate_poly α → string
| zero := "0"
| (nonzero p) := ne_to_string 0 p

instance : has_to_string (univariate_poly α) := ⟨ to_string ⟩

end to_string

end univariate_poly

--#eval (2 : poly) + poly.x

------------------------------------------------------------------------
-- negligible function

-- This is a function with decreases to 0.
--
-- It essentially says that μ approaches 0 super exponentially fast.
def negligible_function :=
  { μ : ℕ → ℚ
  // ∀(c : ℕ), ∃(n0 : ℕ), ∀(n : ℕ),
       n0 ≤ n → abs (μ n) < 1 / (rat.of_nat (nat.pow n c)) }

------------------------------------------------------------------------
-- random

-- A monad for getting random values.
--
-- Note. This will almost certainly need to be generalized into a
-- monad for probablistic processes.  It will probably need to include
-- some way for defining turing complete operations.  Perhaps we will
-- define a notion of an algebra.
inductive random (α : Type) : Type
| uniform_bitvec : Π(k : ℕ), (bitvec k → random) → random
| pure : α → random

instance : has_pure random :=
{ pure := @random.pure }

-- Return the probability that the computation returns true.
def random.pr (r : random bool) : ℚ :=
  let on_uniform (k : ℕ) (next : bitvec k → random bool) (rec : bitvec k → rat) : rat :=
        algebra.sum (list.map rec (bitvec.all k)) / rat.of_nat (nat.pow 2 k) in
  let on_pure (a : bool) : rat := if a then 1 else 0 in
  @random.rec bool (λx, rat) on_uniform on_pure r

-- This defines a function family over a class K with domain D and range R.
def family (K D R : Type) := K → D → R

def family.keys  {K D R : Type} (f : family K D R) := K
def family.dom   {K D R : Type} (f : family K D R) := D
def family.range {K D R : Type} (f : family K D R) := R

-- This creates a random function
def random.fun (k : ℕ) (D R : Type) (f : family (bitvec k) D R) : random (D → R) :=
  random.uniform_bitvec k (random.pure ∘ f)
