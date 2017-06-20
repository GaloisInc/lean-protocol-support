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

universe variables u v

def algebra.sum {α : Type u} [has_zero α] [has_add α] : list α → α
| [] := 0
| (x::l) := x + algebra.sum l

------------------------------------------------------------------------
-- negligible function

-- A univariate polynomial
inductive poly (α : Type)
| cns : α → poly
| var : poly
| add : poly → poly → poly
| mul : poly → poly → poly


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
