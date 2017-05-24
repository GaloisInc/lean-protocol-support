namespace nat

def gcd.f (n:ℕ) (rec : Π(m:ℕ), m < n → ℕ → ℕ) (m : ℕ) : ℕ :=
  if n_pos : n > 0 then
    rec (m % n) (nat.mod_lt m n_pos) n
  else
    m

-- Return the greatest common divisor of two natural numbers
def gcd (x : ℕ) : ℕ → ℕ := nat.strong_rec_on x gcd.f

end nat
