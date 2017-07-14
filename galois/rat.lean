import library_dev.data.rat
import galois.nat.div_lemmas

namespace rat

def of_nat.f (n : ℕ) (rec : Π(m:ℕ), m < n → ℚ) : ℚ :=
  if pr : n > 0 then
    let pr2 : 1 < 2 := (by simp [nat.succ_lt_succ_iff, nat.zero_lt_succ_iff_true]) in
    if n = 1 then
      1
    else if (n % 2) = 0 then
      bit0 (rec (n / 2) (nat.div_lt_self pr pr2))
    else
      bit1 (rec (n / 2) (nat.div_lt_self pr pr2))
  else
    0

def of_nat (n : ℕ) : ℚ := @nat.strong_rec_on (λx, ℚ) n @of_nat.f

end rat
