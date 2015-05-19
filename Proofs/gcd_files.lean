import data.nat
open nat

-- "(0::nat) < n ==> gcd (n * k + m) n = gcd m n"

theorem gcd_mult_add (n k m: ℕ} : gcd (n * k + m) n = gcd m n :=
nat.induction_on n



