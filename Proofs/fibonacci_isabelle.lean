import data.nat
open nat

-- source: the official tutorial for lean

definition fib : nat → nat
| fib 0        := 0
| fib (succ 0) := 1
| fib (succ (succ n)) := fib n + fib (succ n)

eval fib(2)

-- ****************************************************************** --

-- 0 <= fib(n)

theorem fib_pos : ∀ n, 0 ≤ fib n,
	fib_pos 0 := show 0 ≤ 0, from le.refl (0), 
	fib_pos (succ 0) := calc
		 0 ≤ 1 : zero_le_one,
	fib_pos (succ (succ n)) := calc
		0 = 0 + 0             : rfl
		... ≤ fib n + 0     : add_le_add_right (fib_pos n) 0
		... ≤ fib n + fib (succ n) : add_le_add_left  (fib_pos (succ n)) (fib n)
		... = fib (succ (succ n)) : rfl
 

-- ****************************************************************** --

-- "fib (n + k + 1) = fib (k + 1) * fib (n + 1) + fib k * fib n"

theorem fib_add (n k : ℕ) : fib(succ (n + k)) = fib (succ k) * fib (succ n) + fib k * fib n :=
nat.induction_on k
	(calc
		fib(succ (n + 0)) = fib (succ n) : rfl
			... = 1 * fib (succ n) : one_mul
			... = fib (succ 0) * fib (succ n) : rfl
			... = fib (succ 0) * fib (succ n) + 0 : add_zero
			... = fib (succ 0) * fib (succ n) + 0 * fib n : zero_mul
			... = fib (succ 0) * fib (succ n) + fib 0 * fib n : rfl)
	(take k' IH,
		calc 
			fib(succ (n + succ k')) = fib(succ (succ (n + k'))) : add_succ
				... = fib (succ (succ k')) * fib (succ n) + fib (succ k') * fib n : sorry) 

-- ****************************************************************** --

-- "gcd (m::nat) (m + n) = gcd m n"
-- taken from isabelle
theorem gcd_add2_nat (m n: ℕ) : gcd m (m + n) = gcd m n :=
sorry

-- ****************************************************************** --

theorem gcd_succ_fib : ∀ n, gcd (fib n) (fib (succ n)) = 1 := 
sorry

-- ****************************************************************** --

-- gcd (fib n) (fib (n + 1)) = 1
theorem gcd_fib_Suc_eq_1 : ∀ n, gcd (fib n) (fib (n + 1)) = 1,
  	gcd_fib_Suc_eq_1 0 := calc
		gcd (fib 0) (fib(0 + 1)) = gcd 0 (fib(0 + 1)) : rfl
			... = fib(0 + 1) : gcd_zero_left
			... = fib 1 : zero_add
			... = fib (succ 0) : rfl
			... = 1 : rfl,
	gcd_fib_Suc_eq_1 (succ n) := calc
		gcd (fib (succ n)) (fib (succ n + 1)) = gcd (fib (succ n)) (fib (succ (n + 1))) : succ_add
		  	... = gcd (fib (succ n)) ( (fib (succ 1)) * (fib (succ n)) + (fib 1) * (fib n)) : fib_add
		  	... = gcd (fib (succ n)) ( 1 * (fib (succ n)) + (fib 1) * (fib n)) : rfl
		  	... = gcd (fib (succ n)) ( 1 * (fib (succ n)) + 1 * (fib n)) : rfl
		  	... = gcd (fib (succ n)) ( (fib (succ n)) + 1 * (fib n)) : one_mul
		  	... = gcd (fib (succ n)) ( (fib (succ n)) + (fib n) ) : one_mul
		  	... = gcd (fib (succ n)) (fib n) : gcd_add2_nat
		  	... = gcd (fib n) (fib (succ n)) : gcd.comm
		  	... = 1 : gcd_succ_fib


-- ****************************************************************** --



