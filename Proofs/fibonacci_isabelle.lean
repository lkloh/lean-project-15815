import data.nat
open nat

-- source: the official tutorial for lean

definition fib : nat → nat
| fib 0        := 0
| fib (succ 0) := 1
| fib (succ (succ n)) := fib n + fib (succ n)

eval fib(5)

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
			fib(succ(n + (succ k') + 1)) = fib(succ (succ (n + k') + 1)) : add_succ
				... = fib(succ (succ (succ (n + k')))) : add_one
				... = fib (succ (n + k')) + fib (succ (succ (n + k'))) : rfl
				... = 
				... = fib (succ k' + 1) * fib (n + 1) + fib (succ k') * fib n : sorry)







