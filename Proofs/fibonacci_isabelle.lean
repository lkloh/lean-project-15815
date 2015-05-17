import data.nat
open nat

-- source: the official tutorial for lean

definition fib : nat → nat
| fib 0        := 0
| fib (succ 0) := 1
| fib (succ (succ n)) := fib n + fib (succ n)

eval fib(5)

-- ****************************************************************** --

theorem fib_pos : ∀ n, 0 ≤ fib n,
	fib_pos 0 := show 0 ≤ 0, from le.refl (0), 
	fib_pos (succ 0) := calc
		 0 < succ 0 : zero_lt_succ 0
		 ... = 1 : rfl
	fib_pos (a+2) := calc
		  0 = 0 + 0             : rfl
		... < fib (a+1) + 0     : add_lt_add_right (fib_pos (a+1)) 0
		... < fib (a+1) + fib a : add_lt_add_left  (fib_pos a)     (fib (a+1))
		... = fib (a+2)         : rfl