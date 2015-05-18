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









