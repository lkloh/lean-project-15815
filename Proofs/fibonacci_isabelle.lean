import data.nat
open nat

-- source: the official tutorial for lean

definition fib : nat → nat
| fib 0        := 0
| fib (succ 0) := 1
| fib (succ (succ n)) := fib n + fib (succ n)

-- ****************************************************************** --

--  "fib (Suc n) > 0"
theorem fib_simp: ∀ n, fib (succ n) > 0
| fib_simp(0) := show fib (succ 0) > 0, from rfl
| fib_simp(succ (succ n)) := 
	calc
		fib (succ (succ n)) = fib n + fib (succ n) : rfl
		    	...         > 0 + fib (succ n)     : {fib_simp n}
	