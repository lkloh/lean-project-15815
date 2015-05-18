import data.nat
open nat
-- source: the official tutorial for lean

definition fib : nat → nat
| fib 0     := 1
| fib 1     := 1
| fib (n+2) := fib (n+1) + fib n

definition sumF : nat → nat
| sumF 0    := 1
| sumF(n+1) := sumF(n) + fib(n+1)

eval sumF(2)


-- ****************************************************************** --

theorem fibminus: ∀ n, sumF(n)+1 = fib(n+2)
| fibminus(0) := show 2 = 2, from rfl
| fibminus(n+1) := calc
    sumF(n+1)+1 = (sumF(n) + fib(n+1)) + 1 : rfl
    ... = sumF(n) + (fib(n+1)+1)   : add.assoc
    ... = sumF(n) + (1+fib(n+1))   : add.comm
    ... = (sumF(n)+1) + fib(n+1)   : add.assoc
    ... = fib(n+2) + fib(n+1)      : {fibminus n}
    ... = fib(n+3)                 : rfl 

-- ****************************************************************** --

theorem fib_pos : ∀ n, 0 < fib n,
	fib_pos 0 := show 0 < 1, from zero_lt_succ 0, 
	fib_pos 1 := show 0 < 1, from zero_lt_succ 0, 
	fib_pos (a+2) := calc
		  0 = 0 + 0             : rfl
		... < fib (a+1) + 0     : add_lt_add_right (fib_pos (a+1)) 0
		... < fib (a+1) + fib a : add_lt_add_left  (fib_pos a)     (fib (a+1))
		... = fib (a+2)         : rfl


-- ****************************************************************** --

















