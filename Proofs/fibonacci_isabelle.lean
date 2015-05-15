import data.nat
open nat

-- source: the official tutorial for lean

definition fib : nat → nat
| fib 0     := 1
| fib 1     := 1
| fib (a+2) := fib (a+1) + fib a

-- ****************************************************************** --

-- "fib (n + k + 1) = fib (k + 1) * fib (n + 1) + fib k * fib n"

theorem fib_add (n k : ℕ) : fib(n + k + 1) = fib(k+1)*fib(n+1) + fib(k)*fib(n) :=
	nat.induction_on k
		(calc
			fib(n+0+1) = fib(0+1)*fib(n+1) + fib(0)*fib(n) : rfl
			... = fib(n+1) + fib(0)*fib(n) : rfl
			... = 1*fib(n+1) + fib(0)*fib(n) : rfl 
		)
		(take m IH, calc 
			fib(n + (succ m) + 1) = fib((succ m)+1) 


(take (H : 0 + m = 0), rfl)
  (take k IH,
    assume H : succ k + m = 0,
    absurd
      (show succ (k + m) = 0, from calc
         succ (k + m) = succ k + m : succ_add
                  ... = 0          : H)
      !succ_ne_zero)