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

theorem fibminus: ∀ n, sumF(n)+1 = fib(n+2)
| fibminus(0) := show 2 = 2, from rfl
| fibminus(n+1) := calc
    sumF(n+1)+1 = (sumF(n) + fib(n+1)) + 1 : rfl
    ... = sumF(n) + (fib(n+1)+1)   : add.assoc
    ... = sumF(n) + (1+fib(n+1))   : add.comm
    ... = (sumF(n)+1) + fib(n+1)   : add.assoc
    ... = fib(n+2) + fib(n+1)      : {fibminus n}
    ... = fib(n+3)                 : rfl 