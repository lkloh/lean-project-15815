import data.nat
open nat

definition binomial : nat → nat → nat 
| binomial 0 0 := 1
| binomial 0 (succ k) := 0
| binomial (succ n) 0 := 1
| binomial (succ n) (succ k) := binomial n k + binomial n (succ k)




