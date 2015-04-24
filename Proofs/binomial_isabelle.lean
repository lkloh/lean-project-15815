import data.nat
open nat



definition binomial : nat → nat → nat
| binomial 0 0 := 1
| binomial 0 k := 0
| binomial(succ n) 0 := 1
| binomial(succ n) k := binomial n (k-1) + binomial n k

eval binomial 5 2