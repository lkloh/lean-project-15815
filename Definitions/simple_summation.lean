import data.nat
open nat

definition summ : nat → nat
| summ 0     := 0
| summ 1     := 1
| summ(n+1) := summ(n)+(n+1)

eval summ 3

