import data.nat
open nat

definition fac : nat → nat
| fac 0     := 1
| fac 1     := 1
| fac (n+2) := fac (n+1) * (n+2)

check fac 3 = 6