import data.nat
open nat

definition fac : nat → nat
| fac 0     := 1
| fac 1     := 1
| fac (n+2) := fac (n+1) * (n+2)

check fac 3 = 6

definition mchoosen (m n : ℕ ) : ℕ := divide (fac m) (fac(m-n) * fac n)

check mchoosen 5 1 = 5
check mchoosen 5 2 = 10