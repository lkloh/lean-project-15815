import data.nat
open nat

definition fac : nat → nat
| fac 0     := 1
| fac 1     := 1
| fac (n+2) := fac (n+1) * (n+2)

eval fac 3 

definition mchoosen (m n : ℕ ) : ℕ := divide (fac m) (fac(m-n) * fac n)

eval mchoosen 5 1 
eval mchoosen 5 2 