import data.nat
open nat

definition fac : nat → nat
| fac 0     := 1
| fac 1     := 1
| fac (n+2) := fac (n+1) * (n+2)


definition mchoosen (m n : ℕ ) : ℕ := divide (fac m) (fac(m-n) * fac n)

eval mchoosen 5 1 
eval mchoosen 5 2 

-- m choose n = m choose (m-n)
theorem fac_n: ∀ n, mchoosen 10 n = mchoosen 10 (10-n) := calc
	mchoosen 10 n = divide (fac 10) (fac(10-n) * fac n), rfl
	   ... = divide (fac 10) (fac n * fac(10-n)), mul.comm
	   ... = mchoosen 10 (10-n), rfl 





























