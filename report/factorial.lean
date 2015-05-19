import data.nat
open nat

definition fac : nat → nat
| fac 0     := 1
| fac 1     := 1
| fac (n+2) := fac (n+1) * (n+2)

-- ****************************************************************** --

definition mchoosen (m n : ℕ ) : ℕ := divide (fac m) (fac(m-n) * fac n)

-- ****************************************************************** --

eval mchoosen 5 1 
eval mchoosen 5 2 


-- ****************************************************************** --

example : fac 0 = 1 :=
rfl 

example : fac 1 = 1 :=
rfl

-- fac is always positive
theorem fac_pos : ∀ n, 0 < fac n
| fac_pos 0 := show 0 < 1, from zero_lt_succ 0
| fac_pos 1 := show 0 < 1, from zero_lt_succ 0
| fac_pos (n+2) := 
    have H1 : 0 < n + 2, from !succ_pos,
    calc
      0 < fac (n+1) * (n+2) : mul_pos (fac_pos (n + 1)) H1
        ... = fac (n+2)     : rfl

-- ****************************************************************** --
