import data.nat
open nat

-- even factorial
-- #0 -> 0, 0!! = 1
-- #1 -> 2, 2!! = 2
-- #2 -> 4, 4!! = 8
-- #3 -> 6, 6!! = 48
-- ...
definition efac : nat → nat
| efac 0 := 1
| efac 1 := 2
| efac (n+2) := efac(n+1) * (2*(n+2))

eval efac 0
eval efac 1
eval efac 2
eval efac 3

example : efac 0 = 1 :=
rfl 

example : efac 1 = 2 :=
rfl

-- fac is always positive
theorem efac_pos : ∀ n, 0 < efac n
| efac_pos 0 := show 0 < 1, from zero_lt_succ 0
| efac_pos 1 := show 0 < 2, from zero_lt_succ 1
| efac_pos (n+2) := 
    have H1 : 0 < 2*(n+2), from !succ_pos,
    calc
      0 < efac(n+1) * (2*(n+2)) : mul_pos (efac_pos(n+1)) H1
        ... = efac(n+2)       : rfl
