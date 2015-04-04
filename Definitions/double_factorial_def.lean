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
| efac (n+1) := efac(n) * (2*(n+1))

eval efac 0
eval efac 1
eval efac 2
eval efac 3






-- odd factorial
-- #0 -> 1, 1!! = 1
-- #1 -> 3, 3!! = 3
-- #2 -> 5, 5!! = 15
-- #3 -> 7, 7!! = 105
definition ofac : nat → nat
| ofac 0 := 1
| ofac 1 := 3
| ofac (n+1) := ofac(n) * (2*(n+1)+1)

eval ofac 0
eval ofac 3

