import data.nat
open nat

-- source: the official tutorial for lean

definition fib : nat → nat
| fib 0     := 1
| fib 1     := 1
| fib (a+2) := fib (a+1) + fib a

-- ****************************************************************** --



