import data.nat
open nat

-- source: the official tutorial for lean

definition fib : nat → nat
| fib 0     := 1
| fib 1     := 1
| fib (a+2) := fib (a+1) + fib a

-- The defining equations hold definitionally

example : fib 0 = 1 :=
rfl

example : fib 1 = 1 :=
rfl

example (a : nat) : fib (a+2) = fib (a+1) + fib a :=
rfl

-- fib is always positive
theorem fib_pos : ∀ n, 0 < fib n
| fib_pos 0     := show 0 < 1, from zero_lt_succ 0
| fib_pos 1     := show 0 < 1, from zero_lt_succ 0
| fib_pos (a+2) := calc
    0 = 0 + 0             : rfl
  ... < fib (a+1) + 0     : add_lt_add_right (fib_pos (a+1)) 0
  ... < fib (a+1) + fib a : add_lt_add_left  (fib_pos a)     (fib (a+1))
  ... = fib (a+2)         : rfl
