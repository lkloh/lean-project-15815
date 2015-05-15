import data.nat
open nat

definition binomial : nat → nat → nat
| binomial 0 0 := 1
| binomial 0 (succ k) := 0
| binomial(succ n) 0 := 1
| binomial(succ n) (succ k) := binomial n k + binomial n (succ k)


-- ****************************************************************** --

-- "n choose n = 1"
theorem binomial_n_n : ∀ n, binomial n n = 1
| binomial_n_n 0 := show binomial 0 0 = 1, from rfl
| binomial_n_n (succ n) := calc
	binomial (succ n) (succ n) = 1 : sorry

-- ****************************************************************** --

-- "Suc n choose n = Suc n"

theorem binomial_Suc_n : ∀ n, binomial (succ n) n = succ n
| binomial_Suc_n 0 := show binomial (succ 0) 0 = 1, from rfl 
| binomial_Suc_n (succ n) := calc
	binomial (succ (succ n)) (succ n) = binomial (succ n) n + binomial (succ n) (succ n) : rfl
		... = binomial (succ n) n + 1 : binomial_n_n
		... = (succ n) + 1 : {binomial_Suc_n n} 
		... = succ (succ n) : rfl
