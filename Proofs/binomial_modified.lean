import data.nat
open nat

definition binomial : nat → nat → nat 
| binomial 0 0 := 1
| binomial 0 (succ k) := 0
| binomial (succ n) 0 := 1
| binomial (succ n) (succ k) := binomial n k + binomial n (succ k)


-- ****************************************************************** --

theorem binomial_eq_0 {n : ℕ} : ∀{k}, n < k → binomial n k = 0 := 
nat.induction_on n
	(take k, assume H : k > 0,
		obtain k' (H' : k = succ k'), from exists_eq_succ_of_lt H, 
		calc
			binomial 0 k = binomial 0 (succ k') : H' 
					 ... = 0 : rfl)
	(take n',
		assume IH : ∀{k}, n' < k → binomial n' k = 0,
		take k, assume H : succ n' < k,
		obtain k' (H' : k = succ k'), from exists_eq_succ_of_lt H, 
		calc
			binomial (succ n') k = binomial (succ n') (succ k') : H' 
			... = binomial n' k' + binomial n' (succ k') : rfl
			... = 0 + binomial n' (succ k') : {lt_of_succ_lt_succ H}
			... = binomial n' (succ k') : zero_add
			... = 0 : IH(lt_of_succ_le H) )

-- ****************************************************************** --















