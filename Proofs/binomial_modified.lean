import data.nat
open nat

definition binomial : nat → nat → nat 
| binomial 0 0 := 1
| binomial 0 (succ k) := 0
| binomial (succ n) 0 := 1
| binomial (succ n) (succ k) := binomial n k + binomial n (succ k)


-- ****************************************************************** --

-- "(Suc n choose Suc k) = (n choose k) + (n choose Suc k)"
theorem binomial_Suc_Suc {n k : ℕ} : binomial (succ n) (succ k) = binomial n k + binomial n (succ k) := 
rfl

-- ****************************************************************** --

-- "n < k ==> n choose k = 0"
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
                have H1 : succ n' < succ k', from eq.subst H' H,
                have H2 : n' < succ k', from lt.trans !lt_succ_self H1,
                have H3 : n' < k', from lt_of_succ_lt_succ H1,
		calc
			binomial (succ n') k = binomial (succ n') (succ k') : H'
			... = binomial n' k' + binomial n' (succ k') : rfl
			... = 0 + binomial n' (succ k') : {IH H3}
			... = binomial n' (succ k') : zero_add
			... = 0 : IH H2)

-- ****************************************************************** --

-- binomial n k >= 0
theorem binomial_geq_0 (n k : ℕ) : binomial n k ≥ 0 := 
	sorry

-- ****************************************************************** --

-- "k <= n ==> binomial n k > 0"

theorem zero_less_binomial {k : ℕ} : ∀{n}, k ≤ n → binomial n k > 0 :=
nat.induction_on k
	(take n, assume H : 0 ≤ n → binomial n 0 > 0,
		obtain n' (H' : n = succ n'), from exists_eq_succ_of_lt H,
		calc
			binomial n 0 = binomial (succ n') 0 : H'
			         ... = 1 : rfl
			         ... > 0 : dec_trivial)
	(take k',
		assume IH : ∀{n}, k' ≤ n → binomial n k' > 0,
		take n, assume H : succ k' ≤ n,
		obtain n' (H' : n = succ n'), from exists_eq_succ_of_lt H,
			have H1 : succ k' ≤ succ n', from eq.subst H' H,
            have H2 : k' ≤ n', from lt_of_succ_lt_succ H1,
        calc
        	binomial n (succ k') = binomial (succ n') (succ k') : H'
        		... = binomial n' k' + binomial n' (succ k') : rfl
        		... > 0 + binomial n' (succ k') : add_lt_add_left (IH H2)
        		... = binomial n' (succ k') : zero_add
        		... ≥ 0 : binomial_geq_0
        		... > 0 : gt_of_gt_of_ge
        )







							 
