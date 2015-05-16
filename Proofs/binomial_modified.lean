import data.nat
open nat

definition binomial : nat → nat → nat 
| binomial 0 0 := 1
| binomial 0 (succ k) := 0
| binomial (succ n) 0 := 1
| binomial (succ n) (succ k) := binomial n k + binomial n (succ k)

-- ****************************************************************** --

-- 0 <= binomial n k 
theorem binomial_geq_0 {n : ℕ} : ∀{k}, binomial n k ≥ 0 := sorry

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

-- "k <= n ==> binomial n k > 0"

theorem zero_less_binomial {n : ℕ} : ∀{k}, k ≤ n → binomial n k > 0 :=
nat.induction_on n
	(take k, assume H : k = 0,
		obtain k' (H' : k = succ k'), from exists_eq_succ_of_lt H,
		calc
			binomial 0 k = binomial 0 (succ k') : H'
				     ... = 1 : rfl
				     ... > 0 : rfl)
	(take n',
		assume IH: ∀{k}, k ≤ n' → binomial n' k > 0,
		take k, assume H : k ≤ succ n',
		obtain k' (H' : k = succ k'), from exists_eq_succ_of_lt H,
			have H1 : succ k' ≤ succ n', from eq.subst H' H,
			have H2 : k' ≤ n', from lt_of_succ_lt_succ H1,
		calc 
			binomial (succ n') k = binomial (succ n') (succ k') : H'
							 ... = binomial n' k' + binomial n' (succ k') : rfl
							 ... > 0 + binomial n' (succ k') : sorry
							 ... > binomial n' (succ k') : zero_add
							 ... > 0 : binomial_geq_0)

