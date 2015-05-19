import data.nat
open nat

-- These are taken from http://afp.sourceforge.net/browser_info/current/AFP/Girth_Chromatic/Binomial.html

-- ****************************************************************** --

definition binomial : nat → nat → nat
| binomial 0 0 := 1
| binomial 0 k := 0
| binomial(succ n) 0 := 1
| binomial(succ n) k := binomial n (k-1) + binomial n k

eval binomial 5 2

-- ****************************************************************** --

--  (n choose 0) = 1 

theorem binomial_n_0 : ∀ n, binomial n 0 = 1
| binomial_n_0 0 := show binomial 0 0 = 1, from rfl
| binomial_n_0 (succ n) := show binomial (succ n) 0 = 1, from rfl

-- ****************************************************************** --

-- (0 choose Suc k) = 0

theorem binomial_0_Suc : ∀ k, binomial 0 (succ k) = 0
| binomial_0_Suc 0 := show binomial 0 1 = 0, from rfl
| binomial_0_Suc (succ k) := show binomial 0 (succ k) = 0, from rfl

-- ****************************************************************** --

-- "n choose Suc 0 = n"
theorem binomial_1 : ∀ n, binomial n (succ 0) = n
| binomial_1 0 := show binomial 0 (succ 0) = 0, from rfl
| binomial_1 (succ n) := calc
	binomial (succ n) (succ 0) = binomial n 0 + binomial n (succ 0) : rfl
	... = binomial n 0 + n : {binomial_1 n}
	... = 1 + n : {binomial_n_0 n}
	... = n + 1 : add.comm
	... = succ n : rfl


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

-- "n choose n = 1"
theorem binomial_n_n : ∀ n, binomial n n = 1
| binomial_n_n 0 := show binomial 0 0 = 1, from rfl
| binomial_n_n (succ n) := calc
	binomial (succ n) (succ n) = binomial n n + binomial n (succ n) : rfl
	... = 1 + binomial n (succ n) : {binomial_n_n n}
	... = 1 + 0 : binomial_eq_0 (lt_succ_self n)
	... = 1 : rfl

-- ****************************************************************** --

-- "Suc n choose n = Suc n"

theorem binomial_Suc_n : ∀ n, binomial (succ n) n = succ n
| binomial_Suc_n 0 := show binomial (succ 0) 0 = 1, from rfl 
| binomial_Suc_n (succ n) := calc
	binomial (succ (succ n)) (succ n) = binomial (succ n) n + binomial (succ n) (succ n) : rfl
		... = binomial (succ n) n + 1 : binomial_n_n
		... = (succ n) + 1 : {binomial_Suc_n n} 
		... = succ (succ n) : rfl

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
        		... > 0 : !lt_add_of_pos_right)

-- ****************************************************************** --

