import data.nat
open nat

definition binomial : nat → nat → nat
| binomial 0 0 := 1
| binomial 0 (succ k) := 0
| binomial(succ n) 0 := 1
| binomial(succ n) (succ k) := binomial n k + binomial n (succ k)


-- ****************************************************************** --

theorem binomial_eq_0 {n : ℕ} : ∀{k}, n < k → binomial n k = 0 := sorry


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

theorem binomial_n_0 : ∀ n, binomial n 0 = 1
| binomial_n_0 0 := show binomial 0 0 = 1, from rfl
| binomial_n_0 (succ n) := show binomial (succ n) 0 = 1, from rfl

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
theorem binomial_Suc_Suc (n k : ℕ) : binomial (succ n) (succ k) = binomial n k + binomial n (succ k) := rfl





