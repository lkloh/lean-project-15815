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

-- "(Suc n choose Suc k) = (n choose k) + (n choose Suc k)"
-- Needs help

-- ****************************************************************** --

-- n < k ==> n choose k = 0
theorem binomial_eq_0: {n k : ℕ} (H : n < k) : (binomial n k = 0) :=
nat.induction_on n
	(calc binomial 0 k = 0 : rfl)
	(take n,
		assume IH : binomial n k = 0,
		calc
			binomial (succ n) k = binomial n (k-1) + binomial n k : rfl
			... = binomial n (k-1) + 0 : IH
			... = binomial
	)


-- ****************************************************************** --

-- n choose n = 1
theorem binomial_n_n : ∀ n, binomial n n = 1
| binomial_n_n 0 := show binomial 0 0 = 1, from rfl
| binomial_n_n (succ n) := calc
	binomial (succ n) (succ n) = binomial n n + binomial n (succ n) : rfl
	...  = 1 + binomial n (succ n) : {binomial_n_n }
	...  = 




























