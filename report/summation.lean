
import data.nat
open nat

-- ****************************************************************** --

definition summ : nat → nat
| summ 0    := 0
| summ(n+1) := summ(n) + (n+1)

eval summ 3

-- ****************************************************************** --

theorem two : 1+1 = 2 := rfl


theorem summ_form : ∀ n, 2 * summ n = n*(n+1)
| summ_form 0 :=  calc 
        2 * 0 = 0 : mul_zero
        ... = 0 * (0 + 1) : zero_mul
| summ_form (n+1) := calc
    2*summ (n+1) = 2*(summ(n)+(n+1)) : rfl
     ... = 2*summ(n) + 2*(n+1) : mul.left_distrib
     ... = n*(n+1) + 2*(n+1)   : {summ_form n}
     ... = (n+2)*(n+1) : mul.right_distrib
     ... = (n+1)*(n+2) : mul.comm 
     ... = (n+1)*(n+(1+1)) : two
     ... = (n+1)*(n+1+1) : add.assoc

-- ****************************************************************** --












