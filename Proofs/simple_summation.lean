
import data.nat
open nat

definition summ : nat → nat
| summ 0    := 0
| summ 1    := 1
| summ(n+1) := summ n + (n+1)

eval summ 3

theorem summ_form : ∀ n, summ n = divide (n*(n+1)) 2
| summ_form 0 := show 0 = divide (0*(0+1)) 2, from rfl
| summ_form 1 := show 1 = divide (1*(1+1)) 2, from rfl
| summ_form (n+1) := calc
    summ n + (n+1) = n*(n+1) div 2 + (n+1) : rfl
         ...       = (n+1)*(n+2) div 2 : rfl

