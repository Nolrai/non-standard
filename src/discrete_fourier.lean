import data.array.lemmas
import algebra.ring
import data.polynomial.basic
import data.pnat.basic

universe u

section 

open array

def array.sum {g : Type u} [add_monoid g] {n} (a : array n g) : g := 
  a.foldl (0 : g) ((+) : g → g → g)

parameters (a : Type u)
parameters [ring a]
parameters (n : nat) (one_le_n : 1 ≤ n) 
parameters (α : a) (root_of_unity : α ^ n = 1) 
parameters (principle : ∀ k, 1 ≤ k → k < n → array.sum ⟨λ j : fin n, α ^ (j.val * k)⟩ = 0)

def naive_discrete_fourier_transform (v : array n a) : array n a := 



end