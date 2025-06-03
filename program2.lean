import Mathlib

/-open Real-/

open Nat
#check 2

def myFavNum : ℕ := 7

example (a b : ℕ) : a + b = b + a := Nat.add_comm a b
example (a b : ℕ) : a * b = b * a := Nat.mul_comm a b

theorem add_zero_2 (n : ℕ) : n + 0 = n :=
  Nat.add_zero n


#check add_zero_2
example (x : ℕ) := add_zero_2 x
