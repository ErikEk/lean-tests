import Mathlib

open Real

#check 2

def myFavNum : ℕ := 7

example (a b : ℕ) : a + b = b + a := Nat.add_comm a b
example (a b : ℕ) : a * b = b * a := Nat.mul_comm a b
