import Mathlib

open Nat
#check 2

def myFavNum : ℕ := 7

example (a b : ℕ) : a + b = b + a := Nat.add_comm a b
example (a b : ℕ) : a * b = b * a := Nat.mul_comm a b

theorem add_zero_2 (n : ℕ) : n + 0 = n :=
  Nat.add_zero n

#check add_zero_2
example (x : ℕ) := add_zero_2 x


theorem pythagoras {a b : E} (h : ⟪a, b⟫ = 0) :
    ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  calc
    ‖a + b‖ ^ 2 = ⟪a + b, a + b⟫ := norm_sq_eq_inner _
             _ = ⟪a, a⟫ + ⟪b, b⟫ + ⟪a, b⟫ + ⟪b, a⟫ := by
                  rw [inner_add_add_self]
             _ = ‖a‖ ^ 2 + ‖b‖ ^ 2 + 0 + 0 := by
                  rw [← norm_sq_eq_inner a, ← norm_sq_eq_inner b, h, inner_symm, h]
             _ = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by ring
