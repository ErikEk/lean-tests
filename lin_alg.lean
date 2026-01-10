import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Basic

open Nat

example (x y : ℕ) (h : y = x + 7) : 2 * y = 2 * (x+7) := by
  rw [h]
example (P : Prop) : P → P := by
  intro a
  exact a
