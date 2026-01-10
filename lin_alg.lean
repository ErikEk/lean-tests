import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Basic

open Nat

example (x y : ℕ) (h : y = x + 7) : 2 * y = 2 * (x+7) := by
  rw [h]
example (P : Prop) : P → P := by
  intro a
  exact a
example (P Q : Prop) (p: P) (q : Q) : P∧Q := by
  constructor
  exact p
  exact q
example (P Q : Prop) : (P → Q) → ¬Q → ¬P := by
  unfold Not
  intro a b h3
  apply b
  apply a
  exact h3
