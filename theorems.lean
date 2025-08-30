import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Cases
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Real.Basic
set_option diagnostics true

example : ∀ x : ℝ, x^2 ≥ 0 := by
  intro x
  exact sq_nonneg x

example (x y : ℕ) : x + y = y + x := by
  exact Nat.add_comm x y

def OnePlusOneIsTwo : Prop := 1 + 1 = 2
theorem oneplusoneistwo : OnePlusOneIsTwo := rfl
theorem onplusoneistwo : 1 + 1 = 2 := by
    decide

theorem andImpliesOr {A B} : A ∧ B → A ∨ B :=
    fun andEvidence =>
        match andEvidence with
        | And.intro a b => Or.inl a

theorem onePlusOneAndLessThan : 1 + 1 = 2 ∨ 3 < 5 := by decide

/-
simp -- solves goals if the firn A=B or A ↔ B
norm_num -- sovles goals like 1.5 < 1.7 with numbers
linarith -- solves linear inequalites
library_search -- looks for the exact lemma you need
-/
/-
example (n : ℕ) : (1 : ℝ) ≤ 1.5^n := by
    have h : (1 : ℝ) ≤ 1.5 := by norm_num
    sorry
-/

theorem and_imp_iff (P Q R : Prop) : (P ∧ Q → R) ↔ (P → Q → R) := by
  constructor
  -- First direction: (P ∧ Q → R) → (P → Q → R)
  · intro h
    intro hp hq
    exact h ⟨hp, hq⟩
  -- Second direction: (P → Q → R) → (P ∧ Q → R)
  · intro h
    intro hpq
    cases hpq with
    | intro hp hq => exact h hp hq

/-
example (p q r : Prop) : ((p ∨ q) → r) ↔ ((p → r) ∧ (q → r)) := by
    constructor
    {
      intro h
      constructor
      {
        intro hp
        apply h
        left
        assumption
      }
      {
        intro hq
        apply h
        right
        assumption
      }
    }
    {
      intro h
      cases h with
      |  intro hpr hqr => exact hqr hpr

    }
-/

example (x y : ℕ) : x ≤ y ∨ y ≤ x := by
  induction x generalizing y with
  | zero =>
    -- 0 ≤ y is always true
    left
    apply Nat.zero_le
  | succ x ih =>
    cases y with
    | zero =>
      -- y = 0, so succ x ≥ 1 > 0
      right
      apply Nat.zero_le
    | succ y =>
      -- Reduce to totality for x and y
      cases ih y with
      | inl h =>
        left
        exact Nat.succ_le_succ h
      | inr h =>
        right
        exact Nat.succ_le_succ h

example (x y : ℕ) (h : x = 37 ∧ y = 42) : (y = 42 ∧ x = 37) := by
  cases h with
  | intro hx hy =>
    rw [hx, hy]
    constructor
    · rfl
    · rfl
