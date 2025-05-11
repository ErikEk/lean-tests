import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Cases

def OnePlusOneIsTwo : Prop := 1 + 1 = 2
theorem oneplusoneistwo : OnePlusOneIsTwo := rfl
theorem onplusoneistwo : 1 + 1 = 2 := by
    decide

theorem andImpliesOr : A ∧ B → A ∨ B :=
    fun andEvidence =>
        match andEvidence with
        | And.intro a b => Or.inl a

/-
-/
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
