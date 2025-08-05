import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-- Definition of a continuous function
`f : D→ ℝ at a point `a ∈ D`. -/
def IsContinuousAt
  (D : Set ℝ) (f : D → ℝ) (a : D) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : D,
  (|x.val - a.val| < δ → |f x - f a| < ε)

def IsContinuous (D: Set ℝ) (f : D → ℝ) : Prop :=
  ∀ a : D, IsContinuousAt D f a

theorem constant_function_is_continuious_at_a_point
  (D : Set ℝ) (c : ℝ) (a : D) : IsContinuousAt D (fun _ =>  c) a := by
  dsimp [IsContinuousAt]
  intro ε hεbigger0
  exists 1
  --apply And.intro
  --{ exact one_pos }
  simp only [one_pos, true_and]
  intro x _h_xδ_criterion
  simp only [sub_self, abs_zero]
  exact hεbigger0
