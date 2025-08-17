import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-- Definition of a continuous function
`f : D→ ℝ at a point `a ∈ D`. -/
def IsContinuousAt (D : Set ℝ) (f : D → ℝ) (a : D) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : D,
  (|x.val - a.val| < δ → |f x - f a| < ε)

def IsContinuous (D: Set ℝ) (f : D → ℝ) : Prop :=
  ∀ a : D, IsContinuousAt D f a

theorem constant_function_is_continuous_at_a_point
  (D : Set ℝ) (c : ℝ) (a : D) : IsContinuousAt D (fun _ =>  c) a := by
  dsimp [IsContinuousAt]
  intro ε hεbigger0
  exists 1
  apply And.intro
  { exact one_pos }
  --simp only [one_pos, true_and]
  intro x _h_xδ_criterion
  rw [sub_self]
  rw [abs_zero]
  --simp only [sub_self, abs_zero]
  exact hεbigger0

theorem linear_function_is_continuous_at_a_point
  (D : Set ℝ) (m y0 : ℝ) (a : D) : IsContinuousAt D (fun x =>  m*x+y0) a := by
  by_cases m_cases : m = 0
  subst m
  simp only [zero_mul, zero_add]
  exact constant_function_is_continuous_at_a_point D y0 a
  dsimp [IsContinuousAt]
  intro ε hεbigger0
  let δ := ε / |m|
  use δ
  have h_δbigger0 : δ > 0 := by positivity
  --assumption
  --apply And.intro
  simp only [h_δbigger0, true_and]
  intro x h_xδ_criterion
  simp
  let x' := x.val; let a' := a.val
  calc |m * x' - m * a'|
    _ = |m*(x'-a')|
      := by ring_nf
    _ = |m| * |x' - a'|
      := abs_mul m (x' - a')
    _ < |m| * δ
      :=  (mul_lt_mul_left (by positivity)).mpr h_xδ_criterion
    _ = |m| * (ε/|m|)
      := rfl
    _ = ε
      := by field_simp

theorem parabola_function_is_continuious_at_a_point
  (D : Set ℝ) (a : D) : IsContinuousAt D (λ x => x^2) a := by
  let a' := a.val
  dsimp [IsContinuousAt]
  intro ε hεbigger0
  let δ := ε / (2 * |a'| + 1) ⊓ 1
