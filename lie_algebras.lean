import Mathlib.Algebra.Lie.Basic
import Mathlib.Tactic

variable (L M : Type) [LieRing L] [LieRing M]
example : ∀ (x y z : L), ⁅x + y, z⁆ = ⁅x, z⁆ + ⁅y, z⁆ := by
  apply add_lie
example : ∀ (x : L), ⁅x, x⁆ = 0 := by
  apply lie_self
example : ∀ (x y m : L), ⁅x, ⁅y, m⁆⁆ = ⁅⁅x, y⁆, m⁆ + ⁅y, ⁅x, m⁆⁆ := by
  apply leibniz_lie
