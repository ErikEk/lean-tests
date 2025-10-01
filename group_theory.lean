import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.Basic

example {G : Type} [Group G] (g : G) : 1 * g = g := by
  apply one_mul
example {G : Type} [Group G] (a b c : G) :
    (a * b) * c = a * (b * c) := by
    apply mul_assoc
