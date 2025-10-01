import Mathlib.Data.Real.Basic

example {G : Type} [Group G] (g : G) : 1 * g = g := by
  apply one_mul
