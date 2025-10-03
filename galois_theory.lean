import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

-- We work with fields K ⊆ L ⊆ M
variable {K L M : Type} [Field K] [Field L] [Field M]
variable [Algebra K L] [Algebra L M] [Algebra K M]
open FiniteDimensional
#check FiniteDimensional.finrank
-- This lemma: degree of tower extensions
lemma degree_mul [FiniteDimensional K L] [FiniteDimensional L M] :
    (FiniteDimensional.finrank K M) =
    (FiniteDimensional.finrank K L) * (FiniteDimensional.finrank L M) := by
  -- hint: use `FiniteDimensional.finrank_mul` from mathlib
  exact FiniteDimensional.finrank_mul K L M
