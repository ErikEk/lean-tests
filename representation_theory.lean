import Mathlib.Algebra.Group.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

-- Let G be a group and V a K-vector space
variable (G : Type) [Group G]
variable (K V : Type) [Field K] [AddCommGroup V] [Module K V]

-- A representation is a group homomorphism G → GL(V)
structure Representation where
  (ρ : G → V →ₗ[K] V)  -- linear map for each group element
  (map_one : ρ 1 = LinearMap.id)
  (map_mul : ∀ g h : G, ρ (g * h) = (ρ g).comp (ρ h))
