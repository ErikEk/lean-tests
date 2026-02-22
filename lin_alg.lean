import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Basis.Submodule
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

open Submodule

variable (K : Type*) [Field K]
variable (V : Type*) [AddCommGroup V] [Module K V]
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
example (P Q : Prop) : (P ∧ ¬ P) → Q := by
  unfold Not
  intro a
  cases a with
  | intro hp hnp =>
    exfalso
    exact hnp hp

theorem zero_smul_v (w : V) : (0 : K) • w = (0 : V) := by
  apply add_right_cancel (b := (0:K) •w)
  rw [(add_smul (0:K) (0:K) w).symm]
  rw [zero_add, zero_add]
theorem smul_zero_v (a : K) : a • (0 : V) = (0 : V) := by
  apply add_right_cancel (b := a•(0:V))
  rw[(smul_add a (0:V) (0:V)).symm]
  rw [zero_add, zero_add]
theorem neg_one_smul_v (v : V) : (-1 : K) • v = -v := by
  apply add_right_cancel (b:=v)
  nth_rw 2 [(one_smul K v).symm]
  rw [(add_smul (-1:K) (1:K) v).symm]
  rw [neg_add_cancel, neg_add_cancel]
  exact zero_smul K v
theorem subspace_contains_zero (W : Submodule K V) : (0 : V) ∈ W := by
  have h1 : (0 : V) ∈ W := W.zero_mem
  exact h1

def is_linear_combination (S : Set V) (x : V) : Prop :=
  ∃ (s : Finset V) (f : V→K), (↑s ⊆ S) ∧ (x = Finset.sum s (fun v => f v • v))

--variable {A : Set V}

--#check Submodule.span K A


def VV : Type := ℝ × ℝ × ℝ
def KK : Type := ℝ
variable [Field KK] [AddCommGroup VV] [Module KK VV]

def v1 : VV:= (1,0,0)
def v2 : VV := (0,1,0)

def AA : Set VV := {v1, v2}

#check span KK AA
-- Submodule KK VV

#check (v1 ∈ span KK AA)   -- true
#check ((0,0,1) ∈ span KK AA) -- false

#print AA
example : v1 ∈ span KK AA := by
  apply Submodule.subset_span
  --simp? [AA]
  dsimp [AA]
  change v1 = v1 ∨ v1 = v2
  left
  rfl

#check @Finset.sum
#check @Submodule.span
#check @Submodule.span_le

def linear_independent_v (S : Set V) : Prop :=
  ∀ (s : Finset V) (f : V → K),
  (↑s ⊆ S) → (Finset.sum s (fun v ↦ f v • v) = 0) → (∀ v ∈ s, f v = 0)

theorem linear_independence_empty : linear_independent_v K V (∅ : Set V) := by
  unfold linear_independent_v
  intro s f hs zero_sum v vh
  exfalso
  exact hs vh

#check ℂ
#check (1 : ℂ)
#check (Complex.I : ℂ)
#check star

class InnerProductSpace_v (V : Type) [AddCommGroup V] [Module ℂ V] where
  inner : V → V → ℂ
  inner_self_im_zero : ∀ (v : V), (inner v v).im = 0
  inner_self_nonneg : ∀ (v : V), 0 ≤ (inner v v).re
  inner_self_eq_zero : ∀ (v : V), inner v v = 0 ↔ v = 0
  inner_add_left : ∀ (u v w : V), inner (u + v) w = inner u w + inner v w
  inner_smul_left : ∀ (a : ℂ) (v w : V), inner (a • v) w = a * inner v w
  inner_conj_symm :
    ∀ v w : V,
      inner v w = star (inner w v) -- Complex.conj was changed to star
