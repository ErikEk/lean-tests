import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

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
