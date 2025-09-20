import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Cases
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Group.Basic

set_option diagnostics true
open Nat

example : ∀ x : ℝ, x^2 ≥ 0 := by
  intro x
  exact sq_nonneg x

example (x y : ℕ) : x + y = y + x := by
  exact Nat.add_comm x y

def OnePlusOneIsTwo : Prop := 1 + 1 = 2
theorem oneplusoneistwo : OnePlusOneIsTwo := rfl
theorem onplusoneistwo : 1 + 1 = 2 := by
    decide

theorem andImpliesOr {A B} : A ∧ B → A ∨ B :=
    fun andEvidence =>
        match andEvidence with
        | And.intro a _ => Or.inl a

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

lemma add_zero_own(n : Nat) : n + 0 = n := by
  induction n with
  | zero => rfl
  | succ k ik =>
    simp [Nat.add_zero]

lemma even_plus_even_own (m n : Nat)
  (hm : m % 2 = 0) (hn : n % 2 = 0) :
  (m + n) % 2 = 0 := by
  rw [Nat.add_mod]
  rw [hm, hn]

lemma not_not_own (P : Prop) : ¬¬P → P := by
  intro nnp
  by_contra hP
  apply nnp
  exact hP

lemma or_comm_own (P Q : Prop) : P ∨ Q → Q ∨ P := by
  intro h
  cases h with
  | inl hp  => exact Or.inr hp
  | inr hq => exact Or.inl hq

lemma mul_one_own (n : Nat) : n * 1 = n := by
  induction n with
  | zero =>
    rw[Nat.zero_mul]
  | succ k ik =>
    rw [←ik]
    rw [Nat.mul_one, Nat.mul_one]

lemma succ_add_own (m n : Nat) : Nat.succ m + n = Nat.succ (m + n) := by
  induction n with
  | zero =>
    -- base case: n = 0
    rfl
  | succ n ih =>
    -- inductive step
    rw [Nat.add_succ]
    rw [ih]
    rfl

lemma append_nil_own (l : List Nat) : l ++ [] = l := by
  induction l with
  | nil =>
    rfl
  | cons hd tl ih =>
    simp [List.append]

lemma nil_append_own (l : List Nat) : [] ++ l = l := by
  induction l with
  | nil =>
    rfl
  | cons hd tl ih =>
    simp [List.append]

lemma sum_append (l1 l2 : List Nat) : (l1 ++ l2).sum = l1.sum + l2.sum := by
  induction l1 with
  | nil =>
    -- base case: [] ++ l2 = l2
    -- ([] ++ l2).sum = l2.sum, and [].sum = 0
    -- so goal: l2.sum = 0 + l2.sum
    rw [List.sum_nil]
    rw [Nat.zero_add]
    rw [List.nil_append]
  | cons hd tl ih =>
      -- Goal: ((hd :: tl) ++ l2).sum = (hd :: tl).sum + l2.sum
      change (hd :: (tl ++ l2)).sum = (hd :: tl).sum + l2.sum
      -- Expand sums of cons on both sides
      change hd + (tl ++ l2).sum = (hd + tl.sum) + l2.sum
      -- Use the inductive hypothesis
      rw [ih]
      -- Reassociate
      rw [Nat.add_assoc]

def seq_lim (a : ℕ→ℝ) (L : ℝ) :
  Prop := ∀ ε > 0, ∃ (N : ℕ), ∀ n≥N, |a n - L|<ε

lemma const_converge (a : ℕ → ℝ) (L : ℝ)
  (a_const : ∀ (n : ℕ), a n = L) : seq_lim a L := by
  change ∀ ε>0, ∃ (N : ℕ), ∀ n≥N, |a n - L|<ε
  intro ε a_1
  use 1
  intro n n_b
  specialize a_const n
  rw [a_const]
  norm_num
  apply a_1

lemma map_id (l : List Nat) : l.map id = l := by
  induction l with
  | nil =>
    -- base case: [].map id = []
    rfl
  | cons hd tl ih =>
    -- inductive step: (hd :: tl).map id = hd :: (tl.map id)
    -- by definition of map
    change (id hd :: tl.map id) = (hd :: tl)
    rw [ih]
    rfl

theorem and_comm_own (p q : Prop) : p ∧ q ↔ q ∧ p := by
  constructor
  · intro h
    exact ⟨h.right, h.left⟩
  · intro h
    exact ⟨h.right, h.left⟩

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
example (x : ℕ) : x = x := by
  rfl
example : Nat.succ (Nat.succ 4) = 6 := rfl

example (x : ℕ) : x ≤ x := by
  rw [Nat.le_iff_exists_add]

example (x y : ℕ) : x ≤ y ∨ y ≤ x := by
  induction x generalizing y with
  | zero =>
    -- 0 ≤ y is always true
    left
    apply Nat.zero_le
  | succ x ih =>
    cases y with
    | zero =>
      -- y = 0, so succ x ≥ 1 > 0
      right
      apply Nat.zero_le
    | succ y =>
      -- Reduce to totality for x and y
      cases ih y with
      | inl h =>
        left
        exact Nat.succ_le_succ h
      | inr h =>
        right
        exact Nat.succ_le_succ h

example (x y : ℕ) (h : x = 37 ∧ y = 42) : (y = 42 ∧ x = 37) := by
  cases h with
  | intro hx hy =>
    rw [hx, hy]
    constructor
    · rfl
    · rfl

lemma zero_add_own (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Nat.zero_add, ih]

example (b k : Nat) : b + k = k + b := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_succ]
    rw [ih, Nat.succ_add]
