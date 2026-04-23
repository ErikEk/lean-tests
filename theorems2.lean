import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Finset.Basic
set_option diagnostics true
open Finset
open BigOperators -- make ∑ and ∏ notation available
#eval Finset.sum (Finset.range 5) (fun i => i)   -- prints 10

structure Account where
  balance : Nat

def withdraw (acc : Account) (amount : Nat) : Account × Bool :=
  if h : amount ≤ acc.balance then
    (⟨acc.balance - amount⟩, true)
  else
    (acc, false)

-- If it returns true, the balance is reduced correctly
theorem withdraw_ok
  (acc : Account) (amount : Nat) (newAcc : Account) :
  withdraw acc amount = (newAcc, true) →
  newAcc.balance = acc.balance - amount :=
by
  intro h
  unfold withdraw at h
  by_cases hle : amount ≤ acc.balance
  · simp [hle] at h
    cases h
    rfl
  · simp [hle] at h

-- If it returns false, balance is unchanged
theorem withdraw_fail
  (acc : Account) (amount : Nat) :
  (withdraw acc amount).snd = false →
  (withdraw acc amount).fst = acc :=
by
  intro h
  unfold withdraw
  by_cases hle : amount ≤ acc.balance
  · simp [withdraw, hle] at h
  · simp [hle]

-- Balance never increases
theorem withdraw_never_increases
  (acc : Account) (amount : Nat) :
  (withdraw acc amount).fst.balance ≤ acc.balance :=
by
  unfold withdraw
  by_cases hle : amount ≤ acc.balance
  · simp [hle]
  · simp [hle]
